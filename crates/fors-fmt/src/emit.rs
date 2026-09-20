//! CST -> layout ops. One pre-order walk, no per-node allocation.
//!
//! The walk is driven by the lossless tree's central invariant: every raw
//! token belongs to exactly one node (the innermost whose range contains
//! it), children are contiguous and in order, and leading trivia belongs
//! to the token that follows it. So a node handler only has to interleave
//! "the tokens I own" with "my children", and two safety nets make it
//! impossible to lose a token even where a handler is wrong about a
//! production's shape: `child()` first flushes any owned token the handler
//! skipped, and `finish()` flushes whatever is left of the node's range.

use fors_lex::{TokenKind as T, Tokens};
use fors_syntax::{NodeKind as K, Tree};

use crate::doc::{FORCE, Op};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Sep {
    None,
    Space,
    Line,
    Soft,
    Hard,
}

/// The direct children of one node, as a copyable cursor. `fors-syntax`
/// keeps its own `ChildIter` private, and a peekable one cannot be named
/// in a signature anyway; this is the same two-field walk over
/// `subtree_end`, with no allocation.
#[derive(Clone, Copy)]
struct Kids<'a> {
    tree: &'a Tree,
    next: usize,
    end: usize,
}

impl<'a> Kids<'a> {
    fn new(tree: &'a Tree, n: usize) -> Self {
        Kids { tree, next: n + 1, end: tree.subtree_end(n) }
    }
    fn peek(&self) -> Option<usize> {
        if self.next < self.end { Some(self.next) } else { None }
    }
    fn bump(&mut self) {
        if self.next < self.end {
            self.next = self.tree.subtree_end(self.next);
        }
    }
}

pub struct Emitter<'a> {
    src: &'a [u8],
    toks: &'a Tokens,
    tree: &'a Tree,
    pub ops: Vec<Op>,
    cursor: usize,
    /// The last significant token emitted, for the default separator.
    prev: Option<T>,
    /// A separator a handler asked for, consumed by the next token.
    sep: Option<Sep>,
    /// Whether a blank line in the source may be preserved here.
    blank_ok: bool,
    /// Inside a method chain that is being broken one call per line.
    in_chain: bool,
    /// The chain's indent is owed but not yet pushed (it must land after
    /// the head, never before the line's first token).
    chain_indent: bool,
}

/// Tokens that end a value, so `(`, `[`, `.` and `..<` bind tightly to them.
fn value_end(k: T) -> bool {
    matches!(
        k,
        T::Ident
            | T::Int
            | T::Float
            | T::Str
            | T::MultilineStr
            | T::RParen
            | T::RBracket
            | T::RBrace
            | T::Question
            | T::Underscore
            | T::KwTrue
            | T::KwFalse
    )
}

/// The house spacing rule between two adjacent tokens, used wherever a
/// handler does not ask for something else. It is a pure function of the
/// two kinds, so spacing is uniform across every production.
fn default_sep(prev: T, next: T) -> Sep {
    match next {
        T::RParen | T::RBracket | T::Comma | T::Semi | T::Colon | T::Question => Sep::None,
        T::RBrace => {
            if prev == T::LBrace {
                Sep::None // `{}`, never `{ }`
            } else {
                Sep::Space
            }
        }
        T::Dot | T::DotDotLt | T::DotDotEq => {
            if value_end(prev) || matches!(prev, T::Dot | T::DotDotLt | T::DotDotEq) {
                Sep::None
            } else {
                Sep::Space // a leading dot-literal: `contracts: .strict`
            }
        }
        T::LParen | T::LBracket => {
            if value_end(prev) || matches!(prev, T::KwFn | T::KwImpl | T::KwAsm | T::KwIn) {
                Sep::None
            } else {
                Sep::Space
            }
        }
        _ => match prev {
            T::LParen | T::LBracket | T::At | T::Amp | T::Dot | T::DotDotLt | T::DotDotEq => Sep::None,
            _ => Sep::Space,
        },
    }
}

impl<'a> Emitter<'a> {
    pub fn new(src: &'a [u8], toks: &'a Tokens, tree: &'a Tree) -> Self {
        Emitter {
            src,
            toks,
            tree,
            ops: Vec::with_capacity(toks.len() * 2),
            cursor: 0,
            prev: None,
            sep: None,
            blank_ok: false,
            in_chain: false,
            chain_indent: false,
        }
    }

    pub fn run(&mut self) {
        if !self.tree.is_empty() {
            self.node(0);
        }
    }

    // ---- primitives ----

    fn push(&mut self, op: Op) {
        self.ops.push(op);
    }

    fn set(&mut self, s: Sep) {
        self.sep = Some(s);
    }

    /// Opens a group after flushing whatever came before it. A pending
    /// separator or a leading comment must land OUTSIDE the group: inside,
    /// a statement separator's newline would make every group unfittable.
    fn group_open(&mut self) {
        self.trivia();
        if let Some(s) = self.sep.take() {
            if self.prev.is_some() {
                self.emit_sep(s);
            }
        }
        self.push(Op::Open);
    }

    fn emit_sep(&mut self, s: Sep) {
        match s {
            Sep::None => {}
            Sep::Space => self.push(Op::Space),
            Sep::Line => self.push(Op::Line),
            Sep::Soft => self.push(Op::Soft),
            Sep::Hard => self.push(Op::Hard),
        }
    }

    /// Index of the next significant token (trivia skipped).
    fn sig_idx(&self) -> usize {
        let mut i = self.cursor;
        while i < self.toks.len() && self.toks.kinds[i].is_trivia() {
            i += 1;
        }
        i
    }

    /// The next significant kind, or `None` when a comment comes first:
    /// callers use it to decide "is this pair empty", and a comment inside
    /// it is content that must keep the pair open.
    fn peek_no_comment(&self) -> Option<T> {
        let mut i = self.cursor;
        while i < self.toks.len() {
            match self.toks.kinds[i] {
                T::Whitespace => i += 1,
                T::LineComment | T::BlockComment => return None,
                k => return Some(k),
            }
        }
        None
    }

    fn newlines_in(&self, i: usize) -> usize {
        let (a, b) = self.toks.range(i);
        self.src[a as usize..b as usize].iter().filter(|&&c| c == b'\n').count()
    }

    /// Emits the comments between the cursor and the next significant
    /// token, leaving the cursor on that token. Every comment in the file
    /// passes through here exactly once, because trivia is leading and each
    /// token is emitted exactly once.
    fn trivia(&mut self) {
        let mut nl = 0usize;
        while self.cursor < self.toks.len() {
            let k = self.toks.kinds[self.cursor];
            match k {
                T::Whitespace => {
                    nl += self.newlines_in(self.cursor);
                    self.cursor += 1;
                }
                T::LineComment | T::BlockComment => {
                    let (a, b) = self.toks.range(self.cursor);
                    if nl == 0 && self.prev.is_some() {
                        self.trailing_comment(a, b, k);
                    } else {
                        if nl >= 2 && self.blank_ok {
                            self.push(Op::Blank);
                        } else {
                            self.push(Op::Hard);
                        }
                        self.push(Op::Src(a, b));
                        self.push(Op::Hard);
                        self.sep = None;
                    }
                    self.cursor += 1;
                    nl = 0;
                    // The "no blank line here" rule (start of file, just
                    // after `{`) applies to the gap BEFORE the first thing
                    // at this position. Gaps between comments, and between
                    // the last comment and the code, are the author's.
                    self.blank_ok = true;
                }
                _ => break,
            }
        }
        if nl >= 2 && self.blank_ok {
            self.push(Op::Blank);
        }
    }

    /// A comment on the same line as the token before it stays on that
    /// line: it is spliced in directly after the last token's text, in
    /// front of whatever layout ops the enclosing handler already queued
    /// (the statement separator, a dedent, a group boundary).
    ///
    /// MARC: a BLOCK comment crosses every non-text op, including a
    /// `Close`, so `raises E /*c*/` keeps `/*c*/` on E's line even when the
    /// signature's tail group then breaks. A LINE comment carries a `Hard`
    /// and must not be moved inside a group that has already closed: a
    /// `Hard` inside a group makes it unfittable, and `f(a, b) // c` would
    /// explode into one argument per line. It stops at `Close` instead,
    /// and the renderer's "a comment at the start of a line owns the line"
    /// rule keeps the result idempotent when that break does fire.
    ///
    /// The splice is a rotate in place, not a `split_off`: no allocation
    /// per comment.
    fn trailing_comment(&mut self, a: u32, b: u32, k: T) {
        let block = k == T::BlockComment;
        let mut cut = self.ops.len();
        while cut > 0
            && match self.ops[cut - 1] {
                Op::Src(..) => false,
                Op::Close => block,
                _ => true,
            }
        {
            cut -= 1;
        }
        let before = self.ops.len();
        self.push(Op::Space);
        self.push(Op::Src(a, b));
        // a block comment is spaced on both sides (`x /*c*/ :`), a line
        // comment ends the line
        self.push(if block { Op::Space } else { Op::Hard });
        let pushed = self.ops.len() - before;
        self.ops[cut..].rotate_right(pushed);
    }

    /// Emits the next significant token with its leading comments.
    fn tok(&mut self) -> Option<T> {
        self.trivia();
        if self.cursor >= self.toks.len() {
            return None;
        }
        let k = self.toks.kinds[self.cursor];
        let (a, b) = self.toks.range(self.cursor);
        let s = self.sep.take().unwrap_or(match self.prev {
            Some(p) => default_sep(p, k),
            None => Sep::None,
        });
        if self.prev.is_some() {
            self.emit_sep(s);
        }
        self.push(Op::Src(a, b));
        // MARC: a `\\` multiline string swallows every following line that
        // starts with `\\` after whitespace alone, so ANY token printed on
        // its line would be read back as string content. The break after it
        // is a correctness rule, not a style choice (`;` lands on its own
        // line under it).
        if k == T::MultilineStr {
            self.push(Op::Hard);
        }
        self.cursor += 1;
        self.prev = Some(k);
        self.blank_ok = false;
        Some(k)
    }

    /// Emits owned tokens up to (not including) raw token `limit`.
    fn tokens_until(&mut self, limit: usize) {
        loop {
            let mut i = self.cursor;
            while i < limit && self.toks.kinds[i].is_trivia() {
                i += 1;
            }
            if i >= limit {
                break;
            }
            if self.tok().is_none() {
                break;
            }
        }
    }

    /// Emits whatever is left of node `n`'s token range.
    fn finish(&mut self, n: usize) {
        let end = self.tree.token_range(n).1 as usize;
        self.tokens_until(end);
    }

    fn child(&mut self, c: usize) {
        self.tokens_until(self.tree.first_token[c] as usize);
        self.node(c);
        let end = self.tree.token_range(c).1 as usize;
        if self.cursor < end {
            self.cursor = end;
        }
    }

    // ---- dispatch ----

    fn node(&mut self, n: usize) {
        match self.tree.kinds[n] {
            K::File => self.file(n),
            K::Block | K::MatchExpr | K::TraitDecl | K::ImplDecl => self.shaped(n, true),
            K::FnDecl | K::TraitItem | K::ExternFnDecl => self.fn_like(n),
            K::FnSig => self.fn_sig(n, false),
            K::UseDecl => self.wrapped(n),
            K::ScopedType => self.plain(n),
            K::Arm => self.arm(n),
            K::Closure => self.pipes(n),
            K::Handler => self.handler(n),
            K::OrExpr | K::AndExpr | K::CmpExpr | K::BitExpr | K::AddExpr | K::MulExpr | K::CastExpr => {
                self.binary(n)
            }
            K::UnaryExpr | K::PatLit => self.tight_prefix(n),
            K::FieldExpr => self.chain_entry(n),
            K::CallExpr | K::Bracket => self.chain_entry(n),
            _ => self.shaped(n, false),
        }
    }

    /// Children and owned tokens in order, with no list or group logic:
    /// for nodes whose delimiters must never break, such as `scoped(p)`.
    fn plain(&mut self, n: usize) {
        let tree = self.tree;
        let end = tree.token_range(n).1 as usize;
        let mut kids = Kids::new(tree, n);
        loop {
            let ti = self.sig_idx();
            if ti >= end {
                break;
            }
            if let Some(c) = kids.peek() {
                if (tree.first_token[c] as usize) <= ti {
                    self.child(c);
                    kids.bump();
                    continue;
                }
            }
            if self.tok().is_none() {
                break;
            }
        }
        self.finish(n);
    }

    /// A comma-separated run with no delimiters of its own (a `use`
    /// header): one group, continuation lines indented one level. The
    /// indent is pushed AFTER the first token, because an indent that
    /// arrives while a newline is still pending would indent this line.
    fn wrapped(&mut self, n: usize) {
        self.group_open();
        let mut kids = Kids::new(self.tree, n);
        let first = kids.peek().map_or(usize::MAX, |c| self.tree.first_token[c] as usize);
        self.tokens_until(first);
        self.push(Op::Indent);
        self.shaped_from(n, &mut kids, false);
        self.push(Op::Dedent);
        self.push(Op::Close);
    }

    fn file(&mut self, n: usize) {
        let mut first = true;
        for c in self.tree.children(n) {
            if !first {
                self.set(Sep::Hard);
                self.blank_ok = true;
            }
            self.child(c);
            first = false;
        }
        // the file's trailing comments, which belong to `Eof`
        self.finish(n);
    }

    /// The generic node walk: children in order, owned tokens in the gaps,
    /// and — when the node owns a delimiter pair — the items inside it laid
    /// out as a list. `always` makes the pair a block (one item per line);
    /// otherwise it is a group that stays on one line while it fits.
    fn shaped(&mut self, n: usize, always: bool) {
        let mut kids = Kids::new(self.tree, n);
        self.shaped_from(n, &mut kids, always);
    }

    fn shaped_from(&mut self, n: usize, kids: &mut Kids<'a>, always: bool) {
        let tree = self.tree;
        let end = tree.token_range(n).1 as usize;
        let mut close: Option<T> = None;
        let mut first_item = true;
        let mut contracted = false;
        loop {
            let ti = self.sig_idx();
            if ti >= end {
                break;
            }
            if let Some(c) = kids.peek() {
                if (tree.first_token[c] as usize) <= ti {
                    if close.is_some() {
                        if !first_item {
                            if always {
                                self.set(Sep::Hard);
                            }
                            self.blank_ok = true;
                        }
                        first_item = false;
                    } else if tree.kinds[c] == K::Contract {
                        // a `pre`/`post`/`invariant` clause always owns its
                        // line, so the `{` under it always owns one too
                        if !contracted {
                            self.push(Op::Indent);
                            contracted = true;
                        }
                        self.set(Sep::Hard);
                    }
                    self.child(c);
                    kids.bump();
                    continue;
                }
            }
            let k = self.toks.kinds[ti];
            match k {
                T::LParen if close.is_none() && !always && self.hugs(kids) => {
                    // MARC: a call whose ONLY argument is a block-bodied
                    // closure hugs it — `v.each(|x| {` ... `});` — instead of
                    // dropping the closure to its own line because the block
                    // inside it can never fit. "Blocks always break" still
                    // holds: the block breaks, the parens do not. Only the
                    // single-argument form hugs; with more arguments the
                    // list breaks as any list does, one argument per line.
                    self.tok();
                    self.set(Sep::None);
                    let c = kids.peek().unwrap_or(n);
                    self.child(c);
                    kids.bump();
                    self.set(Sep::None);
                }
                T::LParen | T::LBracket | T::LBrace if close.is_none() => {
                    let c = match k {
                        T::LParen => T::RParen,
                        T::LBracket => T::RBracket,
                        _ => T::RBrace,
                    };
                    if contracted {
                        self.push(Op::Dedent);
                        contracted = false;
                        self.set(Sep::Hard);
                    }
                    self.tok();
                    if self.peek_no_comment() == Some(c) {
                        self.set(Sep::None);
                        self.tok();
                        continue;
                    }
                    close = Some(c);
                    first_item = true;
                    if always {
                        self.push(Op::Indent);
                        self.set(Sep::Hard);
                    } else {
                        self.push(Op::Open);
                        self.push(Op::Indent);
                        self.set(if k == T::LBrace { Sep::Line } else { Sep::Soft });
                    }
                }
                _ if Some(k) == close => {
                    self.trivia();
                    // MARC: magic trailing comma. The formatter must not add
                    // or remove a token, so it cannot insert one — but a
                    // comma the author left before the closer is a request to
                    // keep this list one-per-line, and honouring it is the
                    // only way an author can pin a wide list open.
                    if !always && self.prev == Some(T::Comma) {
                        self.push(Op::Ghost(FORCE));
                    }
                    self.push(Op::Dedent);
                    self.set(if always {
                        Sep::Hard
                    } else if k == T::RBrace {
                        Sep::Line
                    } else {
                        Sep::Soft
                    });
                    self.tok();
                    if !always {
                        self.push(Op::Close);
                    }
                    close = None;
                }
                T::Comma => {
                    self.tok();
                    self.set(if always { Sep::Hard } else { Sep::Line });
                }
                _ => {
                    if self.tok().is_none() {
                        break;
                    }
                }
            }
        }
        if contracted {
            self.push(Op::Dedent);
        }
        self.finish(n);
    }

    /// Whether the `(` at the cursor opens a list whose only item is a
    /// closure with a block body, directly followed by the `)`.
    fn hugs(&self, kids: &Kids<'a>) -> bool {
        let tree = self.tree;
        let Some(c) = kids.peek() else { return false };
        if tree.kinds[c] != K::Closure {
            return false;
        }
        let Some(body) = tree.children(c).last() else { return false };
        if tree.kinds[body] != K::Block {
            return false;
        }
        // the item must start right after `(` and end right before `)`
        let mut i = self.sig_idx() + 1;
        while i < self.toks.len() && self.toks.kinds[i].is_trivia() {
            i += 1;
        }
        if i != tree.first_token[c] as usize {
            return false;
        }
        let mut j = tree.token_range(c).1 as usize;
        while j < self.toks.len() && self.toks.kinds[j].is_trivia() {
            j += 1;
        }
        if j >= self.toks.len() || self.toks.kinds[j] != T::RParen {
            return false;
        }
        let mut rest = *kids;
        rest.bump();
        rest.peek().is_none_or(|next| tree.first_token[next] as usize > j)
    }

    // ---- declarations ----

    fn fn_like(&mut self, n: usize) {
        let tree = self.tree;
        let mut kids = Kids::new(tree, n);
        let has_block = tree.children(n).any(|c| tree.kinds[c] == K::Block);
        while let Some(c) = kids.peek() {
            match tree.kinds[c] {
                K::Attribute => {
                    self.child(c);
                    self.set(Sep::Hard);
                }
                K::FnSig => {
                    self.tokens_until(tree.first_token[c] as usize);
                    self.fn_sig(c, has_block);
                    self.cursor = tree.token_range(c).1 as usize;
                    if has_block {
                        self.set(Sep::None); // the signature group already broke or spaced
                    }
                }
                _ => self.child(c),
            }
            kids.bump();
        }
        self.finish(n);
    }

    /// `fn name[generics](params) -> ret raises E` plus contracts. One
    /// group: when it does not fit, `raises` and the `{` move to their own
    /// lines before the parameter list is broken, because the parameter
    /// list is a group of its own and is measured again on its new line.
    fn fn_sig(&mut self, n: usize, brace: bool) {
        let tree = self.tree;
        let end = tree.token_range(n).1 as usize;
        let mut kids = Kids::new(tree, n);
        self.group_open();
        let mut indented = false;
        // The trailing group: `raises`, the contracts, and the break before
        // the body's `{`. Keeping the brace in the SAME group as those
        // clauses is what makes `{` follow the `)` of a parameter list that
        // broke on its own, and drop to its own line only when a clause
        // above it did.
        let mut tail_open = false;
        loop {
            let ti = self.sig_idx();
            if ti >= end {
                break;
            }
            if let Some(c) = kids.peek() {
                if (tree.first_token[c] as usize) <= ti {
                    match tree.kinds[c] {
                        K::Raises | K::Contract => {
                            if !tail_open {
                                self.push(Op::Open);
                                tail_open = true;
                            }
                            if !indented {
                                self.push(Op::Indent);
                                indented = true;
                            }
                            self.set(if tree.kinds[c] == K::Raises { Sep::Line } else { Sep::Hard });
                        }
                        _ => {}
                    }
                    self.child(c);
                    kids.bump();
                    continue;
                }
            }
            if self.tok().is_none() {
                break;
            }
        }
        if !tail_open {
            self.push(Op::Open);
        }
        if indented {
            self.push(Op::Dedent);
        }
        if brace {
            self.push(Op::Ghost(2)); // charge the group for ` {`
            self.push(Op::Line);
        }
        self.push(Op::Close);
        self.push(Op::Close);
        self.finish(n);
    }

    // ---- expressions ----

    /// Operands separated by their operator, breaking BEFORE the operator
    /// so the operator starts the continuation line.
    fn binary(&mut self, n: usize) {
        let tree = self.tree;
        let end = tree.token_range(n).1 as usize;
        let mut kids = Kids::new(tree, n);
        self.group_open();
        let mut first = true;
        let mut indented = false;
        loop {
            let ti = self.sig_idx();
            if ti >= end {
                break;
            }
            if let Some(c) = kids.peek() {
                if (tree.first_token[c] as usize) <= ti {
                    self.child(c);
                    kids.bump();
                    if !indented {
                        self.push(Op::Indent);
                        indented = true;
                    }
                    first = false;
                    continue;
                }
            }
            if !first {
                self.set(Sep::Line);
            }
            if self.tok().is_none() {
                break;
            }
        }
        if indented {
            self.push(Op::Dedent);
        }
        self.push(Op::Close);
        self.finish(n);
    }

    /// `-x`, `move x`, and a negative literal pattern: the prefix token
    /// binds tightly when it is `-`.
    fn tight_prefix(&mut self, n: usize) {
        let tree = self.tree;
        let end = tree.token_range(n).1 as usize;
        let mut kids = Kids::new(tree, n);
        loop {
            let ti = self.sig_idx();
            if ti >= end {
                break;
            }
            if let Some(c) = kids.peek() {
                if (tree.first_token[c] as usize) <= ti {
                    self.child(c);
                    kids.bump();
                    continue;
                }
            }
            let k = self.tok();
            if k == Some(T::Minus) {
                self.set(Sep::None);
            }
            if k.is_none() {
                break;
            }
        }
        self.finish(n);
    }

    /// Number of `.name(...)` links on a postfix spine.
    fn chain_links(&self, start: usize) -> usize {
        let mut n = start;
        let mut count = 0usize;
        loop {
            let k = self.tree.kinds[n];
            if !matches!(k, K::CallExpr | K::FieldExpr | K::TryExpr | K::Bracket) {
                break;
            }
            let Some(c0) = self.tree.children(n).next() else { break };
            if k == K::FieldExpr && self.tree.kinds[c0] == K::CallExpr {
                count += 1;
            }
            n = c0;
        }
        count
    }

    fn chain_entry(&mut self, n: usize) {
        if !self.in_chain && self.chain_links(n) >= 2 {
            self.group_open();
            self.in_chain = true;
            self.chain_indent = true;
            self.postfix(n);
            self.in_chain = false;
            if !self.chain_indent {
                self.push(Op::Dedent);
            }
            self.chain_indent = false;
            self.push(Op::Close);
        } else {
            self.postfix(n);
        }
    }

    fn postfix(&mut self, n: usize) {
        let tree = self.tree;
        let mut kids = Kids::new(tree, n);
        let Some(c0) = kids.peek() else {
            self.shaped_from(n, &mut kids, false);
            return;
        };
        let is_link = tree.kinds[n] == K::FieldExpr && tree.kinds[c0] == K::CallExpr;
        self.child(c0);
        kids.bump();
        if is_link && self.in_chain {
            if self.chain_indent {
                self.push(Op::Indent);
                self.chain_indent = false;
            }
            // Soft, not Line: a chain that fits has no space before its dots
            self.set(Sep::Soft);
        }
        // arguments and indices are not part of the spine
        let saved = std::mem::replace(&mut self.in_chain, false);
        self.shaped_from(n, &mut kids, false);
        self.in_chain = saved;
    }

    // ---- misc shapes ----

    fn arm(&mut self, n: usize) {
        let tree = self.tree;
        let mut kids = Kids::new(tree, n);
        if let Some(pat) = kids.peek() {
            self.child(pat);
            kids.bump();
        }
        self.tokens_until(self.sig_idx() + 1); // `=>`
        match kids.peek() {
            Some(body) if tree.kinds[body] == K::Block => {
                self.set(Sep::Space);
                self.child(body);
                kids.bump();
            }
            Some(body) => {
                self.group_open();
                self.push(Op::Indent);
                self.set(Sep::Line);
                self.child(body);
                kids.bump();
                self.push(Op::Dedent);
                self.push(Op::Close);
            }
            None => {}
        }
        self.shaped_from(n, &mut kids, false);
    }

    /// `|a, b| body` — the pipes hug their parameters.
    fn pipes(&mut self, n: usize) {
        let tree = self.tree;
        let end = tree.token_range(n).1 as usize;
        let mut kids = Kids::new(tree, n);
        let mut open = false;
        let mut done = false;
        loop {
            let ti = self.sig_idx();
            if ti >= end {
                break;
            }
            if let Some(c) = kids.peek() {
                if (tree.first_token[c] as usize) <= ti {
                    self.child(c);
                    kids.bump();
                    continue;
                }
            }
            let k = self.toks.kinds[ti];
            if k == T::Pipe && !done {
                if !open {
                    self.tok();
                    self.set(Sep::None);
                    open = true;
                } else {
                    self.set(Sep::None);
                    self.tok();
                    done = true;
                }
                continue;
            }
            if self.tok().is_none() {
                break;
            }
            if k == T::Comma {
                self.set(Sep::Space);
            }
        }
        self.finish(n);
    }

    /// `else |e| { ... }` on the call's closing line.
    fn handler(&mut self, n: usize) {
        self.pipes(n);
    }
}
