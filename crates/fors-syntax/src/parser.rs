//! Hand-written recursive-descent parser for Fors (spec ch07). No
//! backtracking, no symbol table, at most 2 tokens of lookahead for every
//! grammar decision (the one longer scan, [`Parser::attrs_precede_decl`],
//! is error recovery only). Builds a [`crate::tree::Tree`] and never
//! panics: every failure, including nesting past [`MAX_DEPTH`], becomes a
//! [`Diagnostic`] and an `Error` node, and every loop makes forward
//! progress so arbitrary or truncated input terminates in linear time.
//!
//! Decisions that depend on what follows an already-parsed operand
//! (postfix and binary operators, struct literals, assignment) wrap the
//! finished operand node (`TreeBuilder::wrap_last_sibling`); nothing is
//! re-scanned. Every expression function therefore leaves exactly one
//! finished node behind, and returns whether it has the shape of a
//! `place` (rule 9).
//!
//! Recovery: one diagnostic per token position (a failure usually trips
//! several expectations at the same token; only the first is reported),
//! then a skip to the fixed synchronisation sets of ch07 "Error recovery".

use fors_lex::{TokenKind, Tokens};

use crate::diag::{DiagCode, Diagnostic};
use crate::node_kind::NodeKind;
use crate::tree::{Tree, TreeBuilder};

/// Nesting limit for every recursive production. It bounds both the
/// parser's stack (about 15 frames per level) and, together with
/// [`MAX_POSTFIX_CHAIN`], the depth of the tree later phases recurse over.
const MAX_DEPTH: u32 = 128;
/// Postfix operators nest the tree without recursing in the parser.
const MAX_POSTFIX_CHAIN: u32 = 1024;
/// Bound on the recovery-only attribute scan.
const MAX_ATTR_SCAN: usize = 64;

/// Everything later phases need from one file: the token columns the tree
/// indexes into, the tree, and the lexical + syntax diagnostics in source
/// order.
pub struct Parse {
    pub tokens: Tokens,
    pub tree: Tree,
    pub diags: Vec<Diagnostic>,
}

pub fn parse_file(source: &[u8]) -> Parse {
    let (tokens, lex_diags) = fors_lex::lex(source);
    let (tree, diags) = parse_tokens(&tokens, &lex_diags, source);
    Parse {
        tokens,
        tree,
        diags,
    }
}

pub fn parse(source: &[u8]) -> (Tree, Vec<Diagnostic>) {
    let p = parse_file(source);
    (p.tree, p.diags)
}

fn lex_message(code: fors_lex::DiagCode) -> &'static str {
    use fors_lex::DiagCode::*;
    match code {
        UnterminatedBlockComment => "unterminated block comment",
        UnterminatedString => "unterminated string literal",
        BadEscape => "invalid escape in string literal",
        BadSuffix => "invalid literal suffix",
        BadRangeDots => "'..' is not an operator; expected '..<' or '..='",
        StrayByte => "character is not part of any token",
        FileTooLarge => "source file too large",
        InvalidUtf8 => "source is not valid UTF-8",
    }
}

fn parse_tokens(
    tokens: &Tokens,
    lex_diags: &[fors_lex::Diagnostic],
    source: &[u8],
) -> (Tree, Vec<Diagnostic>) {
    // Lexical-error tokens are reported once (by the lexer) and skipped:
    // to the grammar they are trivia.
    let mut sig = Vec::with_capacity(tokens.len() / 2 + 1);
    for (i, &k) in tokens.kinds.iter().enumerate() {
        if !k.is_trivia() && k != TokenKind::Error {
            sig.push(i as u32);
        }
    }
    let mut diags: Vec<Diagnostic> = lex_diags
        .iter()
        .map(|d| {
            Diagnostic::new(
                d.start,
                d.end.max(d.start.saturating_add(1)),
                DiagCode::LexError,
                lex_message(d.code),
            )
        })
        .collect();
    let has_lex_diags = !diags.is_empty();

    let ends_in_eof = sig
        .last()
        .is_some_and(|&i| tokens.kinds[i as usize] == TokenKind::Eof);
    if !ends_in_eof {
        // `lex` always ends the stream with `Eof`; never let a stream that
        // does not reach the cursor logic.
        let mut b = TreeBuilder::new();
        b.start_node(NodeKind::File);
        b.bump_raw(tokens.len() as u32);
        b.finish_node();
        return (b.finish(), diags);
    }

    let mut p = Parser {
        tokens,
        source,
        sig,
        p: 0,
        b: TreeBuilder::with_capacity(tokens.len() / 3),
        diags: Vec::new(),
        last_err_p: usize::MAX,
        depth: 0,
        depth_reported: false,
        in_struct_header: false,
        in_member_body: 0,
    };
    p.file();
    let tree = p.b.finish();
    diags.append(&mut p.diags);
    if has_lex_diags {
        diags.sort_by_key(|d| d.start);
    }
    (tree, diags)
}

struct Parser<'a> {
    tokens: &'a Tokens,
    source: &'a [u8],
    /// Raw indices of every significant token; the last one is `Eof`.
    sig: Vec<u32>,
    p: usize,
    b: TreeBuilder,
    diags: Vec<Diagnostic>,
    /// Cursor position of the last reported diagnostic (see module docs).
    last_err_p: usize,
    depth: u32,
    depth_reported: bool,
    /// Parsing a struct's `invariant` clauses: the `{` after them opens a
    /// field list, not a block.
    in_struct_header: bool,
    /// Enclosing `trait`/`impl` bodies. The receiver shorthand `convention
    /// "self"` (ch07 Disambiguation 21, owner decision 2026-09-19 round 5,
    /// D1) is legal only inside one.
    in_member_body: u32,
}

/// The one fixed diagnostic of ch07 Disambiguation 21 (round 5, D1).
const RECEIVER_SHORTHAND_MSG: &str =
    "only a parameter named \"self\", in a trait or impl body, may omit its type annotation";

fn is_mul_op(k: TokenKind) -> bool {
    matches!(k, TokenKind::Star | TokenKind::Slash | TokenKind::Percent)
}

fn is_add_op(k: TokenKind) -> bool {
    matches!(k, TokenKind::Plus | TokenKind::Minus)
}

fn is_range_op(k: TokenKind) -> bool {
    matches!(k, TokenKind::DotDotLt | TokenKind::DotDotEq)
}

fn is_cmp_op(k: TokenKind) -> bool {
    use TokenKind::*;
    matches!(k, EqEq | NotEq | Lt | Gt | LtEq | GtEq)
}

fn is_bit_op(k: TokenKind) -> bool {
    use TokenKind::*;
    matches!(k, Amp | Pipe | Caret | Shl | Shr)
}

fn is_binop(k: TokenKind) -> bool {
    is_mul_op(k) || is_add_op(k) || is_range_op(k) || is_cmp_op(k) || is_bit_op(k)
}

fn is_assign_op(k: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        k,
        Eq | PlusEq
            | MinusEq
            | StarEq
            | SlashEq
            | PercentEq
            | AmpEq
            | PipeEq
            | CaretEq
            | ShlEq
            | ShrEq
    )
}

/// Operator tokens that cannot begin an expression: a `bare_op` on one
/// token of lookahead (rule 7). `-`, `|`, `&` need the second token.
fn is_unambiguous_bare_op(k: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        k,
        Plus | Star | Slash | Percent | Caret | Shl | Shr | KwAnd | KwOr
    ) || is_cmp_op(k)
}

fn is_stmt_keyword(k: TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        k,
        KwLet
            | KwVar
            | KwIf
            | KwMatch
            | KwFor
            | KwWhile
            | KwBreak
            | KwContinue
            | KwReturn
            | KwRaise
            | KwWith
            | KwParallel
            | KwSimd
            | KwSpawn
            | KwConsume
            | KwDiscard
            | KwComptime
            | KwDefer
            | KwErrdefer
    )
}

fn is_opener(k: TokenKind) -> bool {
    matches!(
        k,
        TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace
    )
}

fn is_closer(k: TokenKind) -> bool {
    matches!(
        k,
        TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
    )
}

fn open_msg(k: TokenKind) -> &'static str {
    match k {
        TokenKind::LParen => "expected '('",
        TokenKind::LBracket => "expected '['",
        TokenKind::LBrace => "expected '{'",
        _ => "expected '|'",
    }
}

fn close_msg(k: TokenKind) -> &'static str {
    match k {
        TokenKind::RParen => "expected ',' or ')'",
        TokenKind::RBracket => "expected ',' or ']'",
        TokenKind::RBrace => "expected '}'",
        _ => "expected ',' or '|'",
    }
}

fn unclosed_msg(k: TokenKind) -> &'static str {
    match k {
        TokenKind::RParen => "unclosed '('",
        TokenKind::RBracket => "unclosed '['",
        TokenKind::RBrace => "unclosed '{'",
        _ => "unclosed '|'",
    }
}

impl<'a> Parser<'a> {
    // ---- token cursor ----

    fn raw(&self, n: usize) -> usize {
        // `sig` is never empty (it ends in `Eof`); lookahead past the end
        // keeps answering `Eof`.
        let i = (self.p + n).min(self.sig.len() - 1);
        self.sig[i] as usize
    }

    fn nth(&self, n: usize) -> TokenKind {
        self.tokens.kinds[self.raw(n)]
    }

    fn cur(&self) -> TokenKind {
        self.nth(0)
    }

    fn at(&self, k: TokenKind) -> bool {
        self.cur() == k
    }

    fn word_at(&self, n: usize, word: &[u8]) -> bool {
        self.nth(n) == TokenKind::Ident && self.tokens.text(self.raw(n), self.source) == word
    }

    fn is_word(&self, word: &[u8]) -> bool {
        self.word_at(0, word)
    }

    fn cur_range(&self) -> (u32, u32) {
        self.tokens.range(self.raw(0))
    }

    fn prev_end(&self) -> u32 {
        if self.p == 0 {
            0
        } else {
            self.tokens.range(self.sig[self.p - 1] as usize).1
        }
    }

    /// Consumes the current significant token and its leading trivia.
    /// `Eof` is consumed only by `file`, so the trailing trivia is `File`'s.
    fn bump(&mut self) {
        if self.p + 1 < self.sig.len() {
            self.bump_any();
            self.p += 1;
        }
    }

    fn bump_any(&mut self) {
        let raw = self.sig[self.p];
        self.b
            .bump_raw((raw + 1).saturating_sub(self.b.cur_token()));
    }

    fn opt(&mut self, k: TokenKind) -> bool {
        if self.at(k) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn err_at(&mut self, start: u32, end: u32, code: DiagCode, msg: &'static str) {
        if self.last_err_p == self.p {
            return;
        }
        self.last_err_p = self.p;
        self.diags.push(Diagnostic::new(
            start,
            end.max(start.saturating_add(1)),
            code,
            msg,
        ));
    }

    fn err_here(&mut self, code: DiagCode, msg: &'static str) {
        let (mut s, mut e) = self.cur_range();
        if self.at(TokenKind::Eof) {
            // point at the last real token, not past the end of the file
            e = self.prev_end();
            s = e.saturating_sub(1);
        }
        self.err_at(s, e, code, msg);
    }

    fn expect(&mut self, k: TokenKind, msg: &'static str) -> bool {
        if self.opt(k) {
            true
        } else {
            self.err_here(DiagCode::Expected, msg);
            false
        }
    }

    fn enter(&mut self) -> bool {
        if self.depth < MAX_DEPTH {
            self.depth += 1;
            return true;
        }
        self.too_deep();
        false
    }

    fn leave(&mut self) {
        self.depth -= 1;
    }

    /// Leaves one `Error` node. A bracketed group is swallowed whole so the
    /// callers being unwound still find their own closers.
    fn too_deep(&mut self) {
        if !self.depth_reported {
            self.depth_reported = true;
            self.err_here(DiagCode::NestingTooDeep, "nesting too deep");
        }
        if is_opener(self.cur()) {
            self.skip_group();
        } else {
            self.b.empty_node(NodeKind::Error);
        }
    }

    /// At an opener: skips the balanced group into one `Error` node.
    fn skip_group(&mut self) {
        self.b.start_node(NodeKind::Error);
        let mut depth = 0u32;
        while !self.at(TokenKind::Eof) && !self.at_decl_sync() {
            let k = self.cur();
            if is_opener(k) {
                depth += 1;
            } else if is_closer(k) {
                depth = depth.saturating_sub(1);
            }
            self.bump();
            if depth == 0 {
                break;
            }
        }
        self.b.finish_node();
    }

    // ---- synchronisation sets ----

    fn decl_sync_at(&self, o: usize) -> bool {
        use TokenKind::*;
        match self.nth(o) {
            KwModule | KwUse | KwStruct | KwEnum | KwTrait | KwImpl | KwConst | KwExtern => true,
            KwFn => self.nth(o + 1) == Ident,
            KwPub => match self.nth(o + 1) {
                KwUse | KwFn | KwStruct | KwEnum | KwTrait | KwImpl | KwConst | KwExtern => true,
                Ident => self.nth(o + 2) == KwStruct && self.word_at(o + 1, b"soa"),
                _ => false,
            },
            Ident => self.nth(o + 1) == KwStruct && self.word_at(o, b"soa"),
            _ => false,
        }
    }

    /// At a declaration-sync token, or at the attribute run in front of one
    /// ("a run of attributes immediately before the sync token belongs to
    /// the resumed declaration").
    fn at_decl_sync(&self) -> bool {
        self.decl_sync_at(0) || (self.at(TokenKind::At) && self.attrs_precede_decl())
    }

    /// A declaration-sync token that cannot be an item of a `trait`/`impl`
    /// body, i.e. the body's `}` is missing.
    fn at_body_overrun(&self) -> bool {
        use TokenKind::*;
        self.decl_sync_at(0) && !(self.at(KwFn) || (self.at(KwPub) && self.nth(1) == KwFn))
    }

    /// Recovery only, the one scan longer than two tokens: is the attribute
    /// run at the cursor followed by a declaration? Bounded.
    fn attrs_precede_decl(&self) -> bool {
        use TokenKind::*;
        let mut i = 0usize;
        while self.nth(i) == At {
            if self.nth(i + 1) != Ident {
                return false;
            }
            i += 2;
            if self.nth(i) == LParen {
                while self.nth(i) != RParen {
                    if self.nth(i) == Eof || i > MAX_ATTR_SCAN {
                        return false;
                    }
                    i += 1;
                }
                i += 1;
            }
        }
        self.decl_sync_at(i)
    }

    fn at_stmt_sync(&self) -> bool {
        let k = self.cur();
        k == TokenKind::Semi
            || k == TokenKind::RBrace
            || k == TokenKind::Eof
            || is_stmt_keyword(k)
            || self.at_decl_sync()
    }

    /// Tokens an error production must not swallow: the enclosing
    /// construct resynchronises on them.
    fn at_recovery_stop(&self) -> bool {
        use TokenKind::*;
        let k = self.cur();
        matches!(k, Semi | Comma | FatArrow | LBrace | KwElse | At | Eof)
            || is_closer(k)
            || is_stmt_keyword(k)
            || self.at_decl_sync()
    }

    fn error_node(&mut self) {
        self.b.start_node(NodeKind::Error);
        if !self.at_recovery_stop() {
            self.bump();
        }
        self.b.finish_node();
    }

    /// Loop guard: an item that consumed nothing costs one skipped token.
    fn guard_progress(&mut self, before: usize) {
        if self.p != before || self.at(TokenKind::Eof) {
            return;
        }
        self.err_here(DiagCode::UnexpectedToken, "unexpected token");
        self.b.start_node(NodeKind::Error);
        self.bump();
        self.b.finish_node();
    }

    /// Attaches `fix` to the diagnostic the immediately preceding
    /// `err_at`/`err_here` pushed — `before` is `self.diags.len()` from
    /// just before that call, because the one-error-per-token dedup in
    /// [`Self::err_at`] can swallow it and the fix would then land on an
    /// unrelated diagnostic.
    fn attach_fix(&mut self, before: usize, fix: fors_diag::Fix) {
        if self.diags.len() > before
            && let Some(d) = self.diags.last_mut()
        {
            d.fixes.push(fix);
        }
    }

    fn expect_semi(&mut self) {
        if self.opt(TokenKind::Semi) {
            return;
        }
        if self.at_stmt_sync() {
            // virtual insertion: nothing is skipped
            let e = self.prev_end();
            let before = self.diags.len();
            self.err_at(
                e.saturating_sub(1),
                e,
                DiagCode::MissingSemicolon,
                "missing ';'",
            );
            // The parse that follows this point is already the parse of the
            // text WITH the `;`, so the insertion point is not a guess.
            self.attach_fix(
                before,
                fors_diag::Fix::insert(fors_diag::FixKind::InsertSemicolon, "insert `;`", e, ";"),
            );
            return;
        }
        // MARC: no fix-it here, deliberately. Unlike the branch above, this
        // one goes on to SKIP tokens to a sync point, so "a `;` is missing"
        // is only one reading of what the parser found — in the corpus it
        // is usually the WRONG one (a reserved word used as an identifier,
        // an `else` after `?`). The arbiter test (`fors-cli/tests/fixes.rs`)
        // measured it: inserting `;` at all fifteen corpus sites introduced
        // a new parse error at several of them. A fix that has to be
        // reviewed AND is usually wrong costs an agent more than no fix.
        self.err_here(DiagCode::Expected, "expected ';'");
        self.b.start_node(NodeKind::Error);
        let mut depth = 0u32;
        while !self.at(TokenKind::Eof) && !self.at_decl_sync() {
            let k = self.cur();
            if depth == 0 && (k == TokenKind::Semi || k == TokenKind::RBrace || is_stmt_keyword(k))
            {
                break;
            }
            if is_opener(k) {
                depth += 1;
            } else if is_closer(k) {
                depth = depth.saturating_sub(1);
            }
            self.bump();
        }
        self.b.finish_node();
        self.opt(TokenKind::Semi);
    }

    // ---- delimited lists ----

    /// `open [ item { "," item } [ "," ] ] close`.
    fn delimited(
        &mut self,
        open: TokenKind,
        close: TokenKind,
        min_one: Option<&'static str>,
        mut item: impl FnMut(&mut Self),
    ) {
        let (os, oe) = self.cur_range();
        if !self.expect(open, open_msg(open)) {
            return;
        }
        if let Some(msg) = min_one
            && self.at(close)
        {
            self.err_here(DiagCode::Expected, msg);
        }
        while !self.at(close) && !self.at(TokenKind::Eof) && !self.at_decl_sync() {
            let before = self.p;
            item(self);
            if self.p == before || !self.opt(TokenKind::Comma) {
                break;
            }
        }
        self.close(os, oe, close);
    }

    /// Consumes `close`. If it is missing: at a declaration or the end of
    /// the file the opener is reported as unclosed and nothing is skipped;
    /// otherwise tokens are skipped, tracking depth, up to the closer.
    fn close(&mut self, open_start: u32, open_end: u32, close: TokenKind) {
        if self.opt(close) {
            return;
        }
        if self.at(TokenKind::Eof) || self.at_decl_sync() {
            self.err_at(
                open_start,
                open_end,
                DiagCode::UnclosedBrace,
                unclosed_msg(close),
            );
            return;
        }
        self.err_here(DiagCode::Expected, close_msg(close));
        let mut depth = 0u32;
        let mut open_node = false;
        while !self.at(TokenKind::Eof) && !self.at_decl_sync() {
            let k = self.cur();
            if depth == 0 && (k == close || k == TokenKind::Semi || is_closer(k)) {
                break;
            }
            if is_opener(k) {
                depth += 1;
            } else if is_closer(k) {
                depth -= 1; // depth > 0: a closer at depth 0 stopped the loop
            }
            if !open_node {
                open_node = true;
                self.b.start_node(NodeKind::Error);
            }
            self.bump();
        }
        if open_node {
            self.b.finish_node();
        }
        self.opt(close);
    }

    // ================= file and declarations =================

    fn path_tokens(&mut self) {
        self.expect(TokenKind::Ident, "expected identifier");
        while self.at(TokenKind::Dot) && self.nth(1) == TokenKind::Ident {
            self.bump();
            self.bump();
        }
    }

    fn path(&mut self, kind: NodeKind) {
        self.b.start_node(kind);
        self.path_tokens();
        self.b.finish_node();
    }

    /// `path [ "as" ident ]` (ch07 grammar `use_item`, D2). The alias binds
    /// only the alias name (ch08 R3-6); resolving is the checker's.
    fn use_item(&mut self) {
        self.b.start_node(NodeKind::UseItem);
        self.path(NodeKind::Path);
        if self.opt(TokenKind::KwAs) {
            self.expect(TokenKind::Ident, "expected an identifier after 'as'");
        }
        self.b.finish_node();
    }

    /// A single `needs` item. The sealed capability vocabulary is a closed,
    /// single-segment set (`ffi`, `syscall`, `asm`, ...); `asm` also being
    /// reserved (R2-4) would otherwise make it unspellable here, so a lone
    /// `asm` keyword is accepted as this one path's only segment.
    fn needs_path(&mut self) {
        if self.at(TokenKind::KwAsm) {
            self.b.start_node(NodeKind::Path);
            self.bump();
            self.b.finish_node();
        } else {
            self.path(NodeKind::Path);
        }
    }

    fn dot_lit(&mut self) {
        self.b.start_node(NodeKind::DotLit);
        self.expect(TokenKind::Dot, "expected '.'");
        self.expect(TokenKind::Ident, "expected identifier after '.'");
        self.b.finish_node();
    }

    fn file(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::File);
        if self.at(KwModule) {
            self.b.start_node(NodeKind::ModuleHdr);
            self.bump();
            self.path(NodeKind::Path);
            self.expect_semi();
            self.b.finish_node();
        }
        if self.is_word(b"contracts") {
            self.b.start_node(NodeKind::ContractsClause);
            self.bump();
            self.expect(Colon, "expected ':' after 'contracts'");
            self.dot_lit();
            self.expect_semi();
            self.b.finish_node();
        }
        if self.is_word(b"needs") {
            self.b.start_node(NodeKind::NeedsClause);
            self.bump();
            self.delimited(LBrace, RBrace, None, |p| p.needs_path());
            self.expect_semi();
            self.b.finish_node();
        }
        if self.is_word(b"inputs") {
            self.b.start_node(NodeKind::InputsClause);
            self.bump();
            self.delimited(LBrace, RBrace, None, |p| {
                if matches!(p.cur(), Str | MultilineStr) {
                    p.literal();
                } else {
                    p.err_here(DiagCode::Expected, "expected a string");
                }
            });
            self.expect_semi();
            self.b.finish_node();
        }
        while self.at(KwUse) || (self.at(KwPub) && self.nth(1) == KwUse) {
            self.b.start_node(NodeKind::UseDecl);
            self.opt(KwPub);
            self.bump(); // use
            self.use_item();
            while self.opt(Comma) {
                self.use_item();
            }
            self.expect_semi();
            self.b.finish_node();
        }
        while !self.at(Eof) {
            self.decl();
        }
        self.bump_any(); // Eof and the trailing trivia
        self.b.finish_node();
    }

    fn attribute(&mut self) {
        self.b.start_node(NodeKind::Attribute);
        self.bump(); // @
        self.expect(TokenKind::Ident, "expected attribute name");
        if self.at(TokenKind::LBracket) {
            self.err_here(
                DiagCode::Expected,
                "attribute arguments take '( )', not '[ ]'",
            );
            self.skip_group();
        } else if self.at(TokenKind::LParen) {
            self.delimited(TokenKind::LParen, TokenKind::RParen, None, |p| p.attr_arg());
        }
        self.b.finish_node();
    }

    fn attr_arg(&mut self) {
        self.b.start_node(NodeKind::AttrArg);
        if self.at(TokenKind::Ident) && self.nth(1) == TokenKind::Colon {
            self.bump();
            self.bump();
        }
        if !self.literal() {
            if self.at(TokenKind::Ident) {
                self.path(NodeKind::Path);
            } else {
                self.err_here(
                    DiagCode::Expected,
                    "expected a literal or a path as attribute argument",
                );
            }
        }
        self.b.finish_node();
    }

    fn literal(&mut self) -> bool {
        use TokenKind::*;
        match self.cur() {
            Int | Float | Str | MultilineStr | KwTrue | KwFalse => {
                self.b.start_node(NodeKind::Literal);
                self.bump();
                self.b.finish_node();
                true
            }
            Dot if self.nth(1) == Ident => {
                self.dot_lit();
                true
            }
            _ => false,
        }
    }

    /// One top-level declaration. The node is opened before the kind is
    /// known so that attributes, `pub` and `soa` sit inside it: a
    /// declaration is one contiguous, self-contained token range.
    fn decl(&mut self) {
        use TokenKind::*;
        let before = self.p;
        self.b.start_node(NodeKind::Error);
        while self.at(At) {
            self.attribute();
        }
        self.opt(KwPub);
        let kind = match self.cur() {
            KwFn => {
                self.fn_sig();
                self.block();
                NodeKind::FnDecl
            }
            KwExtern => {
                self.bump();
                self.expect(Str, "expected ABI string after 'extern'");
                if self.at(KwFn) {
                    self.fn_sig();
                } else {
                    self.err_here(DiagCode::Expected, "expected 'fn' after the ABI string");
                }
                self.expect_semi();
                NodeKind::ExternFnDecl
            }
            KwStruct => {
                self.struct_decl();
                NodeKind::StructDecl
            }
            Ident if self.nth(1) == KwStruct && self.is_word(b"soa") => {
                self.bump();
                self.struct_decl();
                NodeKind::StructDecl
            }
            KwEnum => {
                self.bump();
                self.expect(Ident, "expected enum name");
                if self.at(LBracket) {
                    self.generics();
                }
                self.delimited(
                    LBrace,
                    RBrace,
                    Some("expected at least one enum variant"),
                    |p| p.evariant(),
                );
                NodeKind::EnumDecl
            }
            KwTrait => {
                self.bump();
                self.expect(Ident, "expected trait name");
                if self.at(LBracket) {
                    self.generics();
                }
                self.item_body(false);
                NodeKind::TraitDecl
            }
            KwImpl => {
                self.bump();
                if self.at(LBracket) {
                    self.generics();
                }
                self.type_(false);
                if self.opt(KwFor) {
                    self.type_(false);
                }
                self.item_body(true);
                NodeKind::ImplDecl
            }
            KwConst => {
                self.bump();
                self.expect(Ident, "expected const name");
                self.expect(Colon, "expected ':' and the const's type");
                self.type_(false);
                self.expect(Eq, "expected '=' and the const's value");
                self.expr(false);
                self.expect_semi();
                NodeKind::ConstDecl
            }
            KwType => {
                // ch07 Error recovery: one fixed diagnostic, skip to `;`.
                self.err_here(
                    DiagCode::UnexpectedToken,
                    "type aliases do not exist; \"type\" is legal only inside a trait or impl body",
                );
                self.bump();
                self.skip_assoc_item();
                NodeKind::Error
            }
            k => {
                let msg = if k == KwUse || k == KwModule {
                    "'module' and 'use' must precede all declarations"
                } else {
                    "expected a declaration"
                };
                self.err_here(DiagCode::UnexpectedToken, msg);
                if self.p == before {
                    self.bump();
                }
                while !self.at(Eof) && !self.at_decl_sync() && !self.at(At) {
                    self.bump();
                }
                NodeKind::Error
            }
        };
        self.b.set_current_kind(kind);
        self.b.finish_node();
    }

    /// `"{" { item } "}"` of a `trait` (`impl_body == false`) or `impl`.
    fn item_body(&mut self, impl_body: bool) {
        use TokenKind::*;
        let (os, oe) = self.cur_range();
        if !self.expect(LBrace, "expected '{'") {
            return;
        }
        self.in_member_body += 1;
        while !self.at(RBrace) && !self.at(Eof) && !self.at_body_overrun() {
            let before = self.p;
            self.b.start_node(if impl_body {
                NodeKind::FnDecl
            } else {
                NodeKind::TraitItem
            });
            while self.at(At) {
                self.attribute();
            }
            if impl_body {
                self.opt(KwPub);
            }
            if self.at(KwFn) {
                self.fn_sig();
                if impl_body || !self.opt(Semi) {
                    self.block();
                }
            } else if self.at(KwType) {
                // ch07 Disambiguation 20: an associated-type item takes no
                // attribute and no `pub`.
                if self.p != before {
                    self.err_here(
                        DiagCode::UnexpectedToken,
                        "an associated-type item takes no attribute and no 'pub'",
                    );
                }
                self.assoc_type_item(impl_body);
            } else {
                self.err_here(DiagCode::Expected, "expected 'fn' or 'type'");
                self.b.set_current_kind(NodeKind::Error);
                if self.p == before && !self.at(Eof) {
                    self.bump();
                }
            }
            self.b.finish_node();
        }
        self.in_member_body -= 1;
        self.close(os, oe, RBrace);
    }

    /// At `type` inside a `trait` (`assoc_type_decl`) or `impl`
    /// (`assoc_type_def`) body; the enclosing item node is already open.
    fn assoc_type_item(&mut self, impl_body: bool) {
        use TokenKind::*;
        self.b.set_current_kind(if impl_body {
            NodeKind::AssocTypeDef
        } else {
            NodeKind::AssocTypeDecl
        });
        self.bump(); // type
        if !self.expect(Ident, "expected associated type name") {
            self.skip_assoc_item();
            return;
        }
        if impl_body {
            if self.at(Eq) {
                self.bump();
                self.type_(false);
            } else if self.at(Semi) || self.at(Colon) {
                self.err_here(DiagCode::Expected, "an impl defines \"type A = T;\"");
            } else {
                self.err_here(
                    DiagCode::Expected,
                    "expected '=' and the associated type's definition",
                );
            }
        } else if self.at(Eq) {
            self.err_here(
                DiagCode::UnexpectedToken,
                "a trait declares \"type A;\" - the definition belongs in an impl",
            );
        } else if self.opt(Colon) {
            self.bounds();
        }
        if !self.opt(Semi) {
            self.err_here(DiagCode::Expected, "expected ';'");
            self.skip_assoc_item();
        }
    }

    /// Recovery inside a `trait`/`impl` body (ch07 Error recovery,
    /// "Associated-type items"): skip through the item's `;`, or stop at
    /// the next member of the item sync set.
    fn skip_assoc_item(&mut self) {
        use TokenKind::*;
        let mut depth = 0u32;
        let mut open_node = false;
        while !self.at(Eof) && !self.at_decl_sync() {
            let k = self.cur();
            if depth == 0 && matches!(k, Semi | RBrace | KwFn | KwType | KwPub | At) {
                break;
            }
            if is_opener(k) {
                depth += 1;
            } else if is_closer(k) {
                depth = depth.saturating_sub(1);
            }
            if !open_node {
                open_node = true;
                self.b.start_node(NodeKind::Error);
            }
            self.bump();
        }
        if open_node {
            self.b.finish_node();
        }
        self.opt(Semi);
    }

    /// `type { "+" type }`.
    fn bounds(&mut self) {
        self.type_(false);
        while self.opt(TokenKind::Plus) {
            self.type_(false);
        }
    }

    fn struct_decl(&mut self) {
        use TokenKind::*;
        self.bump(); // struct
        self.expect(Ident, "expected struct name");
        if self.at(LBracket) {
            self.generics();
        }
        self.in_struct_header = true;
        while self.is_word(b"invariant") {
            self.contract();
        }
        self.in_struct_header = false;
        self.delimited(LBrace, RBrace, None, |p| p.field());
    }

    fn contract(&mut self) {
        self.b.start_node(NodeKind::Contract);
        self.bump();
        self.expr(true);
        self.b.finish_node();
    }

    fn field(&mut self) {
        self.b.start_node(NodeKind::Field);
        self.opt(TokenKind::KwPub);
        self.expect(TokenKind::Ident, "expected field name");
        self.expect(TokenKind::Colon, "expected ':' and the field's type");
        self.type_(false);
        self.b.finish_node();
    }

    fn evariant(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::EVariant);
        self.expect(Ident, "expected variant name");
        if self.at(LParen) {
            self.delimited(
                LParen,
                RParen,
                Some("expected at least one payload type"),
                |p| p.type_(false),
            );
        } else if self.at(LBrace) {
            self.delimited(LBrace, RBrace, Some("expected at least one field"), |p| {
                p.field()
            });
        }
        self.b.finish_node();
    }

    fn generics(&mut self) {
        self.b.start_node(NodeKind::Generics);
        self.delimited(
            TokenKind::LBracket,
            TokenKind::RBracket,
            Some("expected a generic parameter"),
            |p| p.gparam(),
        );
        self.b.finish_node();
    }

    /// `gentry`: the token after the identifier decides (ch07
    /// Disambiguation 19, LA 2): `.` selects `gconstraint`.
    fn gparam(&mut self) {
        use TokenKind::*;
        if self.at(Ident) && self.nth(1) == Dot {
            self.b.start_node(NodeKind::GConstraint);
            self.bump();
            self.bump();
            if self.expect(Ident, "expected an associated type name after '.'") {
                if self.at(Eq) {
                    self.equality_bound();
                } else if self.expect(Colon, "expected ':' and the bounds of the constraint entry")
                {
                    self.bounds();
                }
            }
            self.b.finish_node();
            return;
        }
        self.b.start_node(NodeKind::GParam);
        self.expect(Ident, "expected generic parameter name");
        if self.opt(Colon) {
            if self.is_word(b"brand") {
                self.bump();
            } else {
                self.bounds();
            }
        } else if self.at(Eq) {
            self.equality_bound();
        }
        self.b.finish_node();
    }

    /// At `=` in a `gentry`: fixed message, recover at the next `,` / `]`.
    fn equality_bound(&mut self) {
        use TokenKind::*;
        self.err_here(
            DiagCode::UnexpectedToken,
            "associated-type equality bounds do not exist; constrain with \":\"",
        );
        self.b.start_node(NodeKind::Error);
        let mut depth = 0u32;
        while !self.at(Eof) && !self.at_decl_sync() {
            let k = self.cur();
            if depth == 0 && matches!(k, Comma | RBracket | LBrace | Semi) {
                break;
            }
            if is_opener(k) {
                depth += 1;
            } else if is_closer(k) {
                depth = depth.saturating_sub(1);
            }
            self.bump();
        }
        self.b.finish_node();
    }

    fn convention(&mut self) {
        use TokenKind::*;
        if matches!(self.cur(), KwLet | KwInout | KwSink) || self.is_word(b"set") {
            self.bump();
        } else {
            self.err_here(
                DiagCode::Expected,
                "expected a convention (let/inout/sink/set)",
            );
        }
    }

    /// At `fn`.
    fn fn_sig(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::FnSig);
        self.bump(); // fn
        self.expect(Ident, "expected function name");
        if self.at(LBracket) {
            self.generics();
        }
        self.b.start_node(NodeKind::Params);
        self.delimited(LParen, RParen, None, |p| p.param());
        self.b.finish_node();
        if self.opt(Arrow) {
            self.type_(true);
        }
        self.raises();
        while self.is_word(b"pre") || self.is_word(b"post") || self.is_word(b"invariant") {
            self.contract();
        }
        self.b.finish_node();
    }

    fn raises(&mut self) {
        if self.at(TokenKind::KwRaises) {
            self.b.start_node(NodeKind::Raises);
            self.bump();
            self.type_(false);
            self.b.finish_node();
        }
    }

    /// `param = convention ident ":" type | convention "self"` (ch07
    /// Disambiguation 21). One token of lookahead decides: a `:` after the
    /// identifier takes the annotated form, anything else the receiver
    /// shorthand — which is legal only for the identifier `self` and only
    /// inside a `trait`/`impl` body, both checked here with one fixed
    /// diagnostic.
    fn param(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::Param);
        self.convention();
        if self.at(Ident) && self.nth(1) != Colon {
            if self.in_member_body > 0 && self.is_word(b"self") {
                self.bump(); // `self`, type `Self` (ch09 Rule 16)
                self.b.finish_node();
                return;
            }
            self.err_here(DiagCode::Expected, RECEIVER_SHORTHAND_MSG);
            self.bump();
            self.b.finish_node();
            return;
        }
        self.expect(Ident, "expected parameter name");
        self.expect(Colon, "expected ':' and the parameter's type");
        self.type_(false);
        self.b.finish_node();
    }

    // ================= types =================

    /// `type`, or `ret_type` when `ret` (which adds the `scoped(x)` prefix,
    /// also on tuple elements).
    fn type_(&mut self, ret: bool) {
        use TokenKind::*;
        if !self.enter() {
            return;
        }
        let scoped = ret && self.nth(1) == LParen && self.is_word(b"scoped");
        if scoped {
            self.b.start_node(NodeKind::ScopedType);
            self.bump();
            self.bump();
            self.expect(Ident, "expected a binding name in 'scoped(...)'");
            self.expect(RParen, "expected ')'");
        }
        if matches!(self.cur(), KwIso | KwImm | KwSecret) {
            self.b.start_node(NodeKind::QualType);
            while matches!(self.cur(), KwIso | KwImm | KwSecret) {
                self.bump();
            }
            self.type_core(ret);
            self.b.finish_node();
        } else {
            self.type_core(ret);
        }
        if scoped {
            self.b.finish_node();
        }
        self.leave();
    }

    fn type_core(&mut self, ret: bool) {
        use TokenKind::*;
        match self.cur() {
            Ident => {
                self.type_app();
            }
            LParen => {
                self.b.start_node(NodeKind::TupleType);
                self.delimited(LParen, RParen, None, |p| p.type_(ret));
                self.b.finish_node();
            }
            KwFn => {
                self.b.start_node(NodeKind::FnType);
                self.bump();
                self.delimited(LParen, RParen, None, |p| {
                    p.b.start_node(NodeKind::FParam);
                    p.convention();
                    p.type_(false);
                    p.b.finish_node();
                });
                if self.opt(Arrow) {
                    self.type_(false);
                }
                self.raises();
                self.b.finish_node();
            }
            KwDyn => {
                self.b.start_node(NodeKind::DynType);
                self.bump();
                if self.at(Ident) {
                    self.type_app();
                } else {
                    self.err_here(DiagCode::Expected, "expected a trait path after 'dyn'");
                }
                self.b.finish_node();
            }
            _ => {
                self.err_here(
                    DiagCode::Expected,
                    if ret {
                        "expected a return type"
                    } else {
                        "expected a type"
                    },
                );
                self.b.empty_node(NodeKind::Error);
            }
        }
    }

    /// At an identifier. Returns whether the type is a bare `path`.
    fn type_app(&mut self) -> bool {
        self.b.start_node(NodeKind::TypeApp);
        self.path_tokens();
        let bare = !self.at(TokenKind::LBracket);
        if !bare {
            self.delimited(
                TokenKind::LBracket,
                TokenKind::RBracket,
                Some("expected a generic argument"),
                |p| p.targ(),
            );
        }
        self.b.finish_node();
        bare
    }

    /// Rule 11, type position: chosen by the first token; a bare path that
    /// turns out to be followed by an arithmetic operator becomes the
    /// first operand of the constant expression (a relabel of the built
    /// node, not a re-parse).
    fn targ(&mut self) {
        use TokenKind::*;
        match self.cur() {
            Int | Float | Str | MultilineStr | KwTrue | KwFalse | Minus => {
                self.add_expr(false);
            }
            Ident => {
                if !self.enter() {
                    return;
                }
                if self.type_app() && (is_mul_op(self.cur()) || is_add_op(self.cur())) {
                    self.b.set_last_kind(NodeKind::NameExpr);
                    self.mul_tail(false);
                    self.add_tail(false);
                }
                self.leave();
            }
            _ => self.type_(false),
        }
    }

    // ================= statements =================

    fn block(&mut self) {
        use TokenKind::*;
        if !self.at(LBrace) {
            self.err_here(DiagCode::Expected, "expected '{'");
            self.b.empty_node(NodeKind::Error);
            return;
        }
        if !self.enter() {
            return;
        }
        self.b.start_node(NodeKind::Block);
        let (os, oe) = self.cur_range();
        self.bump();
        while !self.at(RBrace) && !self.at(Eof) && !self.at_decl_sync() {
            let before = self.p;
            self.stmt();
            self.guard_progress(before);
        }
        self.close(os, oe, RBrace);
        self.b.finish_node();
        self.leave();
    }

    fn binding(&mut self) {
        use TokenKind::*;
        match self.cur() {
            Ident | Underscore => {
                self.b.start_node(NodeKind::Binding);
                self.bump();
                self.b.finish_node();
            }
            LParen => {
                if !self.enter() {
                    return;
                }
                self.b.start_node(NodeKind::TupleBinding);
                self.delimited(LParen, RParen, None, |p| p.binding());
                self.b.finish_node();
                self.leave();
            }
            _ => {
                self.err_here(
                    DiagCode::Expected,
                    "expected a binding (a name, '_' or a tuple of bindings)",
                );
                self.b.empty_node(NodeKind::Error);
            }
        }
    }

    fn for_head(&mut self) {
        self.binding();
        self.expect(TokenKind::KwIn, "expected 'in' after the loop binding");
        self.expr(true);
    }

    fn stmt(&mut self) {
        use TokenKind::*;
        match self.cur() {
            KwLet | KwVar => {
                self.b.start_node(NodeKind::LetStmt);
                self.bump();
                self.binding();
                if self.opt(Colon) {
                    self.type_(false);
                }
                if self.opt(Eq) {
                    self.expr(false);
                }
                self.expect_semi();
                self.b.finish_node();
            }
            // statement form: ends at its `}`, never continued by an operator
            KwIf => self.if_expr(),
            KwMatch => self.match_expr(),
            KwComptime => self.comptime_block(),
            KwFor => {
                self.b.start_node(NodeKind::ForStmt);
                self.bump();
                self.for_head();
                self.block();
                self.b.finish_node();
            }
            KwWhile => {
                self.b.start_node(NodeKind::WhileStmt);
                self.bump();
                self.expr(true);
                self.block();
                self.b.finish_node();
            }
            KwBreak | KwContinue => {
                self.b.start_node(if self.at(KwBreak) {
                    NodeKind::BreakStmt
                } else {
                    NodeKind::ContinueStmt
                });
                self.bump();
                self.expect_semi();
                self.b.finish_node();
            }
            KwReturn => {
                self.b.start_node(NodeKind::ReturnStmt);
                self.bump();
                if !matches!(self.cur(), Semi | RBrace | Eof) {
                    self.expr(false);
                }
                self.expect_semi();
                self.b.finish_node();
            }
            KwRaise | KwSpawn => {
                self.b.start_node(if self.at(KwRaise) {
                    NodeKind::RaiseStmt
                } else {
                    NodeKind::SpawnStmt
                });
                self.bump();
                self.expr(false);
                self.expect_semi();
                self.b.finish_node();
            }
            KwWith => {
                self.b.start_node(NodeKind::WithStmt);
                self.bump();
                if self.is_word(b"arena") || self.is_word(b"allocator") {
                    self.bump();
                } else {
                    self.err_here(
                        DiagCode::Expected,
                        "expected 'arena' or 'allocator' after 'with'",
                    );
                    if self.at(Ident) && self.nth(1) == Ident {
                        self.bump();
                    }
                }
                self.expect(Ident, "expected a name for the region");
                self.expect(Colon, "expected ':' and the region's type");
                self.type_(false);
                self.block();
                self.b.finish_node();
            }
            KwParallel => {
                self.b.start_node(NodeKind::ParallelStmt);
                self.bump();
                if self.opt(KwFor) {
                    self.b.set_current_kind(NodeKind::ParallelForStmt);
                    self.for_head();
                    if self.is_word(b"grain") {
                        self.bump();
                        self.expr(true);
                    }
                }
                self.block();
                self.b.finish_node();
            }
            KwSimd => {
                self.b.start_node(NodeKind::SimdForStmt);
                self.bump();
                self.expect(KwFor, "expected 'for' after 'simd'");
                self.for_head();
                self.block();
                self.b.finish_node();
            }
            KwConsume | KwDiscard => {
                self.b.start_node(if self.at(KwConsume) {
                    NodeKind::ConsumeStmt
                } else {
                    NodeKind::DiscardStmt
                });
                self.bump();
                self.place();
                self.expect_semi();
                self.b.finish_node();
            }
            KwDefer | KwErrdefer => {
                // ch07 `defer_stmt` / `errdefer_stmt`, Disambiguation 9:
                // the keyword selects the statement (LA 1) and the token
                // after it selects the body (LA 1) — `{` is a `block`, and
                // anything else begins an `expr` that ends at its `;`.
                self.b.start_node(if self.at(KwDefer) {
                    NodeKind::DeferStmt
                } else {
                    NodeKind::ErrdeferStmt
                });
                self.bump();
                if self.at(LBrace) {
                    self.block();
                } else {
                    self.expr(false);
                    self.expect_semi();
                }
                self.b.finish_node();
            }
            At => {
                self.b.start_node(NodeKind::AttrBlockStmt);
                self.attribute();
                self.block();
                self.b.finish_node();
            }
            LBrace => self.block(),
            _ => {
                // Rule 9: parse one `expr`; the following token decides.
                let is_place = self.expr(false);
                if is_assign_op(self.cur()) {
                    if !is_place {
                        self.err_here(
                            DiagCode::AssignTargetNotPlace,
                            "the left side of an assignment must be a place (name, field or index)",
                        );
                    }
                    self.b.wrap_last_sibling(NodeKind::AssignStmt);
                    self.bump();
                    self.expr(false);
                    self.expect_semi();
                    self.b.finish_node();
                } else if !self.at(RBrace) {
                    self.b.wrap_last_sibling(NodeKind::ExprStmt);
                    self.expect_semi();
                    self.b.finish_node();
                }
                // else: the block's tail value, left as the bare expression
            }
        }
    }

    /// `ident { "." ident | bracket }`, built with the expression kinds
    /// (`NameExpr`, `FieldExpr`, `Bracket`).
    fn place(&mut self) {
        use TokenKind::*;
        if !self.at(Ident) {
            self.err_here(
                DiagCode::Expected,
                "expected a place (name, field or index)",
            );
            self.b.empty_node(NodeKind::Error);
            return;
        }
        self.path(NodeKind::NameExpr);
        let mut chain = 0u32;
        loop {
            match self.cur() {
                Dot => {
                    self.b.wrap_last_sibling(NodeKind::FieldExpr);
                    self.bump();
                    self.expect(Ident, "expected field name");
                    self.b.finish_node();
                }
                LBracket => self.bracket(),
                _ => break,
            }
            chain += 1;
            if chain >= MAX_POSTFIX_CHAIN {
                break;
            }
        }
    }

    // ================= expressions =================

    fn expr(&mut self, ns: bool) -> bool {
        let mut is_place = self.and_expr(ns);
        if self.at(TokenKind::KwOr) {
            self.b.wrap_last_sibling(NodeKind::OrExpr);
            while self.opt(TokenKind::KwOr) {
                self.and_expr(ns);
            }
            self.b.finish_node();
            is_place = false;
        }
        is_place
    }

    fn and_expr(&mut self, ns: bool) -> bool {
        let mut is_place = self.not_expr(ns);
        if self.at(TokenKind::KwAnd) {
            self.b.wrap_last_sibling(NodeKind::AndExpr);
            while self.opt(TokenKind::KwAnd) {
                self.not_expr(ns);
            }
            self.b.finish_node();
            is_place = false;
        }
        is_place
    }

    fn not_expr(&mut self, ns: bool) -> bool {
        if !self.at(TokenKind::KwNot) {
            return self.cmp_expr(ns);
        }
        if !self.enter() {
            return false;
        }
        self.b.start_node(NodeKind::NotExpr);
        self.bump();
        self.not_expr(ns);
        self.b.finish_node();
        self.leave();
        false
    }

    /// `cmp_expr = bit_expr | range_expr [ cmp_op range_expr ]` (rule 12).
    fn cmp_expr(&mut self, ns: bool) -> bool {
        let (is_place, bitwise) = self.range_or_bit(ns, true);
        if bitwise {
            return false;
        }
        let k = self.cur();
        if is_cmp_op(k) {
            self.b.wrap_last_sibling(NodeKind::CmpExpr);
            self.bump();
            self.range_or_bit(ns, false);
            if is_cmp_op(self.cur()) {
                self.err_here(
                    DiagCode::ComparisonChained,
                    "comparison operators do not chain; parenthesize",
                );
                self.eat_operator_tail(ns);
            }
            self.b.finish_node();
            false
        } else if is_bit_op(k) {
            // `a + b & c`, `a ..< b | c`
            self.b.wrap_last_sibling(NodeKind::Error);
            self.mix_error(ns);
            self.b.finish_node();
            false
        } else {
            is_place
        }
    }

    fn mix_error(&mut self, ns: bool) {
        self.err_here(
            DiagCode::BitwiseNeedsParens,
            "a bitwise operator cannot be mixed with arithmetic, range, comparison or a different bitwise operator; parenthesize",
        );
        self.eat_operator_tail(ns);
    }

    /// After a precedence diagnostic: consume the rest of the operator
    /// chain into the open node so the error does not cascade.
    fn eat_operator_tail(&mut self, ns: bool) {
        while is_binop(self.cur()) {
            self.bump();
            self.cast_expr(ns);
        }
    }

    /// Both alternatives of `cmp_expr` start with a `cast_expr`: parse one,
    /// then a bitwise operator selects `bit_expr`, anything else continues
    /// `mul_expr`/`add_expr`/`range_expr`. Returns `(is_place, was_bitwise)`.
    fn range_or_bit(&mut self, ns: bool, allow_bit: bool) -> (bool, bool) {
        use TokenKind::*;
        let mut is_place = self.cast_expr(ns);
        let op = self.cur();
        if is_bit_op(op) {
            if !allow_bit {
                self.mix_error(ns); // `a == b & c`
                return (false, false);
            }
            self.b.wrap_last_sibling(NodeKind::BitExpr);
            if matches!(op, Shl | Shr) {
                self.bump();
                self.cast_expr(ns);
            } else {
                while self.at(op) {
                    self.bump();
                    self.cast_expr(ns);
                }
            }
            if is_binop(self.cur()) {
                self.mix_error(ns);
            }
            self.b.finish_node();
            return (false, true);
        }
        let mul = self.mul_tail(ns);
        let add = self.add_tail(ns);
        is_place = is_place && !mul && !add;
        if is_range_op(self.cur()) {
            self.b.wrap_last_sibling(NodeKind::RangeExpr);
            self.bump();
            self.add_expr(ns);
            if is_range_op(self.cur()) {
                self.err_here(
                    DiagCode::RangeChained,
                    "range operators do not chain; parenthesize",
                );
                self.eat_operator_tail(ns);
            }
            self.b.finish_node();
            is_place = false;
        }
        (is_place, false)
    }

    /// Continues a `mul_expr` whose first operand is the last finished node.
    fn mul_tail(&mut self, ns: bool) -> bool {
        if !is_mul_op(self.cur()) {
            return false;
        }
        self.b.wrap_last_sibling(NodeKind::MulExpr);
        while is_mul_op(self.cur()) {
            self.bump();
            self.cast_expr(ns);
        }
        self.b.finish_node();
        true
    }

    fn add_tail(&mut self, ns: bool) -> bool {
        if !is_add_op(self.cur()) {
            return false;
        }
        self.b.wrap_last_sibling(NodeKind::AddExpr);
        while is_add_op(self.cur()) {
            self.bump();
            self.cast_expr(ns);
            self.mul_tail(ns);
        }
        self.b.finish_node();
        true
    }

    fn add_expr(&mut self, ns: bool) {
        self.cast_expr(ns);
        self.mul_tail(ns);
        self.add_tail(ns);
    }

    fn cast_expr(&mut self, ns: bool) -> bool {
        let mut is_place = self.unary_expr(ns);
        if self.at(TokenKind::KwAs) {
            self.b.wrap_last_sibling(NodeKind::CastExpr);
            while self.opt(TokenKind::KwAs) {
                self.type_(false);
            }
            self.b.finish_node();
            is_place = false;
        }
        is_place
    }

    fn unary_expr(&mut self, ns: bool) -> bool {
        if !matches!(self.cur(), TokenKind::Minus | TokenKind::KwMove) {
            return self.postfix_expr(ns);
        }
        if !self.enter() {
            return false;
        }
        self.b.start_node(NodeKind::UnaryExpr);
        self.bump();
        self.unary_expr(ns);
        self.b.finish_node();
        self.leave();
        false
    }

    fn postfix_expr(&mut self, ns: bool) -> bool {
        use TokenKind::*;
        let mut is_place = self.primary_expr(ns);
        // `struct_lit = path [bracket] "{"`: only a bare path, or a bare
        // path with exactly one bracket, can take a `{`.
        let mut is_bare_path = is_place;
        let mut chain = 0u32;
        loop {
            match self.cur() {
                Question => {
                    self.b.wrap_last_sibling(NodeKind::TryExpr);
                    self.bump();
                    self.b.finish_node();
                    is_place = false;
                }
                Dot => {
                    self.b.wrap_last_sibling(NodeKind::FieldExpr);
                    self.bump();
                    self.expect(Ident, "expected field or method name after '.'");
                    self.b.finish_node();
                }
                LParen => {
                    self.b.wrap_last_sibling(NodeKind::CallExpr);
                    if self.enter() {
                        self.delimited(LParen, RParen, None, |p| p.arg());
                        self.leave();
                    }
                    // rule 3: a handler exists only directly after a call's `)`
                    if self.at(KwElse) && self.nth(1) == Pipe {
                        self.b.start_node(NodeKind::Handler);
                        self.bump();
                        self.bump();
                        self.expect(Ident, "expected the handler's error binding");
                        self.expect(Pipe, "expected '|'");
                        self.block();
                        self.b.finish_node();
                    }
                    self.b.finish_node();
                    is_place = false;
                }
                LBracket => {
                    self.bracket();
                    if is_bare_path && !ns && self.at(LBrace) {
                        self.struct_lit_tail();
                        is_place = false;
                    }
                }
                _ => break,
            }
            is_bare_path = false;
            chain += 1;
            if chain >= MAX_POSTFIX_CHAIN {
                if is_opener(self.cur()) || matches!(self.cur(), Question | Dot) {
                    self.err_here(DiagCode::NestingTooDeep, "postfix chain too long");
                }
                break;
            }
        }
        is_place
    }

    /// Wraps the last finished node in a `Bracket` (rule 11, expression
    /// position: an argument is a type only when it starts with a reserved
    /// type keyword).
    fn bracket(&mut self) {
        use TokenKind::*;
        self.b.wrap_last_sibling(NodeKind::Bracket);
        if self.enter() {
            self.delimited(LBracket, RBracket, None, |p| {
                if matches!(p.cur(), KwIso | KwImm | KwSecret | KwFn | KwDyn) {
                    p.type_(false);
                } else {
                    p.expr(false);
                }
            });
            self.leave();
        }
        self.b.finish_node();
    }

    fn struct_lit_tail(&mut self) {
        self.b.wrap_last_sibling(NodeKind::StructLit);
        if self.enter() {
            self.delimited(TokenKind::LBrace, TokenKind::RBrace, None, |p| {
                p.b.start_node(NodeKind::FInit);
                p.expect(TokenKind::Ident, "expected field name");
                p.expect(TokenKind::Colon, "expected ':' and the field's value");
                p.expr(false);
                p.b.finish_node();
            });
            self.leave();
        }
        self.b.finish_node();
    }

    fn arg(&mut self) {
        use TokenKind::*;
        let named = self.at(Ident) && self.nth(1) == Colon;
        if named {
            self.b.start_node(NodeKind::NamedArg);
            self.bump();
            self.bump();
        }
        let k = self.cur();
        let ends = matches!(self.nth(1), Comma | RParen);
        if is_unambiguous_bare_op(k) || (matches!(k, Minus | Pipe | Amp) && ends) {
            self.b.start_node(NodeKind::BareOp);
            self.bump();
            self.b.finish_node();
        } else if k == Amp {
            // rule 4: `&out x` is the set marker; `&out`, `&out.f`,
            // `&out[i]` mark a binding named `out`
            self.b.start_node(NodeKind::InoutArg);
            self.bump();
            if self.nth(1) == Ident && self.is_word(b"out") {
                self.b.set_current_kind(NodeKind::SetArg);
                self.bump();
            }
            self.place();
            self.b.finish_node();
        } else {
            self.expr(false);
        }
        if named {
            self.b.finish_node();
        }
    }

    fn primary_expr(&mut self, ns: bool) -> bool {
        use TokenKind::*;
        if self.literal() {
            return false;
        }
        match self.cur() {
            Ident => {
                self.path(NodeKind::NameExpr);
                if self.at(LBrace) {
                    if !ns {
                        self.struct_lit_tail();
                        return false;
                    }
                    // Rule 1 decided `{` opens the block. `{ ident :` starts no
                    // statement (only a struct's field list, after its
                    // `invariant`s), so this is an error either way; the deeper
                    // peek only picks the better diagnostic and recovery.
                    if !self.in_struct_header && self.nth(1) == Ident && self.nth(2) == Colon {
                        self.err_here(
                            DiagCode::Expected,
                            "a struct literal here must be parenthesized",
                        );
                        self.struct_lit_tail();
                        return false;
                    }
                }
                return true;
            }
            LParen | LBracket | Pipe | KwIf | KwMatch | KwComptime | KwAsm => {}
            KwNot => {
                self.err_here(
                    DiagCode::Expected,
                    "'not' binds looser than this operator; parenthesize the 'not' expression",
                );
                self.not_expr(ns);
                return false;
            }
            Amp => {
                self.err_here(
                    DiagCode::Expected,
                    "'&' is only an argument marker (f(&x)), not an expression operator",
                );
                if self.enter() {
                    self.b.start_node(NodeKind::Error);
                    self.bump();
                    self.unary_expr(ns);
                    self.b.finish_node();
                    self.leave();
                }
                return false;
            }
            Dot if matches!(self.nth(1), Int | Float) => {
                self.err_here(
                    DiagCode::Expected,
                    "a number literal cannot start with '.'; write '0.5'",
                );
                self.b.start_node(NodeKind::Error);
                self.bump();
                self.bump();
                self.b.finish_node();
                return false;
            }
            _ => {
                self.err_here(DiagCode::Expected, "expected an expression");
                self.error_node();
                return false;
            }
        }
        if !self.enter() {
            return false;
        }
        match self.cur() {
            LParen => {
                self.b.start_node(NodeKind::TupleOrParen);
                self.delimited(LParen, RParen, None, |p| {
                    p.expr(false);
                });
                self.b.finish_node();
            }
            LBracket => {
                let (os, oe) = self.cur_range();
                self.b.start_node(NodeKind::ArrayLit);
                self.bump();
                if !self.at(RBracket) {
                    self.expr(false);
                    if self.opt(Semi) {
                        self.expr(false);
                    } else {
                        while self.opt(Comma) && !self.at(RBracket) {
                            self.expr(false);
                        }
                    }
                }
                self.close(os, oe, RBracket);
                self.b.finish_node();
            }
            Pipe => {
                self.b.start_node(NodeKind::Closure);
                self.delimited(Pipe, Pipe, None, |p| p.cparam());
                // rule 2: `{` is a block (no expression starts with `{`)
                if self.at(LBrace) {
                    self.block();
                } else {
                    self.expr(ns);
                }
                self.b.finish_node();
            }
            KwIf => self.if_expr(),
            KwMatch => self.match_expr(),
            KwAsm => self.asm_expr(),
            _ => self.comptime_block(),
        }
        self.leave();
        false
    }

    /// At `asm`. Rule 2-4: `"asm" "(" IDENT ")" "{" asm_item { "," asm_item }
    /// [ "," ] "}"`, at least one `STRING` item required.
    fn asm_expr(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::AsmExpr);
        self.bump(); // asm
        self.expect(LParen, "expected '(' after 'asm'");
        self.expect(Ident, "expected an architecture name");
        self.expect(RParen, "expected ')'");
        let (os, oe) = self.cur_range();
        let mut has_string = false;
        self.delimited(LBrace, RBrace, Some("expected an asm item"), |p| {
            if p.asm_item() {
                has_string = true;
            }
        });
        if !has_string {
            self.err_at(
                os,
                oe,
                DiagCode::Expected,
                "an 'asm' block needs at least one string instruction",
            );
        }
        self.b.finish_node();
    }

    /// One `asm_item`. Returns whether it was a bare `STRING`.
    fn asm_item(&mut self) -> bool {
        use TokenKind::*;
        self.b.start_node(NodeKind::AsmItem);
        let is_string = match self.cur() {
            Str | MultilineStr => {
                self.bump();
                true
            }
            KwIn => {
                self.bump();
                self.expect(LParen, "expected '('");
                self.expect(Ident, "expected a register name");
                self.expect(RParen, "expected ')'");
                self.expect(Eq, "expected '='");
                self.expr(false);
                false
            }
            _ if self.is_word(b"out") => {
                self.bump();
                self.expect(LParen, "expected '('");
                self.expect(Ident, "expected a register name");
                self.expect(RParen, "expected ')'");
                false
            }
            _ if self.is_word(b"clobber") => {
                self.bump();
                self.delimited(LParen, RParen, Some("expected a register name"), |p| {
                    p.expect(Ident, "expected a register name");
                });
                false
            }
            _ => {
                self.err_here(
                    DiagCode::Expected,
                    "expected 'in', 'out', 'clobber', or a string",
                );
                self.error_node();
                false
            }
        };
        self.b.finish_node();
        is_string
    }

    fn cparam(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::CParam);
        if matches!(self.cur(), KwLet | KwInout | KwSink)
            || (matches!(self.nth(1), Ident | Underscore) && self.is_word(b"set"))
        {
            self.bump();
        }
        if matches!(self.cur(), Ident | Underscore) {
            self.bump();
        } else {
            self.err_here(DiagCode::Expected, "expected a closure parameter name");
        }
        if self.opt(Colon) {
            self.type_(false);
        }
        self.b.finish_node();
    }

    fn comptime_block(&mut self) {
        self.b.start_node(NodeKind::ComptimeBlock);
        self.bump();
        self.block();
        self.b.finish_node();
    }

    /// At `if`. The `else if` chain is one flat node (see `NodeKind::IfExpr`).
    fn if_expr(&mut self) {
        self.b.start_node(NodeKind::IfExpr);
        loop {
            self.bump(); // if
            self.expr(true);
            self.block();
            if !self.opt(TokenKind::KwElse) {
                break;
            }
            if !self.at(TokenKind::KwIf) {
                self.block();
                break;
            }
        }
        self.b.finish_node();
    }

    fn match_expr(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::MatchExpr);
        self.bump(); // match
        self.expr(true);
        let (os, oe) = self.cur_range();
        if self.expect(LBrace, "expected '{' and the match arms") {
            while !self.at(RBrace) && !self.at(Eof) && !self.at_decl_sync() {
                let before = self.p;
                self.arm();
                self.guard_progress(before);
            }
            self.close(os, oe, RBrace);
        }
        self.b.finish_node();
    }

    fn arm(&mut self) {
        use TokenKind::*;
        self.b.start_node(NodeKind::Arm);
        self.pattern();
        if !self.expect(FatArrow, "expected '=>' after the pattern") {
            // resynchronise on the arm boundary
            self.b.start_node(NodeKind::Error);
            let mut depth = 0u32;
            while !self.at(Eof) && !self.at_decl_sync() {
                let k = self.cur();
                if depth == 0 && matches!(k, Comma | RBrace | Semi) {
                    break;
                }
                if is_opener(k) {
                    depth += 1;
                } else if is_closer(k) {
                    depth = depth.saturating_sub(1);
                }
                self.bump();
            }
            self.b.finish_node();
            self.opt(Comma);
        } else if self.at(LBrace) {
            self.block();
            self.opt(Comma);
        } else {
            self.expr(false);
            if !self.opt(Comma) && !self.at(RBrace) {
                self.err_here(DiagCode::Expected, "expected ',' after the match arm");
            }
        }
        self.b.finish_node();
    }

    fn pattern(&mut self) {
        use TokenKind::*;
        match self.cur() {
            KwLet => {
                // "let" ident: the only way a pattern binds (ch07 grammar,
                // ch08 R25 -- owner decision 2026-09-19, round 3, D1).
                self.b.start_node(NodeKind::PatLet);
                self.bump();
                self.expect(Ident, "expected an identifier after 'let'");
                self.b.finish_node();
            }
            Underscore => {
                self.b.start_node(NodeKind::PatWild);
                self.bump();
                self.b.finish_node();
            }
            Int | Float | Str | MultilineStr | KwTrue | KwFalse => {
                self.b.start_node(NodeKind::PatLit);
                self.bump();
                self.b.finish_node();
            }
            Minus if matches!(self.nth(1), Int | Float) => {
                self.b.start_node(NodeKind::PatLit);
                self.bump();
                self.bump();
                self.b.finish_node();
            }
            Dot | Ident => {
                if self.at(Dot) {
                    self.b.start_node(NodeKind::PatDot);
                    self.bump();
                    self.expect(Ident, "expected a variant name after '.'");
                } else {
                    self.b.start_node(NodeKind::PatPath);
                    self.path_tokens();
                }
                if matches!(self.cur(), LParen | LBrace) && self.enter() {
                    self.b.start_node(NodeKind::Payload);
                    if self.at(LParen) {
                        self.delimited(
                            LParen,
                            RParen,
                            Some("expected at least one pattern"),
                            |p| p.pattern(),
                        );
                    } else {
                        self.delimited(
                            LBrace,
                            RBrace,
                            Some("expected at least one field pattern"),
                            |p| {
                                p.b.start_node(NodeKind::FPat);
                                if p.at(KwLet) {
                                    // "let" ident: binds the field and its name
                                    // together (D1). Shorthand for `x: (let x)`.
                                    p.bump();
                                    p.expect(Ident, "expected an identifier after 'let'");
                                } else {
                                    let name_range = p.cur_range();
                                    p.expect(Ident, "expected field name");
                                    if p.opt(Colon) {
                                        p.pattern();
                                    } else {
                                        // The bare `ident` shorthand is removed
                                        // (round 3, D1): a bare field name no
                                        // longer binds. Reported at the
                                        // identifier, per ch07 Error recovery.
                                        p.err_at(
                                            name_range.0,
                                            name_range.1,
                                            DiagCode::Expected,
                                            "write \"let x\" to bind the field or \"x: pattern\"",
                                        );
                                    }
                                }
                                p.b.finish_node();
                            },
                        );
                    }
                    self.b.finish_node();
                    self.leave();
                }
                self.b.finish_node();
            }
            LParen => {
                if !self.enter() {
                    return;
                }
                self.b.start_node(NodeKind::PatTuple);
                self.delimited(LParen, RParen, None, |p| p.pattern());
                self.b.finish_node();
                self.leave();
            }
            _ => {
                self.err_here(DiagCode::Expected, "expected a pattern");
                self.error_node();
            }
        }
    }
}
