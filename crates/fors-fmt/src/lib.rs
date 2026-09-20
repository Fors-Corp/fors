//! `fors-fmt`: the canonical Fors formatter.
//!
//! Std only, no external crates. One parse, one pre-order walk that lowers
//! the lossless CST to a flat op stream ([`doc::Op`]), one measuring pass
//! and one rendering pass. No `HashMap` anywhere on the output path, no
//! per-node heap allocation, no dependence on file order or timing: the
//! same bytes in always give the same bytes out.
//!
//! # The style specification
//!
//! There are no options. Fors code looks like this everywhere, forever.
//! Where a rule had to be chosen, it was chosen for SMALL DIFFS and easy
//! review, not for density.
//!
//! **Indentation and width.** Four spaces per level (never tabs), a
//! 100-column target. The margin is a budget for deciding breaks, not a
//! hard cap: a single long token (a string, a path) may pass it, and so
//! may a line whose last token is forced tight by the token-gluing guard.
//! A line of exactly 100 columns fits; 101 breaks.
//!
//! **Line endings are LF.** A CRLF file is converted; the lexer treats
//! `\r` as whitespace, so that is a whitespace-only change like every
//! other. A lone `\r` that does not precede a newline is left alone.
//!
//! **The formatter is whitespace-only.** It never adds, removes, reorders
//! or rewrites a token — not a trailing comma, not a redundant paren, not
//! a `use` item's position. That is what makes the losslessness and
//! diagnostic-neutrality properties checkable by token equality, and it is
//! why `use` headers are NOT sorted (sorting is a lint's job, not a
//! formatter's). A comma the author already wrote before a closing
//! delimiter is honoured as a "magic trailing comma": that list is then
//! always broken one item per line.
//!
//! **Lists** (parameters, generics, arguments, tuples, array literals,
//! struct-literal fields, struct fields, enum variants, `needs`/`inputs`
//! items, `use` items, patterns, asm items) print on one line while they
//! fit; otherwise every item goes on its own line, indented one level,
//! with the closing delimiter back at the opening line's indent. Brace
//! lists are padded (`Point { x: 1 }`), paren and bracket lists are not
//! (`f(a, b)`, `Vec[i32, A]`). An empty pair is always tight: `{}`, `()`,
//! `[]`.
//!
//! **Blocks always break.** A `{ ... }` with any content puts one
//! statement per line, even when it would fit — including `if`/`else` and
//! `match` arm bodies. Predictability beats density: a statement never
//! changes shape because a neighbour grew.
//!
//! **Signatures.** `fn name[generics](params) -> ret raises E` on one line
//! while it fits, and then `{` at the end of that line. When it does not
//! fit, the innermost thing that can absorb the overflow breaks first: the
//! parameter list goes one parameter per line and the `{` still follows
//! the closing `)`. Only when a clause AFTER the parameters has to move —
//! `raises`, or any contract — does that clause take its own continuation
//! line (indented one level) and the `{` drop to its own line at the
//! declaration's indent, which is what then separates the body from the
//! continuation lines. Generic entries with bounds
//! (`T: Copyable + Show`) and constraint entries (`T.Item: Show`) are
//! ordinary items of the generics list. A `scoped(p)` return type stays
//! tight (`-> scoped(self) Slice[T]`).
//!
//! **Contracts always own their line.** Every `pre`/`post`/`invariant`
//! clause of a function or struct is printed on its own line, indented one
//! level under the signature, however short it is — a contract is
//! semantics, not decoration, and adding one must not reflow the line
//! above it. A declaration with contracts therefore always has its `{` on
//! its own line.
//!
//! **Method chains.** Round 6 made `it.map(f).filter(g).fold(0, h)`
//! idiomatic, so a chain is one group: it stays on one line while it fits,
//! and otherwise breaks ONE CALL PER LINE with the dot leading the line,
//! indented one level. It is never filled to the margin — filling makes
//! the diff of an inserted adaptor touch every following line, while
//! one-per-line touches exactly one. The head (the receiver together with
//! its first call, e.g. `it.map(f)`) stays on the opening line: the CST
//! parses `it.map` as a single greedy `NameExpr` leaf, so the first dot is
//! not a node boundary, and pretending otherwise would mean splitting a
//! leaf's tokens for no gain in readability.
//!
//! **Operators.** Binary operators are spaced (`a + b`, `x as i64`,
//! `a and b`) and a long expression breaks BEFORE the operator, indented
//! one level, so the operator starts the continuation line. Ranges are
//! tight (`0..<n`). Prefix `-` is tight (`-x`), `not` and `move` are
//! spaced. `?`, `.field`, call and index parens bind tight. `&p` and
//! `&out p` bind tight to the place.
//!
//! **Match arms.** `pattern => expr,` on one line; when the body does not
//! fit it moves to the next line, indented one level. A block body opens
//! on the arm's line (`pattern => {`).
//!
//! **Closures.** `|a, b| body`, pipes hugging the parameters. A call
//! whose ONLY argument is a closure with a block body hugs it:
//! `v.each(|x| {` on the call's line, the block's statements indented one
//! level, `});` back at the call's indent. With any other argument
//! beside it — or a trailing comma after it — the argument list breaks
//! like any list, one argument per line.
//!
//! **Attributes.** One per line above the declaration they decorate. An
//! attribute-block statement keeps its block on the attribute's line
//! (`@unsafe {`).
//!
//! **Comments.** A comment that shares a line with the code before it
//! stays there, one space after it; a block comment is also followed by
//! one space (`x /*c*/ : T`, `f( /* none */ )`). Every other comment keeps
//! its own line, at the indent of the construct it precedes (a comment
//! before `}` sits at the body's indent, not the brace's), and forces the
//! construct around it to break. A same-line comment that a break pushes
//! to the start of the next line then owns that line, as it would on the
//! next pass. Blank lines around a comment are the author's and
//! are kept (collapsed to one), even where the blank line directly after
//! an opening brace would have been dropped. Block comments are emitted verbatim, never
//! re-indented inside, because their content is not the formatter's to
//! rewrite. Doc-style `//!` and `//` headers are ordinary line comments
//! and keep their position and order.
//!
//! **Blank lines.** A run of blank lines anywhere an item can start (top
//! level, between statements, between list items) collapses to exactly
//! one and is otherwise preserved; blank lines are removed directly after
//! an opening brace, directly before a closing one, and at the start of
//! the file. A preserved blank inside a list forces that list to break. A
//! non-empty file ends with exactly one newline, and no line ever has
//! trailing whitespace.
//!
//! # Properties
//!
//! Every `format_source` result is self-verified before it is returned:
//! the output is re-lexed and its significant tokens (kind AND text) must
//! equal the input's, with every comment present exactly once. If that
//! check ever fails, or if the input does not parse, the ORIGINAL bytes
//! are returned with a [`Status`] saying why. A formatter that mangles a
//! file is worse than one that declines it.
//!
//! `tests/corpus.rs` proves losslessness, idempotence, diagnostic
//! neutrality, parse-error tolerance and determinism over every corpus
//! and std file, and again over four whitespace/comment perturbations of
//! each; `tests/attacks.rs` pins the shapes above on inputs the corpus
//! lacks, including a 1 MB file.

pub mod diff;
pub mod doc;
mod emit;

pub use diff::{TextEdit, diff as text_diff, render_diff};
pub use doc::{INDENT, MARGIN};

use fors_lex::TokenKind;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Status {
    /// The buffer was formatted and the result verified.
    Formatted,
    /// The buffer does not parse (or does not lex); it was returned
    /// unchanged. The corpus's deliberate parse-error files land here.
    ParseFailed,
    /// The formatter produced output that would not have re-lexed to the
    /// same tokens, so it declined: the buffer was returned unchanged.
    /// This must never happen; it is a bug, and the corpus test asserts it.
    Bailed,
}

pub struct Formatted {
    pub text: Vec<u8>,
    pub status: Status,
    pub changed: bool,
    /// Parse diagnostics of the INPUT (0 unless `status` is `ParseFailed`).
    pub parse_diagnostics: usize,
}

impl Formatted {
    pub fn is_ok(&self) -> bool {
        self.status == Status::Formatted
    }
}

/// `CRLF` -> `LF`, in place. The lexer treats `\r` as whitespace, so this
/// is a whitespace-only change like every other the formatter makes — but
/// it is done BEFORE lexing, because a `\r` before the newline that ends a
/// line comment is part of the comment token's text, and the only other
/// way to drop it would be to rewrite a token.
fn normalise_newlines(src: &[u8]) -> std::borrow::Cow<'_, [u8]> {
    if !src.contains(&b'\r') {
        return std::borrow::Cow::Borrowed(src);
    }
    let mut v = Vec::with_capacity(src.len());
    let mut i = 0;
    while i < src.len() {
        if src[i] == b'\r' && src.get(i + 1) == Some(&b'\n') {
            i += 1;
            continue;
        }
        v.push(src[i]);
        i += 1;
    }
    std::borrow::Cow::Owned(v)
}

/// Formats a whole source buffer.
///
/// MARC: a file with CRLF line endings is formatted with LF line endings.
/// The canonical form has one line terminator, and converting is a
/// whitespace-only change (see [`normalise_newlines`]); a lone `\r` that
/// does not precede `\n` is left where it is. The token check runs against
/// the normalised input, so `same_tokens` also compares modulo CRLF.
pub fn format_source(src: &[u8]) -> Formatted {
    let parse = fors_syntax::parse_file(src);
    if !parse.diags.is_empty() {
        return Formatted {
            text: src.to_vec(),
            status: Status::ParseFailed,
            changed: false,
            parse_diagnostics: parse.diags.len(),
        };
    }
    let lf = normalise_newlines(src);
    let parse = match lf {
        std::borrow::Cow::Borrowed(_) => parse,
        std::borrow::Cow::Owned(_) => fors_syntax::parse_file(&lf),
    };
    let src = &lf[..];
    let mut em = emit::Emitter::new(src, &parse.tokens, &parse.tree);
    em.run();
    let out = doc::render(&em.ops, src);
    if !same_tokens(src, &out) {
        return Formatted {
            text: src.to_vec(),
            status: Status::Bailed,
            changed: false,
            parse_diagnostics: 0,
        };
    }
    let changed = out != src || matches!(lf, std::borrow::Cow::Owned(_));
    Formatted { text: out, status: Status::Formatted, changed, parse_diagnostics: 0 }
}

/// Whether two buffers carry exactly the same tokens: the same significant
/// tokens in the same order with the same text, and the same comments in
/// the same order with the same text. Only whitespace may differ (and a
/// CRLF on one side matches an LF on the other). This is the losslessness
/// property, and `format_source` checks it on itself.
pub fn same_tokens(a: &[u8], b: &[u8]) -> bool {
    let a = normalise_newlines(a);
    let b = normalise_newlines(b);
    let (a, b) = (&a[..], &b[..]);
    let (ta, _) = fors_lex::lex(a);
    let (tb, _) = fors_lex::lex(b);
    let mut ia = 0usize;
    let mut ib = 0usize;
    loop {
        while ia < ta.len() && ta.kinds[ia] == TokenKind::Whitespace {
            ia += 1;
        }
        while ib < tb.len() && tb.kinds[ib] == TokenKind::Whitespace {
            ib += 1;
        }
        match (ia < ta.len(), ib < tb.len()) {
            (false, false) => return true,
            (true, false) | (false, true) => return false,
            (true, true) => {}
        }
        if ta.kinds[ia] != tb.kinds[ib] || ta.text(ia, a) != tb.text(ib, b) {
            return false;
        }
        ia += 1;
        ib += 1;
    }
}

pub struct Check {
    pub formatted: bool,
    pub status: Status,
    /// Empty when `formatted`; otherwise the minimal set of line edits
    /// that turns the input into the canonical form.
    pub edits: Vec<TextEdit>,
}

/// Reports whether a buffer is already in canonical form, with the edits
/// that would fix it. The CI gate ("every .fors file in the repo is
/// formatted") is `check_source(..).formatted` over the tree.
pub fn check_source(src: &[u8]) -> Check {
    let f = format_source(src);
    Check {
        formatted: !f.changed,
        status: f.status,
        edits: if f.changed { diff::diff(src, &f.text) } else { Vec::new() },
    }
}

/// Formats the lines touched by `[start, end)` and returns only the edits
/// inside that span — the LSP's `textDocument/rangeFormatting`.
///
/// MARC: range formatting is whole-buffer formatting with the edits
/// filtered, not a formatter that starts mid-file. Anything else can
/// disagree with `format_source` on the same bytes, and two formatters
/// that disagree are worse than one that is occasionally over-eager.
pub fn format_range(src: &[u8], start: u32, end: u32) -> Check {
    let c = check_source(src);
    let edits = c
        .edits
        .into_iter()
        .filter(|e| e.start < end.max(start + 1) && e.end > start)
        .collect();
    Check { formatted: c.formatted, status: c.status, edits }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(src: &str) -> String {
        let out = format_source(src.as_bytes());
        assert_eq!(out.status, Status::Formatted, "input: {src}");
        String::from_utf8(out.text).unwrap()
    }

    #[test]
    fn empty_stays_empty() {
        assert_eq!(f(""), "");
    }

    #[test]
    fn simple_fn() {
        assert_eq!(f("fn   f( ) {let  x=1+2 ;}"), "fn f() {\n    let x = 1 + 2;\n}\n");
    }

    #[test]
    fn idempotent_on_itself() {
        let once = f("fn f(let x:i32)->i32{return x+1;}");
        assert_eq!(f(&once), once);
    }

    #[test]
    fn magic_trailing_comma_pins_a_list_open() {
        assert_eq!(f("fn f(let a: i32, let b: i32,) {}"), "fn f(\n    let a: i32,\n    let b: i32,\n) {}\n");
        assert_eq!(f("fn f(let a: i32, let b: i32) {}"), "fn f(let a: i32, let b: i32) {}\n");
    }

    #[test]
    fn contracts_own_their_line_and_push_the_brace_down() {
        assert_eq!(
            f("fn f(let i: usize) pre i < 4 { g(); }"),
            "fn f(let i: usize)\n    pre i < 4\n{\n    g();\n}\n"
        );
    }

    #[test]
    fn a_short_chain_stays_on_one_line() {
        let src = "fn f() { let n = v.iter().map(d).count(); }";
        assert!(String::from_utf8(format_source(src.as_bytes()).text).unwrap().contains("v.iter().map(d).count()"));
    }

    #[test]
    fn a_blank_line_inside_a_list_breaks_it() {
        assert_eq!(f("struct S { a: i32,\n\n b: i32 }"), "struct S {\n    a: i32,\n\n    b: i32\n}\n");
    }

    #[test]
    fn tokens_are_never_glued_together() {
        // `not` and a negative literal must keep their space
        let out = f("fn f() { let x = 1 - -2; }");
        assert!(out.contains("1 - -2"), "{out}");
    }

    #[test]
    fn a_multiline_string_keeps_its_own_lines() {
        let out = f(concat!("fn f() { let s = ", r"\\a", "\n    ", r"\\b", "\n; }"));
        assert!(out.contains(r"\\a"), "{out}");
        assert_eq!(format_source(out.as_bytes()).text, out.as_bytes());
    }

    #[test]
    fn parse_error_is_untouched() {
        let src = "fn f( {";
        let out = format_source(src.as_bytes());
        assert_eq!(out.status, Status::ParseFailed);
        assert_eq!(out.text, src.as_bytes());
    }
}
