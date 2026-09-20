//! Token kinds for the Fors lexer (spec ch07 "Lexical Structure and Grammar").
//!
//! Fieldless, `#[repr(u8)]`: a `TokenKind` is one byte, stored in a parallel
//! column (see `Tokens` in `lexer.rs`), never boxed or attached to owned text.
//! Reserved keywords each get their own variant (ch07 "Keywords — reserved");
//! contextual keywords (`contracts`, `needs`, `soa`, `set`, `brand`, `scoped`,
//! `arena`, `allocator`, `pre`, `post`, `invariant`, `grain`, `out`) are never
//! distinguished here — they lex as `Ident` and the parser decides from slot
//! context, per ch07 "Keywords — contextual".

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum TokenKind {
    // ---- trivia (kept in the stream so it stays lossless) ----
    Whitespace,
    LineComment,
    BlockComment,

    // ---- names and literals ----
    Ident,
    Int,
    Float,
    Str,
    /// A `\\`-line-oriented multiline string. Consecutive `\\` lines
    /// separated only by whitespace lex as ONE token; a comment between them
    /// ends the literal (ch07 rule 6).
    MultilineStr,

    // ---- reserved keywords (never identifiers) ----
    KwModule,
    KwUse,
    KwPub,
    KwFn,
    KwStruct,
    KwEnum,
    KwTrait,
    KwImpl,
    KwConst,
    KwExtern,
    KwLet,
    KwVar,
    KwInout,
    KwSink,
    KwIf,
    KwElse,
    KwMatch,
    KwFor,
    KwIn,
    KwWhile,
    KwBreak,
    KwContinue,
    KwReturn,
    KwRaise,
    KwRaises,
    KwWith,
    KwParallel,
    KwSimd,
    KwSpawn,
    KwComptime,
    KwMove,
    KwConsume,
    KwDiscard,
    KwAs,
    KwAnd,
    KwOr,
    KwNot,
    KwTrue,
    KwFalse,
    KwIso,
    KwImm,
    KwSecret,
    KwDyn,
    /// `asm` (ch07 R2-4 / grammar): reserved from v0.1.
    KwAsm,
    /// Reserved, no production yet (ch07 "Reserved without a production").
    KwImport,
    /// Reserved, no production yet (ch07 "Reserved without a production").
    KwRecover,
    /// The single character `_`: its own token, never an `Ident` (ch07 §3).
    Underscore,

    // ---- punctuation and operators (maximal munch) ----
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semi,
    Colon,
    Dot,
    At,
    Question,
    Arrow,   // ->
    FatArrow, // =>
    Eq,
    EqEq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Pipe,
    Caret,
    Shl, // <<
    Shr, // >>
    DotDotLt, // ..<
    DotDotEq, // ..=
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    AmpEq,
    PipeEq,
    CaretEq,
    ShlEq,
    ShrEq,

    /// A lexical error. Its source slice is still present (losslessness
    /// holds), but the text is not a valid token of any other kind; see the
    /// accompanying `Diagnostic` for why.
    Error,
    /// Zero-length token at end of input.
    Eof,

    // ---- appended, owner decision 2026-09-19 round 4: additive only,
    // never reorder anything above. ----
    /// `type` (ch07 Disambiguation 20): reserved; introduces an associated
    /// type inside a `trait` or `impl` body and has no other production.
    KwType,

    // ---- appended, owner decision 2026-09-19 round 5 (D2): additive only,
    // never reorder anything above. ----
    /// `spmd` (ch07 reserved-unused): the SPMD region of ch01/ch03 (M6).
    /// Reserved from v0.1; no production mentions it.
    KwSpmd,
    /// `kernel` (ch07 reserved-unused): the device-kernel region of
    /// ch01/ch03 (M9). Reserved from v0.1; no production mentions it.
    KwKernel,

    // ---- appended, owner decision 2026-09-20 round 6 (O2): additive only,
    // never reorder anything above. ----
    /// `defer` (ch07 `defer_stmt`): its body runs on every exit of the
    /// directly containing block (ch01 Rules 23-23a).
    KwDefer,
    /// `errdefer` (ch07 `errdefer_stmt`): its body runs on the ERROR exits
    /// of the directly containing block only (ch01 Rule 23b, ch02 Rule 16).
    KwErrdefer,
}

impl TokenKind {
    /// Whitespace and comments: never significant to the grammar, kept only
    /// so the token stream is lossless.
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
        )
    }
}

/// Looks up a reserved keyword by its exact spelling. Returns `None` for
/// every contextual keyword and every ordinary identifier — those lex as
/// `Ident` (see module docs).
pub fn keyword_kind(word: &[u8]) -> Option<TokenKind> {
    use TokenKind::*;
    Some(match word {
        b"module" => KwModule,
        b"use" => KwUse,
        b"pub" => KwPub,
        b"fn" => KwFn,
        b"struct" => KwStruct,
        b"enum" => KwEnum,
        b"trait" => KwTrait,
        b"impl" => KwImpl,
        b"const" => KwConst,
        b"extern" => KwExtern,
        b"let" => KwLet,
        b"var" => KwVar,
        b"inout" => KwInout,
        b"sink" => KwSink,
        b"if" => KwIf,
        b"else" => KwElse,
        b"match" => KwMatch,
        b"for" => KwFor,
        b"in" => KwIn,
        b"while" => KwWhile,
        b"break" => KwBreak,
        b"continue" => KwContinue,
        b"return" => KwReturn,
        b"raise" => KwRaise,
        b"raises" => KwRaises,
        b"with" => KwWith,
        b"parallel" => KwParallel,
        b"simd" => KwSimd,
        b"spawn" => KwSpawn,
        b"comptime" => KwComptime,
        b"move" => KwMove,
        b"consume" => KwConsume,
        b"discard" => KwDiscard,
        b"as" => KwAs,
        b"and" => KwAnd,
        b"or" => KwOr,
        b"not" => KwNot,
        b"true" => KwTrue,
        b"false" => KwFalse,
        b"iso" => KwIso,
        b"imm" => KwImm,
        b"secret" => KwSecret,
        b"dyn" => KwDyn,
        b"asm" => KwAsm,
        b"import" => KwImport,
        b"recover" => KwRecover,
        b"type" => KwType,
        b"spmd" => KwSpmd,
        b"kernel" => KwKernel,
        b"defer" => KwDefer,
        b"errdefer" => KwErrdefer,
        _ => return None,
    })
}

/// Legal integer literal width suffixes (ch07 §4).
pub const INT_SUFFIXES: [&[u8]; 10] = [
    b"i8", b"i16", b"i32", b"i64", b"u8", b"u16", b"u32", b"u64", b"isize", b"usize",
];
/// Legal float literal width suffixes (ch07 §4).
pub const FLOAT_SUFFIXES: [&[u8]; 2] = [b"f32", b"f64"];

/// Whether a glued identifier run is a legal suffix for the literal it
/// follows. Hex/octal/binary literals take integer suffixes only.
pub fn is_legal_suffix(suffix: &[u8], is_radix_literal: bool, is_float_literal: bool) -> bool {
    if is_radix_literal {
        INT_SUFFIXES.contains(&suffix)
    } else if is_float_literal {
        FLOAT_SUFFIXES.contains(&suffix)
    } else {
        INT_SUFFIXES.contains(&suffix) || FLOAT_SUFFIXES.contains(&suffix)
    }
}
