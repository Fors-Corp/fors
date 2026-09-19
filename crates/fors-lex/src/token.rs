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
        b"import" => KwImport,
        b"recover" => KwRecover,
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
