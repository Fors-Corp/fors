//! Lexer diagnostics: a byte offset range plus a stable code, per the
//! engineering rule that failures are values, never panics.

/// Stable diagnostic code. Numbers are part of the contract other tools may
/// key on (e.g. suppressions); append, never renumber.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagCode {
    /// `/* ... ` reached EOF at nesting depth > 0 (ch07 §2).
    UnterminatedBlockComment = 0,
    /// A `"..."` string hit a raw newline or EOF before its closing quote
    /// (ch07 §5).
    UnterminatedString = 1,
    /// An escape inside a `"..."` string is not one of
    /// `\n \r \t \0 \\ \" \xHH \u{H..}` (ch07 §5).
    BadEscape = 2,
    /// An identifier run glued directly onto a number literal is not one of
    /// the legal width suffixes (ch07 §4).
    BadSuffix = 3,
    /// `..` not immediately followed by `<` or `=` (ch07 §7).
    BadRangeDots = 4,
    /// A byte that starts no token at all (stray punctuation, a bare
    /// non-ASCII byte outside a comment/string, ...).
    StrayByte = 5,
    /// The source is larger than `MAX_SOURCE_LEN`; lexing stops after one
    /// error token.
    FileTooLarge = 6,
    /// The source is not valid UTF-8 (inside a comment or string literal;
    /// elsewhere the bytes are already a `StrayByte`). First occurrence only.
    InvalidUtf8 = 7,
}

/// One lexical diagnostic: a half-open byte range `[start, end)` into the
/// source, plus its code. Carries no message string — that is a rendering
/// concern for a caller that has the source text and a locale.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Diagnostic {
    pub start: u32,
    pub end: u32,
    pub code: DiagCode,
}

impl DiagCode {
    pub fn as_str(self) -> &'static str {
        match self {
            DiagCode::UnterminatedBlockComment => "L0000",
            DiagCode::UnterminatedString => "L0001",
            DiagCode::BadEscape => "L0002",
            DiagCode::BadSuffix => "L0003",
            DiagCode::BadRangeDots => "L0004",
            DiagCode::StrayByte => "L0005",
            DiagCode::FileTooLarge => "L0006",
            DiagCode::InvalidUtf8 => "L0007",
        }
    }
}

impl Diagnostic {
    pub fn new(start: u32, end: u32, code: DiagCode) -> Self {
        Diagnostic { start, end, code }
    }
}
