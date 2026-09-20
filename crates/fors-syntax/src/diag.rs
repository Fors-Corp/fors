//! Parser diagnostics: a byte offset range plus a stable `Pxxxx` code
//! (append, never renumber).
//! Never a panic path — every parse failure becomes one of these.

#[repr(u16)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagCode {
    /// A production expected a specific token (or one of a small set) and
    /// found something else.
    Expected = 1,
    /// Statement sync set: a `;` was expected but the next token is a
    /// statement/declaration boundary; one virtual `;` is inserted.
    MissingSemicolon = 2,
    /// A `{`/`(`/`[` was never closed before a declaration-sync token or
    /// the end of the file; every open construct up to the enclosing item
    /// list was force-closed. The range is the opening delimiter.
    UnclosedBrace = 3,
    /// The left-hand side of an `assign_op` does not have the shape of a
    /// `place`.
    AssignTargetNotPlace = 4,
    /// Ch07 rule 12: mixing a bitwise operator with arithmetic, range,
    /// comparison or a different bitwise operator needs parentheses.
    BitwiseNeedsParens = 5,
    /// Ch07: comparison operators do not chain.
    ComparisonChained = 6,
    /// Recursion/nesting depth limit hit; parsing of the construct stopped
    /// rather than risking a stack overflow.
    NestingTooDeep = 7,
    /// A lexical error (the message names which); the token was skipped.
    LexError = 8,
    /// Tokens that start no declaration/item; the range covers what was
    /// skipped to resynchronise.
    UnexpectedToken = 9,
    /// Ch07 operator table level 6: range operators are single use.
    RangeChained = 10,
}

impl DiagCode {
    pub fn as_str(self) -> &'static str {
        match self {
            DiagCode::Expected => "P0001",
            DiagCode::MissingSemicolon => "P0002",
            DiagCode::UnclosedBrace => "P0003",
            DiagCode::AssignTargetNotPlace => "P0004",
            DiagCode::BitwiseNeedsParens => "P0005",
            DiagCode::ComparisonChained => "P0006",
            DiagCode::NestingTooDeep => "P0007",
            DiagCode::LexError => "P0008",
            DiagCode::UnexpectedToken => "P0009",
            DiagCode::RangeChained => "P0010",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub start: u32,
    pub end: u32,
    pub code: DiagCode,
    pub message: &'static str,
}

impl Diagnostic {
    pub fn new(start: u32, end: u32, code: DiagCode, message: &'static str) -> Self {
        Diagnostic {
            start,
            end,
            code,
            message,
        }
    }
}
