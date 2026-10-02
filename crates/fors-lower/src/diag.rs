//! Clean lowering diagnostics: what F1 cannot lower, and why.
//!
//! Every rejection names the function and the reason. There is no "cannot
//! happen" case: the walk is total over the CST, and anything outside the
//! F1 scope lands here.

use fors_index::ids::DefId;

/// Why one function body was not lowered.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LowerError {
    /// The body had a type error: lowering only reads checked-clean facts.
    /// Carries the first checker diagnostic code for the body, if known.
    CheckErrors,
    /// A generic declaration or a generic/tainted call: I5 owns it.
    Generic(String),
    /// A projection (`I.Item`, qualified associated type): I6 owns it.
    Projection,
    /// A closure literal or `fn` value: captures are I9's (R19c/R19d).
    Closure,
    /// `match`: I7 owns patterns and exhaustiveness.
    Match,
    /// A ch02 failure form (`?`, `else |e|`, `raise`) F3 cannot lower,
    /// with the reason: the checker published no D10 row for it (a checker
    /// gap — lowering never re-derives the edge from syntax), or the edge
    /// needs an impl D10 does not name (`ErrorFromBound`, a generic
    /// `ErrorFrom` impl).
    Failure(String),
    /// `for`/`while` loops: F1 covers straight-line code plus `if`; loops
    /// lower in a later increment (design F1's `plain-for-accumulator` gate
    /// moves with them).
    Loop,
    /// A reference to a `const`/`comptime` item: F9 owns comptime.
    Comptime(String),
    /// Anything else outside the F1 expression/statement subset. Carries
    /// the CST kind name so the diagnostic is actionable.
    Unsupported(String),
    /// A name the facts never bound (lowering bug or resolver gap) — still
    /// a diagnostic, never a panic.
    Unresolved(String),
    /// F7 (ch10 R26): a string literal's decoded bytes are not valid
    /// UTF-8. The lexer validates only the raw source bytes; `\xHH`
    /// escapes are decoded here and MUST be checked too, or a `Str`
    /// value could carry invalid UTF-8 straight from a literal.
    InvalidUtf8Literal(String),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::CheckErrors => write!(
                f,
                "body has type errors; F1 lowers checked-clean bodies only"
            ),
            LowerError::Generic(w) => write!(f, "generics are not lowered in F1 ({w})"),
            LowerError::Projection => write!(f, "projections need I6; not lowered in F1"),
            LowerError::Closure => write!(f, "closures need capture decisions; not lowered in F1"),
            LowerError::Match => write!(f, "`match` needs I7; not lowered in F1"),
            LowerError::Failure(w) => write!(f, "failure edge not lowered: {w}"),
            LowerError::Loop => write!(f, "loops are not lowered in F1"),
            LowerError::Comptime(w) => write!(f, "comptime item references need F9 ({w})"),
            LowerError::Unsupported(k) => write!(f, "`{k}` is outside the F1 subset"),
            LowerError::Unresolved(n) => write!(f, "could not resolve `{n}` from BodyFacts"),
            LowerError::InvalidUtf8Literal(reason) => {
                write!(
                    f,
                    "string literal is not valid UTF-8 after \\x decoding: {reason}"
                )
            }
        }
    }
}

impl std::error::Error for LowerError {}

/// One skipped function: which one, and why.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LowerDiag {
    pub def: DefId,
    pub name: String,
    pub error: LowerError,
}
