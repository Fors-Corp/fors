//! `fors-lex`: the lexer for the Fors compiler frontend (spec ch07).
//!
//! Std only, no per-token heap allocation: tokens are `(kind, start)` pairs
//! in parallel columns (see [`Tokens`]), and a token's text is a byte-slice
//! offset into the caller's source buffer, never an owned string. Each file
//! is lexed independently with no global state, so callers may lex many
//! files in parallel.

mod diag;
mod lexer;
mod token;

pub use diag::{DiagCode, Diagnostic};
pub use lexer::{MAX_SOURCE_LEN, Tokens, lex};
pub use token::{TokenKind, keyword_kind};
