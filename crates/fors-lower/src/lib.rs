//! `fors-lower`: checked bodies → FMIR (F1).
//!
//! Design: `docs/design/fmir-interpreter.md` §4 (the checker interface),
//! F1 ("lowering + interpreter core"). The lowering walk is driven by
//! [`BodyFacts`](fors_check::facts::BodyFacts) (data D1-D4: per-expression
//! types, resolved callees, receiver/argument conventions, resolved
//! members) over the CST the checker already consumed. It never re-derives
//! a type, never resolves a name, never reads a signature beyond what the
//! facts name: every decision the checker made is READ, not remade.
//!
//! F1 scope: non-generic `fn` bodies over scalars, `bool`, `Str`, local
//! structs (field reads), free-function and inherent-method calls, `let`
//! bindings, assignment, `if`/`else` and blocks. Everything else —
//! generics, `defer`/`errdefer`, projections, closures, `match`, `?`/
//! `raise`, loops, `const` refs — is a clean [`LowerError`] diagnostic,
//! never a panic. The [`Program`](fors_interp::Program)-shaped output is
//! assembled by the caller (tests): this crate returns [`LoweredFn`] rows,
//! so it never depends on the interpreter crate (design §2, "Why three").

//! F-mono adds MONOMORPHISATION and PATTERN lowering to that scope. A call
//! whose `BodyFacts::generic_args` row is non-empty lowers to an
//! instantiation of its callee at those arguments: the body is lowered once
//! per distinct `(callee, arguments)` pair ([`mono::Instances`]), with every
//! substituted type interned in a store this crate OWNS (a clone of the
//! checker's frozen one — see [`mono`]'s module docs). A `match`, and a
//! `let`/`var` destructuring, lowers from `BodyFacts::patterns`: the
//! checker's decided shapes, never re-derived here.

pub mod diag;
pub mod lower;
pub mod mono;

pub use diag::{LowerDiag, LowerError};
pub use lower::{LoweredBuild, LoweredFn, lower_build};
pub use mono::{Instance, Instances};
