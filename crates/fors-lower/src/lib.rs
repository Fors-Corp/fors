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
//! bindings, assignment, `if`/`else` and blocks. Everything outside the
//! lowered subset — projections, closures, `const` refs, the M3
//! concurrency statements — is a clean [`LowerError`] diagnostic, never a
//! panic (later increments widened the subset: loops, `match`, generics,
//! `defer`/`errdefer`, and F3's `?`/`else |e|`/`raise`). The [`Program`](fors_interp::Program)-shaped output is
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
//!
//! F3 adds ch02's failure surface from `BodyFacts::failure` (D10) — `?` and
//! `else |e| { }` as a `try_br` on the call, `raise` as the `raise`
//! terminator on an `Error` exit edge — and lowers ch03's explicit-arithmetic
//! methods and `reduce` from `BodyFacts::numeric` (D11) instead of by
//! spelling. [`LoweredBuild::names`] carries the static names ch02 R17's
//! `render` needs.

pub mod diag;
pub mod lower;
pub mod mono;

pub use diag::{LowerDiag, LowerError};
pub use lower::{LoweredBuild, LoweredFn, lower_build};
pub use mono::{Instance, Instances};
