//! `fors-interp`: the FMIR interpreter core (F1).
//!
//! Design: `docs/design/fmir-interpreter.md` §5.1-§5.5. This increment owns
//! the value model ([`value`]), integer/float semantics ([`arith`]) and the
//! dispatch loop ([`exec`]) over the F1 FMIR subset: scalars (`const_*`,
//! trapping and explicit arithmetic, `f*`, `icmp`/`fcmp`, `and`/`or`/`xor`/
//! `not`, `conv_*`), aggregates (`agg_new`, `field`), direct calls
//! (`call_direct`), the single host door (`intrinsic`, closed table in
//! [`exec`]), and terminators (`br`, `cond_br`, `ret`, `trap`,
//! `unreachable`). Everything else (`index`, `try_br`, …) answers
//! [`InterpError`], never a panic.
//!
//! F5 adds `slice_range` and `reduce_tree`: the tree's SHAPE is
//! `fors-fmir::reduce`'s (design §3.9's one normative expansion) and
//! [`reduce`] supplies only the `op` and the slot plumbing (§5.7).
//!
//! Disciplines asserted by test, not just by comment:
//! - [`value`] and [`arith`] contain no `usize` (design §5.1: the crates use
//!   Rust's own word size for host bookkeeping only, never for a
//!   program-visible value). `no_host_word_size_in_value_or_arith` greps the
//!   sources.
//! - No fused multiply-add exists: `no_fma_or_libm_float_rem` greps for
//!   the fused intrinsic name, the host remainder routine name and float
//!   `%` in `src/`.
//! - The interpreter has no optimisation-level input (design §3.6, ch02
//!   R10): `interp_has_no_opt_level_input` constructs [`Config`]
//!   exhaustively, so adding an `-O`-shaped field breaks compilation.

pub mod arith;
pub mod exec;
pub mod program;
pub mod reduce;
pub mod shim;
pub mod value;

pub use arith::{FloatKind, IntKind};
pub use exec::{Env, Exit, InterpError, Outcome, run, run_with_host};
pub use program::{Config, Endian, ProgFn, Program};
pub use shim::{ExitStatus, HostEnv, entry_exit, install_sigpipe_ignore};
pub use value::Slot;
