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
//! **F4's interpreter half** (design §3.8, §5.4; `type-checker.md` §13 I8b)
//! executes `fors-fmir`'s exit-edge data: at every control transfer the
//! dispatch loop runs the edge's pending `defer`/`errdefer` bodies, then the
//! drops, then ch01 R22h's check, then the transfer — in that order, from
//! the data, never re-derived. A `trap` is not an exit and runs none of it.
//!
//! **F6's interpreter half** (design §3.5, §3.7, §5.1, §5.2) adds [`mem`]'s
//! allocation objects, arenas and generation checks, and [`ub`]'s detection
//! list. A `ub:` report is NOT a trap (E4): ch02 R15's kind list is closed at
//! eight, so a compiler bug exits [`ub::UB_EXIT_STATUS`] with a
//! machine-readable record instead of looking like a program trap. Owner
//! **Q7**'s backtrace switch lives at the one reporting site, [`trap`].
//!
//! What is explicitly NOT here: the LOWERING halves of F4 and F6. They need
//! checker increment I8b's `D7`/`D8` side tables, which do not exist yet
//! ([HOLE-11]), so both halves are built and tested against hand-written
//! FMIR — design §4.2's "no checker dependency and can be built and tested
//! against F0 textual FMIR first".
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
pub mod mem;
pub mod program;
pub mod reduce;
pub mod shim;
pub mod trap;
pub mod ub;
pub mod value;

pub use arith::{FloatKind, IntKind};
pub use exec::{Env, Exit, InterpError, Outcome, run, run_with_host};
pub use mem::{AllocKind, AllocState, AllocatorId, ArenaId, ArenaVal, RefVal, next_generation};
pub use program::{Config, Endian, ProgFn, Program};
pub use shim::{ExitStatus, HostEnv, entry_exit, install_sigpipe_ignore};
pub use trap::{BacktraceFrame, backtrace_enabled, report_trap, report_ub, trap_line};
pub use ub::{UB_EXIT_STATUS, UbClass, UbReport};
pub use value::Slot;
