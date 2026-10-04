//! `fors-oracle`: F10's correctness harness around the FMIR interpreter
//! (design `docs/design/fmir-interpreter.md` §7, §9 F10;
//! `compiler-architecture.md` §8).
//!
//! - [`generate`]: the FMIR-level typed random program generator — seeded,
//!   deterministic, bounded loops, UB-free and trap-free by construction,
//!   a checksum on `Stdout`.
//! - [`diff`]: the differential runner — each program through the
//!   interpreter, then through a replay of its own [`fors_interp::OracleRecord`],
//!   classified `ok` / `panic` / `ub` / `record-mismatch` (plus the
//!   by-construction-impossible `trap`, `interp-error` and `verify-reject`,
//!   each counted, never dropped).
//! - [`reduce`]: the three-stage minimiser (design §7.3): source level
//!   (declarations, then statements), FMIR level (functions, terminators and
//!   blocks, instructions), value level (constants), the predicate re-checked
//!   after every step, the order of attempts drawn from a seed.
//! - [`build`]: source to runnable FMIR through a caller-chosen lowering.
//! - [`native`] / [`native_diff`] (M2-0, `docs/design/m2-dev-backend.md`
//!   §5): the dev backend as a second engine — compile, link, sign, spawn —
//!   and the interpreter-vs-native differential with its per-class tally.
//!
//! Nothing in the compiler depends on this crate.

pub mod build;
pub mod diff;
pub mod generate;
pub mod native;
pub mod native_diff;
pub mod reduce;
pub mod rng;

use fors_fir::ty::TyStore;
use fors_interp::{HostEnv, Oracle, OracleRecord, Program};

/// A runnable FMIR program: what the FMIR and value stages reduce, and what
/// every predicate is asked about.
#[derive(Clone)]
pub struct Candidate {
    pub prog: Program,
    pub tys: TyStore,
}

/// How one in-process run of a candidate ended, panics included.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult {
    /// The run completed (any exit, trap and `ub:` included) with this
    /// record.
    Record(OracleRecord),
    /// The interpreter refused the program by name.
    Refused(String),
    /// The interpreter PANICKED: always an interpreter bug.
    Panicked(String),
}

/// The step cap on every run this crate makes: a generated program runs at
/// most a few thousand steps (bounded loops, no recursion), and a reducer
/// candidate that a deletion turned into an endless loop must answer fast.
/// Past it a run is the interpreter's named `StepBudget` refusal.
pub const STEP_CAP: u64 = 2_000_000;

/// The tighter cap the minimiser's predicates run under: its inputs are
/// small programs (the seed program runs ~400 steps), and most candidates
/// that loop do so because a deletion removed the loop's increment.
pub const REDUCE_STEP_CAP: u64 = 100_000;

/// Runs `c` live (captured streams, no descriptors), catching a panic.
pub fn run_candidate(c: &Candidate) -> RunResult {
    run_with(c, None)
}

/// Runs `c`, serving host responses from `replay` when given.
pub fn run_with(c: &Candidate, replay: Option<&OracleRecord>) -> RunResult {
    run_capped(c, replay, STEP_CAP)
}

/// [`run_with`] under an explicit step cap.
pub fn run_capped(c: &Candidate, replay: Option<&OracleRecord>, cap: u64) -> RunResult {
    let host = HostEnv::default();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match replay {
        None => fors_interp::run_recorded_capped(&c.prog, &c.tys, &host, &mut Oracle::live(), cap),
        Some(rec) => fors_interp::replay_recorded_capped(&c.prog, &c.tys, &host, rec, cap),
    }));
    match r {
        Ok(Ok(rec)) => RunResult::Record(rec),
        Ok(Err(e)) => RunResult::Refused(e.to_string()),
        Err(p) => RunResult::Panicked(panic_text(&*p)),
    }
}

pub(crate) fn panic_text(p: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = p.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = p.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}
