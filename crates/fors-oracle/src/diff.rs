//! The differential runner (`compiler-architecture.md` §8): every generated
//! program runs through the interpreter, then through a REPLAY of its own
//! [`fors_interp::OracleRecord`] (design §7.2: the interpreter must be a
//! function of FMIR, declared inputs and capability responses, so the
//! replay must reproduce the record byte for byte, step count included).
//! M1 has one engine; the backends join this runner as further engines.
//!
//! Every program gets exactly one [`Verdict`] and every verdict is counted
//! ([`Tally`]); nothing is dropped. A generated program is UB-free and
//! trap-free BY CONSTRUCTION ([`crate::generate`]), so anything but `ok` is a
//! generator bug or an interpreter bug to triage, never a result to waive.

use fors_interp::{OracleRecord, RecordExit};

use crate::generate::Generated;
use crate::{Candidate, RunResult, run_with};

/// One program's classification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// Ran to a normal exit, and the replay reproduced the record.
    Ok,
    /// The interpreter panicked (live or under replay).
    Panic(String),
    /// A `ub:` report: the interpreter found undefined behaviour.
    Ub(String),
    /// The replay's record differs from the live one in this field.
    RecordMismatch(&'static str),
    /// A trap: impossible by construction, so a generator bug or a wrong
    /// trap in the interpreter.
    Trap(String),
    /// A named interpreter refusal, or a non-zero exit status.
    InterpError(String),
    /// The generated FMIR failed `fors_fmir::verify`: a generator bug.
    VerifyReject(String),
}

impl Verdict {
    pub fn class(&self) -> &'static str {
        match self {
            Verdict::Ok => "ok",
            Verdict::Panic(_) => "panic",
            Verdict::Ub(_) => "ub",
            Verdict::RecordMismatch(_) => "record-mismatch",
            Verdict::Trap(_) => "trap",
            Verdict::InterpError(_) => "interp-error",
            Verdict::VerifyReject(_) => "verify-reject",
        }
    }
}

/// Classifies one generated program; the step count is the live run's
/// (0 when it did not complete).
pub fn check(g: &Generated) -> (Verdict, u64) {
    let mut steps = 0;
    let v = classify(g, &mut steps);
    (v, steps)
}

fn classify(g: &Generated, steps: &mut u64) -> Verdict {
    for f in &g.prog.fns {
        if let Some(d) = fors_fmir::verify::verify(&f.decl).first() {
            return Verdict::VerifyReject(format!("{}: {}", f.name, d.message));
        }
    }
    let c = Candidate {
        prog: g.prog.clone(),
        tys: g.tys.clone(),
    };
    let live = match run_with(&c, None) {
        RunResult::Record(r) => r,
        RunResult::Refused(e) => return Verdict::InterpError(e),
        RunResult::Panicked(p) => return Verdict::Panic(p),
    };
    *steps = live.steps;
    match live.exit {
        RecordExit::Status(0) => {}
        RecordExit::Status(n) => return Verdict::InterpError(format!("exit status {n}")),
        RecordExit::Trap { kind, .. } => return Verdict::Trap(kind.as_str().to_string()),
        RecordExit::Ub { class, .. } => return Verdict::Ub(class.as_str().to_string()),
    }
    let replayed: OracleRecord = match run_with(&c, Some(&live)) {
        RunResult::Record(r) => r,
        RunResult::Refused(e) => return Verdict::InterpError(format!("under replay: {e}")),
        RunResult::Panicked(p) => return Verdict::Panic(format!("under replay: {p}")),
    };
    match live.first_difference(&replayed) {
        Some(field) => Verdict::RecordMismatch(field),
        None => Verdict::Ok,
    }
}

/// Counts per class over a run, plus the first few non-`ok` seeds.
#[derive(Clone, Debug, Default)]
pub struct Tally {
    pub ok: u64,
    pub panic: u64,
    pub ub: u64,
    pub record_mismatch: u64,
    pub trap: u64,
    pub interp_error: u64,
    pub verify_reject: u64,
    /// Total FMIR instructions (rows plus terminators) generated.
    pub instructions: u64,
    /// Total interpreter steps over the live runs of `ok` programs, and the
    /// largest single run.
    pub steps: u64,
    pub max_steps: u64,
    /// `(seed, verdict)` for the first non-`ok` programs (at most 20).
    pub failures: Vec<(u64, Verdict)>,
}

impl Tally {
    pub fn total(&self) -> u64 {
        self.ok
            + self.panic
            + self.ub
            + self.record_mismatch
            + self.trap
            + self.interp_error
            + self.verify_reject
    }

    pub fn add(&mut self, seed: u64, v: Verdict) {
        match &v {
            Verdict::Ok => self.ok += 1,
            Verdict::Panic(_) => self.panic += 1,
            Verdict::Ub(_) => self.ub += 1,
            Verdict::RecordMismatch(_) => self.record_mismatch += 1,
            Verdict::Trap(_) => self.trap += 1,
            Verdict::InterpError(_) => self.interp_error += 1,
            Verdict::VerifyReject(_) => self.verify_reject += 1,
        }
        if v != Verdict::Ok && self.failures.len() < 20 {
            self.failures.push((seed, v));
        }
    }

    /// One line, every class named with its count.
    pub fn line(&self) -> String {
        format!(
            "programs {} | ok {} | panic {} | ub {} | record-mismatch {} | trap {} | \
             interp-error {} | verify-reject {} | fmir instructions {} | steps {} (max {})",
            self.total(),
            self.ok,
            self.panic,
            self.ub,
            self.record_mismatch,
            self.trap,
            self.interp_error,
            self.verify_reject,
            self.instructions,
            self.steps,
            self.max_steps
        )
    }
}

/// Generates and checks every seed in `seeds`.
pub fn run_seeds(seeds: std::ops::Range<u64>) -> Tally {
    let mut t = Tally::default();
    for seed in seeds {
        let g = crate::generate::generate(seed);
        t.instructions += g.instruction_count() as u64;
        let (v, steps) = check(&g);
        t.steps += steps;
        t.max_steps = t.max_steps.max(steps);
        t.add(seed, v);
    }
    t
}
