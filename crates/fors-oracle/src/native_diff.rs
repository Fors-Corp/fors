//! The native differential (`docs/design/m2-dev-backend.md` §5, §10 M2-0):
//! every program through the interpreter (the oracle) and through the
//! native backend, records compared — exit (`Status(n)` ↔ `Status(n)`,
//! `Trap{kind}` ↔ `Signal(SIGTRAP)`), stdout bytes, stderr bytes. Every
//! program gets exactly one [`NativeVerdict`] and every class is counted in
//! the [`Tally`]: `ok / mismatch / refused / compile-panic / spawn-fail /
//! signal / timeout`, plus `oracle-fail` (the interpreter itself did not
//! produce a clean record — never expected, never dropped).
//!
//! M2-0's one documented relaxation: a trapping interpreter run ends its
//! stderr with the `trap: <kind> at …` line, which the native side prints
//! only once the runtime's SIGTRAP handler exists (M2-3). Until then the
//! native stderr is compared with the interpreter's MINUS that last line.
//! `steps` and `heap_digest` have no native counterpart and are never
//! compared.

use std::ops::Range;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use fors_interp::{OracleRecord, RecordExit};

use crate::generate::{Profile, generate_with};
use crate::native::{CompileFail, NativeExit, NativeRecord, Phases, Runner, SIGTRAP, compile};
use crate::{Candidate, RunResult, run_candidate};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeVerdict {
    Ok,
    /// The records differ in this field (`exit`, `stdout`, `stderr`).
    Mismatch(String),
    /// The backend refused the program by name.
    Refused(String),
    /// The backend panicked or the link failed.
    CompilePanic(String),
    /// The image could not be written or spawned.
    SpawnFail(String),
    /// The native process died by a signal the interpreter did not predict.
    Signal(i32),
    /// The native process ran past the timeout.
    Timeout,
    /// The interpreter refused, panicked or reported `ub:`.
    OracleFail(String),
}

impl NativeVerdict {
    pub fn class(&self) -> &'static str {
        match self {
            NativeVerdict::Ok => "ok",
            NativeVerdict::Mismatch(_) => "mismatch",
            NativeVerdict::Refused(_) => "refused",
            NativeVerdict::CompilePanic(_) => "compile-panic",
            NativeVerdict::SpawnFail(_) => "spawn-fail",
            NativeVerdict::Signal(_) => "signal",
            NativeVerdict::Timeout => "timeout",
            NativeVerdict::OracleFail(_) => "oracle-fail",
        }
    }
}

/// Strips the interpreter's trailing trap line (see the module docs).
fn without_trap_line(stderr: &[u8]) -> &[u8] {
    let body = stderr.strip_suffix(b"\n").unwrap_or(stderr);
    match body.iter().rposition(|&b| b == b'\n') {
        Some(i) if body[i + 1..].starts_with(b"trap: ") => &stderr[..i + 1],
        None if body.starts_with(b"trap: ") => &[],
        _ => stderr,
    }
}

/// Compares an interpreter record with a native one.
pub fn compare(interp: &OracleRecord, native: &NativeRecord) -> NativeVerdict {
    let trapped = matches!(interp.exit, RecordExit::Trap { .. });
    match (&interp.exit, &native.exit) {
        (RecordExit::Ub { class, .. }, _) => {
            return NativeVerdict::OracleFail(format!("ub: {}", class.as_str()));
        }
        (_, NativeExit::Timeout) => return NativeVerdict::Timeout,
        (RecordExit::Trap { .. }, NativeExit::Signal(SIGTRAP)) => {}
        (_, NativeExit::Signal(s)) => return NativeVerdict::Signal(*s),
        (RecordExit::Status(a), NativeExit::Status(b)) if a == b => {}
        _ => return NativeVerdict::Mismatch("exit".into()),
    }
    if interp.stdout != native.stdout {
        return NativeVerdict::Mismatch("stdout".into());
    }
    let want = if trapped {
        without_trap_line(&interp.stderr)
    } else {
        &interp.stderr[..]
    };
    if want != native.stderr.as_slice() {
        return NativeVerdict::Mismatch("stderr".into());
    }
    NativeVerdict::Ok
}

/// Timings of one checked program (microseconds).
#[derive(Clone, Copy, Debug, Default)]
pub struct Timing {
    pub interp: u64,
    pub compile: u64,
    pub native: u64,
    pub phases: Phases,
    pub image_size: usize,
}

/// Runs `c` through both engines with `runner`'s scratch directory.
pub fn check_with(c: &Candidate, runner: &Runner) -> (NativeVerdict, Timing) {
    let mut tm = Timing::default();
    let t = Instant::now();
    let interp = match run_candidate(c) {
        RunResult::Record(r) => r,
        RunResult::Refused(e) => return (NativeVerdict::OracleFail(e), tm),
        RunResult::Panicked(p) => return (NativeVerdict::OracleFail(format!("panic: {p}")), tm),
    };
    tm.interp = t.elapsed().as_micros() as u64;
    let t = Instant::now();
    let compiled = match compile(c) {
        Ok(x) => x,
        Err(CompileFail::Refused(r)) => return (NativeVerdict::Refused(r.to_string()), tm),
        Err(CompileFail::Panicked(p)) => return (NativeVerdict::CompilePanic(p), tm),
    };
    tm.compile = t.elapsed().as_micros() as u64;
    tm.phases = compiled.phases;
    tm.image_size = compiled.image.len();
    let t = Instant::now();
    let native = match runner.run(&compiled.image) {
        Ok((rec, write_us)) => {
            tm.phases.write = write_us;
            rec
        }
        Err(e) => return (NativeVerdict::SpawnFail(e), tm),
    };
    tm.native = t.elapsed().as_micros() as u64;
    (compare(&interp, &native), tm)
}

/// Per-class counts over a run, plus the first non-`ok` seeds and the
/// report numbers.
#[derive(Clone, Debug, Default)]
pub struct Tally {
    pub ok: u64,
    pub mismatch: u64,
    pub refused: u64,
    pub compile_panic: u64,
    pub spawn_fail: u64,
    pub signal: u64,
    pub timeout: u64,
    pub oracle_fail: u64,
    /// `(seed, verdict)` of the first 20 non-`ok` programs, by seed.
    pub failures: Vec<(u64, NativeVerdict)>,
    pub instructions: u64,
    pub interp_us: u64,
    pub compile_us: u64,
    pub native_us: u64,
    /// The largest program (by FMIR instructions): seed, size, phases,
    /// image bytes.
    pub largest: Option<(u64, usize, Phases, usize)>,
}

impl Tally {
    pub fn total(&self) -> u64 {
        self.ok
            + self.mismatch
            + self.refused
            + self.compile_panic
            + self.spawn_fail
            + self.signal
            + self.timeout
            + self.oracle_fail
    }

    pub fn add(&mut self, seed: u64, v: NativeVerdict) {
        match &v {
            NativeVerdict::Ok => self.ok += 1,
            NativeVerdict::Mismatch(_) => self.mismatch += 1,
            NativeVerdict::Refused(_) => self.refused += 1,
            NativeVerdict::CompilePanic(_) => self.compile_panic += 1,
            NativeVerdict::SpawnFail(_) => self.spawn_fail += 1,
            NativeVerdict::Signal(_) => self.signal += 1,
            NativeVerdict::Timeout => self.timeout += 1,
            NativeVerdict::OracleFail(_) => self.oracle_fail += 1,
        }
        if v != NativeVerdict::Ok && self.failures.len() < 20 {
            self.failures.push((seed, v));
        }
    }

    /// One line, every class named with its count.
    pub fn line(&self) -> String {
        format!(
            "programs {} | ok {} | mismatch {} | refused {} | compile-panic {} | spawn-fail {} | \
             signal {} | timeout {} | oracle-fail {} | fmir instructions {}",
            self.total(),
            self.ok,
            self.mismatch,
            self.refused,
            self.compile_panic,
            self.spawn_fail,
            self.signal,
            self.timeout,
            self.oracle_fail,
            self.instructions
        )
    }
}

/// Generates seeds `seeds` under `p` and checks each, on as many worker
/// threads as the machine has. Results are tallied BY SEED, so the tally
/// does not depend on the worker count.
pub fn run_seeds(seeds: Range<u64>, p: &Profile) -> Tally {
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(16);
    let next = AtomicU64::new(seeds.start);
    let results: Mutex<Vec<(u64, usize, NativeVerdict, Timing)>> = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..workers {
            s.spawn(|| {
                let runner = Runner::new();
                loop {
                    let seed = next.fetch_add(1, Ordering::Relaxed);
                    if seed >= seeds.end {
                        break;
                    }
                    let g = generate_with(seed, p);
                    let n = g.instruction_count();
                    let c = Candidate {
                        prog: g.prog,
                        tys: g.tys,
                    };
                    let (v, tm) = match &runner {
                        Ok(r) => check_with(&c, r),
                        Err(e) => (
                            NativeVerdict::SpawnFail(format!("scratch dir: {e}")),
                            Timing::default(),
                        ),
                    };
                    results
                        .lock()
                        .expect("no poisoned worker")
                        .push((seed, n, v, tm));
                }
            });
        }
    });
    let mut rs = results.into_inner().expect("no poisoned worker");
    rs.sort_by_key(|r| r.0);
    let mut t = Tally::default();
    for (seed, n, v, tm) in rs {
        t.instructions += n as u64;
        t.interp_us += tm.interp;
        t.compile_us += tm.compile;
        t.native_us += tm.native;
        if v == NativeVerdict::Ok && t.largest.as_ref().is_none_or(|l| n > l.1) {
            t.largest = Some((seed, n, tm.phases, tm.image_size));
        }
        t.add(seed, v);
    }
    t
}
