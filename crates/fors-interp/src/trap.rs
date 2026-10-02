//! **The one trap-reporting site** (design §5.3, §7.2a; owner decision
//! **Q7**, accepted 2026-10-02).
//!
//! §5.3: a `trap` is a deterministic whole-process abort — the interpreter
//! "prints one line to its own stderr — `trap: <kind> at <file>:<L>:<C>`",
//! performs no deferred body, does not flush `Stdout`, and exits by a signal
//! status.
//!
//! §7.2a fixes that line as part of ch05 R17's byte comparison, "which makes
//! a **backtrace on the trap path illegal for any program in the differential
//! corpus**". `compiler-architecture.md` §7 promises an FP-walking backtrace
//! printer anyway, so Q7 resolves the conflict: **the trap handler prints
//! exactly the one line §7.2a fixes; a backtrace is opt-in
//! (`FORS_BACKTRACE=1`) and excluded from the differential corpus.**
//!
//! The switch lives HERE and nowhere else: [`report_trap`] is the only
//! function in this crate that writes a trap line, so there is no second path
//! a backtrace could leak onto. [`report_ub`] is its `ub:` twin (design §5.2)
//! and takes the same switch, for the same reason.

use std::io::Write;

use fors_fmir::op::TrapKind;

use crate::ub::UbReport;

/// The environment variable Q7 names. Exactly `"1"` enables the backtrace;
/// anything else, including `"0"`, `"true"` and an unset variable, leaves it
/// off — a single accepted spelling keeps "is the corpus running with
/// backtraces?" a yes/no question.
pub const BACKTRACE_ENV: &str = "FORS_BACKTRACE";

/// Is the opt-in backtrace enabled for this process (owner Q7)?
pub fn backtrace_enabled() -> bool {
    std::env::var(BACKTRACE_ENV).ok().as_deref() == Some("1")
}

/// One frame of the opt-in backtrace: the function and the site within it.
/// Derived entirely from FMIR (a declaration name plus a `SitePool` row), so
/// it is deterministic — but it is still host- and layout-adjacent in spirit
/// and §7.2a keeps it out of the oracle record regardless.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BacktraceFrame {
    pub func: String,
    pub line: u32,
    pub col: u32,
}

/// §7.2a's exact trap line, newline included: `trap: <kind> at
/// <file>:<L>:<C>`. `<kind>` is one of ch02 R15's eight strings
/// ([`TrapKind::as_str`]), never an interpreter-invented name.
pub fn trap_line(kind: TrapKind, file: &str, line: u32, col: u32) -> String {
    format!("trap: {} at {}:{}:{}\n", kind.as_str(), file, line, col)
}

/// Writes the trap report to `w` (the process's **unbuffered** `Stderr` in a
/// real run — ch10 R40 makes `Stderr` unbuffered, which is why the three
/// `trap`/`defer` corpus tests can observe it at all).
///
/// `frames` is printed **only** under `FORS_BACKTRACE=1`. The caller passes
/// whatever it has; this function decides. Nothing else in this crate writes
/// a trap line, so the switch cannot be bypassed.
pub fn report_trap(
    w: &mut impl Write,
    kind: TrapKind,
    file: &str,
    line: u32,
    col: u32,
    frames: &[BacktraceFrame],
) -> std::io::Result<()> {
    w.write_all(trap_line(kind, file, line, col).as_bytes())?;
    write_backtrace(w, frames)
}

/// The `ub:` twin of [`report_trap`] (design §5.2): a `ub:` diagnostic is not
/// a trap — it exits 70 and carries a machine-readable record — and its line
/// is likewise the only thing printed unless the Q7 switch is on.
pub fn report_ub(
    w: &mut impl Write,
    report: &UbReport,
    file: &str,
    frames: &[BacktraceFrame],
) -> std::io::Result<()> {
    w.write_all(report.line(file).as_bytes())?;
    write_backtrace(w, frames)
}

fn write_backtrace(w: &mut impl Write, frames: &[BacktraceFrame]) -> std::io::Result<()> {
    if !backtrace_enabled() {
        return Ok(());
    }
    for (i, f) in frames.iter().enumerate() {
        writeln!(w, "  {i}: {} at {}:{}", f.func, f.line, f.col)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `FORS_BACKTRACE` is process-global and `cargo test` runs this
    /// module's tests on parallel threads: every test that sets, removes
    /// or depends on the variable's absence holds this lock for its whole
    /// body, or one test's `remove_var` lands between another's `set_var`
    /// and its read (F7 verification: that race failed about one run in
    /// five).
    static ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn frames() -> Vec<BacktraceFrame> {
        vec![BacktraceFrame {
            func: "main".into(),
            line: 12,
            col: 5,
        }]
    }

    #[test]
    fn the_trap_line_is_exactly_the_one_line_7_2a_fixes() {
        assert_eq!(
            trap_line(TrapKind::ArenaGeneration, "main.fors", 12, 5),
            "trap: arena-generation at main.fors:12:5\n"
        );
        // Every one of ch02 R15's eight is spelled by its own string, and no
        // other text appears on the line.
        for (i, name) in TrapKind::KINDS.iter().enumerate() {
            let k = TrapKind::from_u32(i as u32).unwrap();
            let line = trap_line(k, "a.fors", 1, 1);
            assert_eq!(line, format!("trap: {name} at a.fors:1:1\n"));
        }
    }

    /// The Q7 switch, both ways, at the ONE reporting site. The env var is
    /// process-global, so this one test covers both branches in sequence
    /// rather than two tests racing over it.
    #[test]
    fn a_backtrace_appears_only_under_fors_backtrace_1() {
        let _env = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let previous = std::env::var(BACKTRACE_ENV).ok();

        // SAFETY (both `set_var`/`remove_var` calls): this test owns the
        // variable for its duration under `ENV_LOCK` and restores it; the
        // only other test touching it (`a_ub_report_goes_through_the_
        // same_site`) takes the same lock, so no concurrent reader exists.
        unsafe { std::env::remove_var(BACKTRACE_ENV) };
        let mut off = Vec::new();
        report_trap(&mut off, TrapKind::Bounds, "a.fors", 3, 4, &frames()).unwrap();
        assert_eq!(off, b"trap: bounds at a.fors:3:4\n");

        unsafe { std::env::set_var(BACKTRACE_ENV, "0") };
        let mut zero = Vec::new();
        report_trap(&mut zero, TrapKind::Bounds, "a.fors", 3, 4, &frames()).unwrap();
        assert_eq!(zero, off, "only `1` enables it");

        unsafe { std::env::set_var(BACKTRACE_ENV, "1") };
        let mut on = Vec::new();
        report_trap(&mut on, TrapKind::Bounds, "a.fors", 3, 4, &frames()).unwrap();
        assert_eq!(on, b"trap: bounds at a.fors:3:4\n  0: main at 12:5\n");
        assert!(
            on.starts_with(&off[..]),
            "the fixed line is unchanged; the backtrace only follows it"
        );

        match previous {
            Some(v) => unsafe { std::env::set_var(BACKTRACE_ENV, v) },
            None => unsafe { std::env::remove_var(BACKTRACE_ENV) },
        }
    }

    #[test]
    fn a_ub_report_goes_through_the_same_site() {
        let _env = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let previous = std::env::var(BACKTRACE_ENV).ok();
        // SAFETY: same ownership-under-`ENV_LOCK` argument as the test above.
        unsafe { std::env::remove_var(BACKTRACE_ENV) };
        let r = UbReport::new(crate::ub::UbClass::LinearLeak, 4, (9, 2), "`v` is owed");
        let mut out = Vec::new();
        report_ub(&mut out, &r, "main.fors", &frames()).unwrap();
        assert_eq!(out, r.line("main.fors").as_bytes());
        match previous {
            Some(v) => unsafe { std::env::set_var(BACKTRACE_ENV, v) },
            None => unsafe { std::env::remove_var(BACKTRACE_ENV) },
        }
    }
}
