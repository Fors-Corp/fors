//! The runtime entry shim (design §5.3, §5.4, ch02 R17, ch10 R40(d)): the
//! host environment the dispatch loop reads ([`HostEnv`]), the one place a
//! `Stdout` byte reaches the operating system ([`host_write`]), and the
//! exit-status decision taken once `main` settles ([`entry_exit`]).
//!
//! F2's slice of ch10 R40(d)'s closed table: `main` returned and nothing
//! latched -> status 0; `main` returned but `Stdout` carries a latched
//! error -> status 2; a trap -> a signal status, never 0/1/2 (§5.3: the
//! trap path has no flush and no error line, dominating everything else).
//! **F4** added status 1 (`main` raised, ch02 R17): `errdefer` runs on error
//! exits and nowhere else (ch01 R23b), so F4 needed `Exit::Raise` to have an
//! error exit to test at all. What stays F3's is the CONTENT of that exit —
//! `render`'s `error: ` line and `?`/`try_br` — not the status.
//! **F6** added the `ub:` row at status [`crate::ub::UB_EXIT_STATUS`].
//!
//! A 536-line spike at
//! `/Users/marcfors/fors-wt/i35-i4/spikes/contracts/f2_contracts_shim.rs`
//! prototypes this same `entry_shim`/`ShimExit` shape (read-only, another
//! worktree); this module is written fresh against the REAL [`Outcome`]
//! type rather than copied in, per the task's "reuse its logic where it
//! fits the real crates, do not copy it in as a file".

use crate::exec::{Exit, Outcome};
use fors_fmir::op::TrapKind;

/// What the dispatch loop's host-effecting intrinsics see of the process
/// environment. `Default` is the oracle's case: `Stdout` is captured
/// in-process as an exact byte image and never touches a descriptor.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct HostEnv {
    /// `Some(fd)`: every `Stdout` `write_*` also goes through
    /// [`host_write`] to this real file descriptor, and a failed write —
    /// `EPIPE` from a pipe whose read end is closed, `EBADF`, a short
    /// write — LATCHES (ch10 R39) instead of trapping or appending to the
    /// captured image. This is how the conformance runner presents "the
    /// standard OUTPUT descriptor closed before `main`" (§7.2a,
    /// `tests/conformance/README.md`) to `main-returns-latched-stdout-
    /// exit-2` and `10-std/sigpipe-ignored-write-latches-run-error`: a
    /// real pipe with its read end closed, so the write only fails as
    /// `io.Error.closed` because [`install_sigpipe_ignore`] ran first.
    /// `None`: capture only.
    pub stdout_fd: Option<i32>,
}

/// Writes `bytes` whole to the raw descriptor `fd`. Any `Err` is the
/// caller's latching signal: ch10 R39 makes a `Stdout` write failure a
/// sticky flag, not a value, so the dispatch loop keeps only "latched" and
/// the OS error (`EPIPE`, `EBADF`, ...) stays here for a debugger. Partial
/// writes are retried until the buffer is out (`write_all`) and `EINTR` is
/// retried by std; anything else is a failure.
#[cfg(unix)]
pub fn host_write(fd: i32, bytes: &[u8]) -> std::io::Result<()> {
    use std::io::Write;
    use std::mem::ManuallyDrop;
    use std::os::fd::FromRawFd;

    // The caller owns `fd`; `ManuallyDrop` keeps `File`'s drop from
    // closing it. SAFETY: a `File` over a descriptor the caller keeps
    // open for the duration of this call; no other owner is created.
    let mut file = ManuallyDrop::new(unsafe { std::fs::File::from_raw_fd(fd) });
    file.write_all(bytes)
}

/// Non-Unix targets have no raw descriptor to write through: a
/// `stdout_fd` there is a write that cannot arrive, i.e. a latch.
#[cfg(not(unix))]
pub fn host_write(_fd: i32, _bytes: &[u8]) -> std::io::Result<()> {
    Err(std::io::Error::from(std::io::ErrorKind::Unsupported))
}

/// The process's final observable status: an ordinary exit code, or a
/// trap's signal status (never a 0/1/2 exit code — §5.3, ch10 R40(d)).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExitStatus {
    Status(i32),
    Trap(TrapKind),
}

/// Ch10 R40(d)'s exit-status table, restricted to what F2 can produce:
///
/// | `outcome.exit` | `stdout_latched` | status |
/// |---|---|---|
/// | `Trap(k)` | (irrelevant) | `Trap(k)` — dominates everything (§5.3) |
/// | `Return` | `false` | `Status(0)` |
/// | `Return` | `true` | `Status(2)` |
///
/// F4 adds the `raise` row (status 1, ch02 R17(c): "Exit status 1, whether
/// or not 3 or 4 succeeded") because it needs an ERROR EXIT to run an
/// `errdefer` on at all; `render`'s `error: ` line stays F3's. F6 adds the
/// `ub:` row: design §5.2's "A `ub:` diagnostic exits with status
/// [`crate::ub::UB_EXIT_STATUS`]", which is an ordinary exit code and
/// deliberately NOT a new [`ExitStatus`] variant — ch02 R15's eight trap
/// kinds stay the only non-code outcome (E4).
pub fn entry_exit(outcome: &Outcome) -> ExitStatus {
    match outcome.exit {
        Exit::Trap(k) => ExitStatus::Trap(k),
        Exit::Ub(_) => ExitStatus::Status(crate::ub::UB_EXIT_STATUS),
        Exit::Raise => ExitStatus::Status(1),
        Exit::Return if outcome.stdout_latched => ExitStatus::Status(2),
        Exit::Return => ExitStatus::Status(0),
    }
}

/// `SIGPIPE`'s number and `SIG_IGN`'s value, both fixed by POSIX for the
/// platforms this crate builds on (shared with the conformance runner,
/// which resets the disposition to default before proving the shim's
/// install is what keeps the process alive).
#[cfg(unix)]
pub const SIGPIPE: i32 = 13;
#[cfg(unix)]
pub const SIG_IGN: usize = 1;
#[cfg(unix)]
pub const SIG_DFL: usize = 0;

#[cfg(unix)]
unsafe extern "C" {
    /// The platform's own `signal(2)`; every Unix binary already links
    /// against libc, so no `libc` crate is needed (zero-dependency).
    fn signal(signum: i32, handler: usize) -> usize;
}

/// Sets `SIGPIPE`'s disposition to `handler` (`SIG_IGN`/`SIG_DFL`) and
/// returns the previous one. Exposed so the conformance runner can prove
/// [`install_sigpipe_ignore`] matters (it resets to `SIG_DFL` first).
#[cfg(unix)]
pub fn set_sigpipe(handler: usize) -> usize {
    // SAFETY: `signal(2)` with a valid signal number and one of the two
    // well-known dispositions; it has no memory-safety preconditions.
    unsafe { signal(SIGPIPE, handler) }
}

/// Installs `SIG_IGN` for `SIGPIPE` (ch02 R17, ch10 R40(d)): "The runtime
/// entry shim installs `SIG_IGN` for `SIGPIPE` before `main` runs, so a
/// write to a closed pipe fails as an ordinary `io.Error.closed` ... and
/// cannot end the process by a signal here." A real OS-process entry point
/// (the eventual `fors run`) calls this once before invoking
/// [`crate::exec::run`]; the conformance runner calls it before handing a
/// closed pipe's write end to [`HostEnv::stdout_fd`].
#[cfg(unix)]
pub fn install_sigpipe_ignore() {
    set_sigpipe(SIG_IGN);
}

/// Non-Unix targets have no `SIGPIPE` to ignore.
#[cfg(not(unix))]
pub fn install_sigpipe_ignore() {}

#[cfg(test)]
mod tests {
    use super::*;

    fn outcome(exit: Exit, stdout_latched: bool) -> Outcome {
        Outcome {
            exit,
            stdout: Vec::new(),
            stdout_latched,
            site: None,
            ub: None,
            backtrace: Vec::new(),
        }
    }

    #[test]
    fn a_raise_out_of_main_is_status_1() {
        // ch02 R17(c), and F4's reason for needing an error exit at all.
        assert_eq!(
            entry_exit(&outcome(Exit::Raise, false)),
            ExitStatus::Status(1)
        );
        assert_eq!(
            entry_exit(&outcome(Exit::Raise, true)),
            ExitStatus::Status(1)
        );
    }

    #[test]
    fn a_ub_report_is_status_70_and_never_a_trap() {
        // design §5.2 / E4: "a compiler bug must not look like a program
        // trap". There is no `ExitStatus::Trap` on this path for any class.
        for class in crate::ub::UbClass::ALL {
            let status = entry_exit(&outcome(Exit::Ub(class), false));
            assert_eq!(status, ExitStatus::Status(crate::ub::UB_EXIT_STATUS));
            assert!(!matches!(status, ExitStatus::Trap(_)));
        }
    }

    // -- the exit table, every row -----------------------------------------

    #[test]
    fn clean_return_is_status_0() {
        assert_eq!(
            entry_exit(&outcome(Exit::Return, false)),
            ExitStatus::Status(0)
        );
    }

    #[test]
    fn latched_stdout_on_return_is_status_2() {
        // ch10 R40(d): "main returned but the final flush failed or an
        // error was latched on Stdout" -> status 2, not 1.
        assert_eq!(
            entry_exit(&outcome(Exit::Return, true)),
            ExitStatus::Status(2)
        );
    }

    #[test]
    fn trap_is_never_a_0_1_2_status() {
        for &k in &[
            TrapKind::Bounds,
            TrapKind::Overflow,
            TrapKind::DivZero,
            TrapKind::Shift,
            TrapKind::CheckedConversion,
            TrapKind::ArenaGeneration,
            TrapKind::Contract,
            TrapKind::EmptyReduce,
        ] {
            assert_eq!(
                entry_exit(&outcome(Exit::Trap(k), false)),
                ExitStatus::Trap(k)
            );
        }
    }

    #[test]
    fn trap_dominates_a_simultaneous_latch() {
        // §5.3: a trap has no successor and never reaches the entry
        // shim's flush; a latch that happened earlier in the same run
        // changes nothing about the trap's own status.
        assert_eq!(
            entry_exit(&outcome(Exit::Trap(TrapKind::Bounds), true)),
            ExitStatus::Trap(TrapKind::Bounds)
        );
    }

    // -- SIGPIPE ------------------------------------------------------------

    #[test]
    #[cfg(unix)]
    fn sigpipe_ignore_is_idempotent_and_sticks() {
        // `signal` returns the PREVIOUS handler; after the install, a
        // second call's return value must be `SIG_IGN`, confirming the
        // ignore actually took effect rather than merely not panicking.
        install_sigpipe_ignore();
        let previous = set_sigpipe(SIG_IGN);
        assert_eq!(previous, SIG_IGN, "SIGPIPE must already be SIG_IGN");
    }

    #[test]
    #[cfg(unix)]
    fn host_write_to_a_closed_pipe_fails_instead_of_killing_the_process() {
        // The real mechanism the two closed-pipe gate tests rely on: with
        // `SIG_IGN` installed, a write to a pipe whose read end is gone
        // comes back as an error (`EPIPE`) rather than a `SIGPIPE` death.
        use std::os::fd::AsRawFd;
        install_sigpipe_ignore();
        let (reader, writer) = std::io::pipe().expect("a pipe");
        drop(reader);
        let err = host_write(writer.as_raw_fd(), b"gone\n").expect_err("EPIPE");
        assert_eq!(err.kind(), std::io::ErrorKind::BrokenPipe);
        // And an open pipe carries the bytes through, whole.
        let (mut reader, writer) = std::io::pipe().expect("a pipe");
        host_write(writer.as_raw_fd(), b"ok\n").expect("an open pipe");
        drop(writer);
        let mut got = Vec::new();
        std::io::Read::read_to_end(&mut reader, &mut got).unwrap();
        assert_eq!(got, b"ok\n");
    }
}
