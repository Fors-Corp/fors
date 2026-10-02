//! F8 (design `fmir-interpreter.md` §7.2, §9 F8's GATE): `fors run
//! --oracle-record` then `--oracle-replay` gives two runs that are
//! byte-identical on stdout and exit status, and a replay that diverges from
//! its record is a NAMED error — never a silent divergence.
//!
//! The probe program prints a monotonic reading, an entropy draw and an
//! elapsed duration, so two LIVE runs differ (that is checked too): only the
//! replay makes the output a function of the record.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// A fresh scratch directory for one test (no `tempfile` crate: the
/// workspace takes no dependencies).
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("fors-oracle-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("scratch dir");
    d
}

fn fors(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fors"))
        .args(args)
        .output()
        .expect("fors runs")
}

const PROBE: &str = "\
module app;
needs { clock, rng, io.stdout };
use std.time, std.rand, std.io;

fn main(let c: time.Clock, inout r: rand.Rng, inout out: io.Stdout) {
    let a: time.Instant = c.now();
    out.write_uint(a.nanos);
    out.write_line(\"\");
    out.write_uint(r.u64());
    out.write_line(\"\");
    let b: time.Instant = c.now();
    let d: time.Duration = b.since(a);
    out.write_uint(d.nanos);
    out.write_line(\"\");
}
";

#[test]
fn record_then_replay_is_byte_identical_on_stdout_and_exit_status() {
    let dir = scratch("probe");
    let prog = dir.join("probe.fors");
    std::fs::write(&prog, PROBE).unwrap();
    let rec = dir.join("probe.record");
    let (prog_s, rec_s) = (prog.to_str().unwrap(), rec.to_str().unwrap());

    let recorded = fors(&["run", "--oracle-record", rec_s, prog_s]);
    assert_eq!(
        recorded.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&recorded.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&recorded.stdout).lines().count(), 3);
    let record = std::fs::read(&rec).expect("the record was written");
    assert!(record.starts_with(b"fors-oracle-record 1\nmono "));

    for _ in 0..2 {
        let replayed = fors(&["run", "--oracle-replay", rec_s, prog_s]);
        assert_eq!(replayed.stdout, recorded.stdout, "stdout bytes");
        assert_eq!(
            replayed.status.code(),
            recorded.status.code(),
            "exit status"
        );
        assert!(replayed.stderr.is_empty(), "{:?}", replayed.stderr);
    }

    // Two LIVE runs differ (a fresh entropy draw), which is what makes the
    // replay's equality meaningful.
    let live = fors(&["run", prog_s]);
    assert_eq!(live.status.code(), Some(0));
    assert_ne!(
        live.stdout, recorded.stdout,
        "two live runs printed the same draw"
    );
}

#[test]
fn a_corpus_clock_test_replays_identically() {
    let dir = scratch("corpus");
    let rec = dir.join("mono.record");
    let rec_s = rec.to_str().unwrap();
    let test = repo_root().join("tests/conformance/10-std/time-now-is-monotonic-run-ok.fors");
    let test_s = test.to_str().unwrap();
    let recorded = fors(&["run", "--oracle-record", rec_s, test_s]);
    assert_eq!(recorded.stdout, b"ok\n");
    assert_eq!(recorded.status.code(), Some(0));
    let replayed = fors(&["run", "--oracle-replay", rec_s, test_s]);
    assert_eq!(replayed.stdout, recorded.stdout);
    assert_eq!(replayed.status.code(), recorded.status.code());
}

#[test]
fn a_diverging_replay_is_a_named_error() {
    let dir = scratch("diverge");
    let prog = dir.join("probe.fors");
    std::fs::write(&prog, PROBE).unwrap();
    let prog_s = prog.to_str().unwrap();
    let cases: [(&str, &str, &str); 3] = [
        (
            "wrong kind first",
            "fors-oracle-record 1\nentropy 0000000000000001\nmono 1\nmono 2\n",
            "mismatch at entry 0",
        ),
        (
            "one entry short",
            "fors-oracle-record 1\nmono 1\nentropy 0000000000000001\n",
            "exhausted",
        ),
        (
            "one entry left over",
            "fors-oracle-record 1\nmono 1\nentropy 0000000000000001\nmono 2\nmono 3\n",
            "unconsumed",
        ),
    ];
    for (what, record, needle) in cases {
        let rec = dir.join("bad.record");
        std::fs::write(&rec, record).unwrap();
        let out = fors(&["run", "--oracle-replay", rec.to_str().unwrap(), prog_s]);
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(69), "{what}: {err}");
        assert!(
            err.contains("oracle") && err.contains(needle),
            "{what}: {err}"
        );
    }
    // A malformed record is refused before anything runs: no stdout at all.
    let rec = dir.join("malformed.record");
    std::fs::write(&rec, "mono 1\n").unwrap();
    let out = fors(&["run", "--oracle-replay", rec.to_str().unwrap(), prog_s]);
    assert_eq!(out.status.code(), Some(69));
    assert!(out.stdout.is_empty());
}

// ---------------------------------------------------------------------------
// F8's run-time backstops to ch04 R7/R8 (design §5.9), pinned through the
// CLI because each needs a build the library harness does not make.
// ---------------------------------------------------------------------------

/// A root module that calls itself `std.time` and declares its own `Clock`
/// with the `clock_mono` stand-in, built WITHOUT the real `std`: the
/// checker's A0007 does not fire on a struct literal inside the declaring
/// module (ch04 R7 says "in every module, std included" — a fors-check gap,
/// not this increment's), and lowering identifies the owner by module path
/// and so intercepts the stand-in. What holds R7 here is the interpreter's
/// receiver check: the door is reached with a value the entry shim did not
/// create, and the run ends in that named refusal with NO clock read
/// printed.
#[test]
fn a_forged_std_time_module_is_refused_at_the_door_not_served() {
    let dir = scratch("forged");
    let empty_std = dir.join("empty-std");
    std::fs::create_dir_all(&empty_std).unwrap();
    let prog = dir.join("forged.fors");
    std::fs::write(
        &prog,
        "module std.time;\nneeds { clock };\npub struct Clock { }\npub enum E { ticked }\n\
         impl Clock {\n    fn clock_mono(let self: Self) -> u64 {\n        return self.clock_mono();\n    }\n\
         pub fn now(let self: Self) -> u64 {\n        return self.clock_mono();\n    }\n}\n\
         fn main() raises E {\n    let c: Clock = Clock { };\n    if c.now() != 0 {\n        raise E.ticked;\n    }\n}\n",
    )
    .unwrap();
    let out = fors(&[
        "run",
        "--std",
        empty_std.to_str().unwrap(),
        prog.to_str().unwrap(),
    ]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(69), "{err}");
    assert!(out.stdout.is_empty());
    assert!(
        err.contains(
            "`clock_mono` reached with a receiver that is not the entry shim's `std.time.Clock` value"
        ),
        "{err}"
    );
}

/// `mem.Heap` is the twelfth root type (ch04 R21) and the one the shim
/// cannot yet supply END TO END: fors-check types a `main` parameter
/// `let h: mem.Heap` as the error type WITHOUT a diagnostic (`fors check`
/// is clean; ch10 R17's fresh-brand binding of `Heap[A: brand]` is not
/// implemented there), so lowering records no root identity for it and the
/// entry shim refuses the program BY NAME rather than inventing a value;
/// `inout h: mem.Heap` is refused one stage earlier, as lowering's named
/// `Unresolved` by-reference type. Pinned here so the day the checker types
/// it, this test — not a silent `()` argument — is what changes. Not this
/// increment's to fix (fors-check is owned by a parallel checker increment).
#[test]
fn a_main_taking_mem_heap_is_refused_by_name_until_the_checker_types_it() {
    let dir = scratch("heap");
    let by_value = dir.join("heap-let.fors");
    std::fs::write(
        &by_value,
        "module app;\nneeds { io.stdout };\nuse std.io, std.mem;\n\
         fn main(inout out: io.Stdout, let h: mem.Heap) {\n    out.write_line(\"ok\");\n}\n",
    )
    .unwrap();
    let out = fors(&["run", by_value.to_str().unwrap()]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(69), "{err}");
    assert!(out.stdout.is_empty(), "main ran: {:?}", out.stdout);
    assert!(
        err.contains("`main` parameter 1 is not one of ch04 R21's twelve root-capability types"),
        "{err}"
    );

    let by_ref = dir.join("heap-inout.fors");
    std::fs::write(
        &by_ref,
        "module app;\nneeds { io.stdout };\nuse std.io, std.mem;\n\
         fn main(inout out: io.Stdout, inout h: mem.Heap) {\n    out.write_line(\"ok\");\n}\n",
    )
    .unwrap();
    let out = fors(&["run", by_ref.to_str().unwrap()]);
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(65), "{err}");
    assert!(
        err.contains("`main` does not lower") && err.contains("by-reference parameter"),
        "{err}"
    );
}
