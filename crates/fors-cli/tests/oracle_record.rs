//! F10's `OracleRecord` through the real binary (design §7.1, §7.2):
//! `fors run --oracle-run-record <file>` writes the complete record of the
//! run, and `--oracle-replay <record>` serves its host section and compares
//! the new run's record with it, field by field.
//!
//! GATE (design §9 F10): `record_is_deterministic_over_100_runs` — 100 live
//! runs of a program that reads no host response give 100 byte-identical
//! records (stdout, stderr, exit and STEP COUNT included), and a program that
//! reads the clock and entropy, recorded once, replays 100 times to the same
//! record byte for byte.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("fors-runrec-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("scratch dir");
    d
}

fn fors(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fors"))
        .args(args)
        .current_dir(repo_root())
        .env_remove("FORS_BACKTRACE")
        .output()
        .expect("fors runs")
}

/// Reads the clock twice, draws entropy, and writes to BOTH streams before
/// raising out of `main`: every record section is non-trivial.
const HOST_PROBE: &str = "\
module app;
needs { clock, rng, io.stdout, io.stderr };
use std.time, std.rand, std.io;

enum E { done }

fn main(let c: time.Clock, inout r: rand.Rng, inout out: io.Stdout, inout err: io.Stderr) raises E {
    let a: time.Instant = c.now();
    out.write_uint(r.u64());
    out.write_line(\"\");
    let b: time.Instant = c.now();
    let d: time.Duration = b.since(a);
    out.write_uint(d.nanos);
    out.write_line(\"\");
    err.write_line(\"to stderr\");
    raise E.done;
}
";

#[test]
fn record_is_deterministic_over_100_runs() {
    let dir = scratch("det");
    // (1) No host responses: 100 live runs, one record. The program writes
    // stdout and stderr and exits through ch02 R17's error line.
    let corpus = "tests/conformance/02-failure/main-raises-after-defer-run-error.fors";
    let mut first: Option<Vec<u8>> = None;
    for i in 0..100 {
        let rec = dir.join(format!("live-{i}.record"));
        let o = fors(&["run", "--oracle-run-record", rec.to_str().unwrap(), corpus]);
        assert_eq!(
            o.status.code(),
            Some(1),
            "{}",
            String::from_utf8_lossy(&o.stderr)
        );
        let bytes = std::fs::read(&rec).expect("record written");
        match &first {
            None => {
                let text = String::from_utf8_lossy(&bytes);
                assert!(text.starts_with("fors-run-record 1\nprogram "), "{text}");
                assert!(text.contains("\nexit status 1\n"), "{text}");
                assert!(
                    text.ends_with("stderr 32\ndeferred\nerror: main.Error.boom\n\n"),
                    "{text}"
                );
                first = Some(bytes);
            }
            Some(f) => assert_eq!(&bytes, f, "live run {i} recorded different bytes"),
        }
    }

    // (2) Host responses: recorded once, replayed 100 times.
    let prog = dir.join("probe.fors");
    std::fs::write(&prog, HOST_PROBE).unwrap();
    let prog_s = prog.to_str().unwrap();
    let rec = dir.join("probe.record");
    let rec_s = rec.to_str().unwrap();
    let live = fors(&["run", "--oracle-run-record", rec_s, prog_s]);
    assert_eq!(
        live.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&live.stderr)
    );
    let recorded = std::fs::read(&rec).expect("record written");
    let text = String::from_utf8_lossy(&recorded);
    assert!(text.contains("\nhost 3\nmono "), "{text}");
    for i in 0..100 {
        let again = dir.join(format!("replay-{i}.record"));
        let o = fors(&[
            "run",
            "--oracle-replay",
            rec_s,
            "--oracle-run-record",
            again.to_str().unwrap(),
            prog_s,
        ]);
        assert_eq!(
            o.status.code(),
            Some(1),
            "{}",
            String::from_utf8_lossy(&o.stderr)
        );
        assert_eq!(o.stdout, live.stdout, "replay {i}: stdout");
        assert_eq!(o.stderr, live.stderr, "replay {i}: stderr");
        let bytes = std::fs::read(&again).expect("record written");
        assert_eq!(bytes, recorded, "replay {i} recorded different bytes");
    }
}

/// A record whose observable section the replay does not reproduce is the
/// named mismatch, exit 69 — never a silent pass.
#[test]
fn a_replay_that_does_not_reproduce_its_record_is_a_named_mismatch() {
    let dir = scratch("mismatch");
    let corpus = "tests/conformance/02-failure/main-raises-after-defer-run-error.fors";
    let rec = dir.join("r.record");
    let rec_s = rec.to_str().unwrap();
    assert_eq!(
        fors(&["run", "--oracle-run-record", rec_s, corpus])
            .status
            .code(),
        Some(1)
    );
    let good = std::fs::read_to_string(&rec).unwrap();
    for (what, from, to, field) in [
        ("stderr byte", "deferred\n", "deferrex\n", "stderr"),
        ("exit", "exit status 1\n", "exit status 0\n", "exit"),
        ("step count", "\nsteps ", "\nsteps 1", "steps"),
    ] {
        let bad = good.replacen(from, to, 1);
        assert_ne!(bad, good, "{what}");
        std::fs::write(&rec, &bad).unwrap();
        let o = fors(&["run", "--oracle-replay", rec_s, corpus]);
        let err = String::from_utf8_lossy(&o.stderr);
        assert_eq!(o.status.code(), Some(69), "{what}: {err}");
        assert!(
            err.contains(&format!("oracle: record mismatch: `{field}`")),
            "{what}: {err}"
        );
    }
    // A record for ANOTHER program is refused on its program digest.
    std::fs::write(&rec, &good).unwrap();
    let o = fors(&[
        "run",
        "--oracle-replay",
        rec_s,
        "tests/conformance/02-failure/main-raises-unit-variant-run-error.fors",
    ]);
    assert_eq!(o.status.code(), Some(69));
    assert!(String::from_utf8_lossy(&o.stderr).contains("record mismatch: `program`"));
}
