//! The native differential's VACUITY checks (`docs/design/m2-dev-backend.md`
//! §5, §10 preamble: "does the native runner really execute native code; do
//! mutations get caught"; "refusals are counted, not dropped").
//!
//! - With a deliberately wrong stencil armed (`fors-codegen-dev`'s test-only
//!   `inject-miscompile` feature, enabled ONLY from this crate's
//!   `[dev-dependencies]`), the straight-line corpus must produce
//!   `mismatch` rows — so an `ok` really is native output agreeing with the
//!   interpreter, not a runner that compares the interpreter with itself.
//! - The full profile (branches, loops, helpers: outside M2-0's surface)
//!   must land in `refused`, every program classified exactly once.
//!
//! The mutation switch is process-global, so these tests live in their own
//! binary and run one at a time (`--test-threads` is irrelevant: the
//! mutation tests serialise on a lock).

use std::sync::Mutex;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use fors_codegen_dev::inject::Mutation;
use fors_codegen_dev::inject::arm;
use fors_oracle::generate::Profile;
use fors_oracle::native_diff::run_seeds;

static ARMED: Mutex<()> = Mutex::new(());

/// Only `fors-oracle`'s `[dev-dependencies]` may enable the feature.
#[test]
fn inject_miscompile_is_enabled_only_by_oracle_dev_deps() {
    let crates = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    for e in std::fs::read_dir(&crates).unwrap() {
        let m = e.unwrap().path().join("Cargo.toml");
        let Ok(text) = std::fs::read_to_string(&m) else {
            continue;
        };
        let name = m
            .parent()
            .unwrap()
            .file_name()
            .unwrap()
            .to_string_lossy()
            .into_owned();
        for (i, line) in text.lines().enumerate() {
            if line.trim_start().starts_with('#') || !line.contains("\"inject-miscompile\"") {
                continue;
            }
            let section = text
                .lines()
                .take(i)
                .filter(|l| l.starts_with('['))
                .last()
                .unwrap_or("");
            assert!(
                name == "fors-oracle" && section == "[dev-dependencies]",
                "{name} enables inject-miscompile in {section}"
            );
        }
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn mutated_mismatches(m: Mutation, seeds: std::ops::Range<u64>) -> fors_oracle::native_diff::Tally {
    let _g = ARMED.lock().unwrap_or_else(|p| p.into_inner());
    arm(Some(m));
    let n = seeds.end - seeds.start;
    let t = run_seeds(seeds, &Profile::STRAIGHT_LINE);
    arm(None);
    println!("{m:?}: {}", t.line());
    for (seed, v) in t.failures.iter().take(5) {
        println!("  seed {seed}: {} {v:?}", v.class());
    }
    assert_eq!(t.total(), n, "every program classified once");
    t
}

/// Seeds per mutation run. `WrapAddIsSub` flips 47 of the first 100
/// straight-line seeds, `XorIsOr` 97, so 20 seeds miss a live mutation with
/// probability below 1e-5 — and each seed is one ~0.35 s native exec.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const SEEDS: std::ops::Range<u64> = 0..20;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn a_wrong_add_stencil_produces_mismatch_rows() {
    let t = mutated_mismatches(Mutation::WrapAddIsSub, SEEDS);
    assert!(
        t.mismatch > 0,
        "a wrong stencil went unnoticed: {}",
        t.line()
    );
    // A mutation changes printed values, never the classes around them.
    assert_eq!(
        t.refused + t.compile_panic + t.spawn_fail + t.timeout + t.oracle_fail,
        0
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn a_wrong_xor_stencil_produces_mismatch_rows() {
    let t = mutated_mismatches(Mutation::XorIsOr, SEEDS);
    assert!(
        t.mismatch > 0,
        "a wrong stencil went unnoticed: {}",
        t.line()
    );
}

/// With nothing armed the same seeds are all `ok` (the control).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn unmutated_control_is_clean() {
    let _g = ARMED.lock().unwrap_or_else(|p| p.into_inner());
    arm(None);
    let t = run_seeds(SEEDS, &Profile::STRAIGHT_LINE);
    println!("control: {}", t.line());
    assert_eq!(t.ok, SEEDS.end - SEEDS.start);
}

/// Programs outside M2-0's surface are refused BY NAME and counted.
#[test]
fn refusals_are_counted_not_dropped() {
    let _g = ARMED.lock().unwrap_or_else(|p| p.into_inner());
    arm(None);
    let t = run_seeds(0..40, &Profile::FULL);
    println!("full profile: {}", t.line());
    for (seed, v) in t.failures.iter().take(3) {
        println!("  seed {seed}: {} {v:?}", v.class());
    }
    assert_eq!(t.total(), 40, "every program classified exactly once");
    assert!(
        t.refused > 0,
        "the full profile is refused (branches, loops, calls)"
    );
    assert_eq!(
        t.mismatch + t.compile_panic + t.signal + t.timeout + t.oracle_fail,
        0
    );
    // Every refusal names its reason.
    for (_, v) in &t.failures {
        if let fors_oracle::native_diff::NativeVerdict::Refused(why) = v {
            assert!(why.starts_with("refused: decl "), "{why}");
        }
    }
}

/// Every class of the comparison is reachable and lands where §5 says.
#[test]
fn compare_classifies_every_exit_shape() {
    use fors_fmir::op::TrapKind;
    use fors_interp::{OracleRecord, RecordExit};
    use fors_oracle::native::{NativeExit, NativeRecord, SIGTRAP};
    use fors_oracle::native_diff::{NativeVerdict, compare};
    let rec = |exit, out: &[u8], err: &[u8]| OracleRecord {
        program: 0,
        target: 0,
        exit,
        steps: 0,
        host: Vec::new(),
        stdout: out.to_vec(),
        stderr: err.to_vec(),
    };
    let nat = |exit, out: &[u8], err: &[u8]| NativeRecord {
        exit,
        stdout: out.to_vec(),
        stderr: err.to_vec(),
    };
    let trap = RecordExit::Trap {
        kind: TrapKind::Overflow,
        site: 1,
    };
    let ok = RecordExit::Status(0);
    let cases = [
        (
            rec(ok, b"1\n", b""),
            nat(NativeExit::Status(0), b"1\n", b""),
            NativeVerdict::Ok,
        ),
        (
            rec(ok, b"1\n", b""),
            nat(NativeExit::Status(0), b"2\n", b""),
            NativeVerdict::Mismatch("stdout".into()),
        ),
        (
            rec(ok, b"", b""),
            nat(NativeExit::Status(3), b"", b""),
            NativeVerdict::Mismatch("exit".into()),
        ),
        (
            rec(ok, b"", b""),
            nat(NativeExit::Signal(11), b"", b""),
            NativeVerdict::Signal(11),
        ),
        (
            rec(ok, b"", b""),
            nat(NativeExit::Signal(SIGTRAP), b"", b""),
            NativeVerdict::Signal(SIGTRAP),
        ),
        (
            rec(trap, b"a\n", b"trap: overflow at m.fors:1:2\n"),
            nat(NativeExit::Signal(SIGTRAP), b"a\n", b""),
            NativeVerdict::Ok,
        ),
        (
            rec(trap, b"", b"x\ntrap: overflow at m.fors:1:2\n"),
            nat(NativeExit::Signal(SIGTRAP), b"", b"x\n"),
            NativeVerdict::Ok,
        ),
        (
            rec(trap, b"", b"trap: overflow at m.fors:1:2\n"),
            nat(NativeExit::Status(0), b"", b""),
            NativeVerdict::Mismatch("exit".into()),
        ),
        (
            rec(ok, b"", b"e\n"),
            nat(NativeExit::Status(0), b"", b""),
            NativeVerdict::Mismatch("stderr".into()),
        ),
        (
            rec(ok, b"", b""),
            nat(NativeExit::Timeout, b"", b""),
            NativeVerdict::Timeout,
        ),
    ];
    for (i, n, want) in cases {
        assert_eq!(compare(&i, &n), want, "{:?} vs {:?}", i.exit, n.exit);
    }
}
