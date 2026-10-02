//! F9's GATE (design `fmir-interpreter.md` §9 F9), run through the
//! interpreter AS A BUILD STEP: `fors build` — parse, resolve, check, lower,
//! then every `comptime` block evaluated by the FMIR interpreter in comptime
//! mode, its diagnostics reported with the checker's.
//!
//! The five ch04 corpus files each reach their expected verdict. Two of
//! them cannot reach it through the rule they cite AS WRITTEN, and each is
//! pinned with the exact reason beside a twin probe that does exercise the
//! rule through the interpreter (the corpus is ground truth and is not
//! edited here):
//! - `comptime-clock-read-rejected` writes `Clock` unqualified with no
//!   `use std.time;`. `Clock` is not one of ch10 R2's prelude names, so with
//!   `std` in the build the resolver stops at `N0014` and nothing is lowered
//!   (the verdict, `check-error`, holds). Its twin names `time.Clock`.
//! - `comptime-file-read-declared-accepted` declares its read with
//!   `@comptime_input(".config")`, which no chapter defines; ch04 R13 and
//!   ch10 R42 name the header's `inputs { ".config" };` clause. So the read
//!   IS undeclared: the checker says `A0013` and so does the comptime
//!   evaluator. Its directive is `parse-ok`, which holds. Its twin writes
//!   the `inputs` clause and builds clean, reading `.config` through the
//!   declared-inputs map.
//!
//! Then the three named tests: `comptime_memo_is_content_addressed`,
//! `comptime_result_identical_across_processes` (two separate processes,
//! byte-identical memo entries) — `address_observation_blocks_tierup` is
//! FMIR-level, in `fors-interp/tests/comptime.rs` — and the GATE's
//! COUNTERS: steps and bytes per evaluation and the memo hit rate.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn corpus(rel: &str) -> String {
    repo_root()
        .join("tests/conformance/04-authority")
        .join(rel)
        .to_string_lossy()
        .into_owned()
}

/// A fresh scratch directory (no `tempfile` crate: the workspace takes no
/// dependencies).
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("fors-f9-{}-{name}", std::process::id()));
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

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// The `error[CODE]` codes of a build's stderr, in order.
fn codes(out: &Output) -> Vec<String> {
    text(&out.stderr)
        .lines()
        .filter_map(|l| {
            let i = l.find("error[")?;
            let rest = &l[i + 6..];
            Some(rest[..rest.find(']')?].to_string())
        })
        .collect()
}

/// The comptime error lines (the evaluator's, not the checker's).
fn comptime_lines(out: &Output) -> Vec<String> {
    text(&out.stderr)
        .lines()
        .filter(|l| l.contains("comptime evaluation of"))
        .map(str::to_string)
        .collect()
}

/// One `--counters` evaluation line.
#[derive(Debug, Clone)]
struct Counter {
    steps: u64,
    bytes: u64,
    hit: bool,
    key: Option<String>,
}

fn counters(out: &Output) -> Vec<Counter> {
    text(&out.stdout)
        .lines()
        .filter(|l| l.starts_with("comptime ") && !l.starts_with("comptime memo:"))
        .map(|l| {
            let field = |k: &str| {
                l.split_whitespace()
                    .find_map(|w| w.strip_prefix(k))
                    .map(str::to_string)
            };
            Counter {
                steps: field("steps=")
                    .and_then(|v| v.parse().ok())
                    .expect("steps="),
                bytes: field("bytes=")
                    .and_then(|v| v.parse().ok())
                    .expect("bytes="),
                hit: field("memo=").as_deref() == Some("hit"),
                key: field("key="),
            }
        })
        .collect()
}

const EXIT_BUILD: i32 = 65;

// -- the five corpus files -----------------------------------------------------

/// ch04 R14: a 10^8-iteration loop exceeds `COMPTIME_STEP_BUDGET` (2^20).
/// The CHECKER is silent on this file (fors-check's `PENDING_04` hands R14
/// to F9: counting steps is evaluation, which R11 keeps out of the
/// checker), so the verdict is the interpreter's alone: `A0014`, naming
/// `setup`, with the counts.
#[test]
fn gate_comptime_budget_exceeded_rejected() {
    let out = fors(&[
        "build",
        "--counters",
        &corpus("comptime-budget-exceeded-rejected.fors"),
    ]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD), "{}", text(&out.stderr));
    assert_eq!(codes(&out), vec!["A0014"], "{}", text(&out.stderr));
    let line = &comptime_lines(&out)[0];
    assert!(line.contains("`setup`"), "names the declaration: {line}");
    assert!(line.contains("COMPTIME_STEP_BUDGET"), "{line}");
    assert!(
        line.contains("1048577 steps charged against a budget of 1048576"),
        "{line}"
    );
    assert!(
        line.contains(":10:5:"),
        "points at the `comptime` keyword: {line}"
    );
    let c = counters(&out);
    assert_eq!(c.len(), 1);
    assert_eq!(c[0].steps, (1 << 20) + 1);
}

/// ch04 R12, AS WRITTEN: `Clock` is unresolved (see the module docs), so
/// the build is rejected at resolution — the expected `check-error` — and
/// no comptime evaluation happens. Pinned, with the twin below.
#[test]
fn gate_comptime_clock_read_rejected() {
    let out = fors(&[
        "build",
        "--counters",
        &corpus("comptime-clock-read-rejected.fors"),
    ]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD));
    assert_eq!(
        codes(&out),
        vec!["N0014"],
        "PINNED: the file writes `Clock` with no `use std.time;` and ch10 R2's prelude has no \
         `Clock`, so with std in the build resolution stops first: {}",
        text(&out.stderr)
    );
    assert!(
        text(&out.stderr).contains(":9:17:"),
        "the `Clock` of `c: Clock`"
    );
    assert!(counters(&out).is_empty(), "nothing reached the evaluator");
}

const CLOCK_TWIN: &str = "\
module app;
needs { clock };
use std.time;

fn setup(let c: time.Clock) {
    comptime {
        let t = c.now();
    }
}
";

/// The clock twin, through the interpreter: the checker's `A0012` (the
/// block reaches the run-time parameter `c`) AND the evaluator's `A0012` —
/// in comptime mode `c` is a WITHHELD capability (the table is empty), and
/// `Clock.now` reaches the `clock_mono` door, which the intrinsic table's
/// comptime column forbids: a build error naming the intrinsic, never a
/// clock read.
#[test]
fn gate_comptime_clock_read_twin_is_named_by_the_interpreter() {
    let dir = scratch("clock");
    let p = dir.join("clock.fors");
    std::fs::write(&p, CLOCK_TWIN).unwrap();
    let out = fors(&["build", "--counters", p.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD));
    assert_eq!(codes(&out), vec!["A0012", "A0012"], "{}", text(&out.stderr));
    let line = &comptime_lines(&out)[0];
    assert!(line.contains("intrinsic `clock_mono`"), "{line}");
    assert!(line.contains("ch04 R12"), "{line}");
}

/// ch04 R13, AS WRITTEN: `parse-ok` holds; the build pins `A0013` twice
/// (checker and evaluator), because `@comptime_input` is not the header's
/// `inputs` clause (see the module docs).
#[test]
fn gate_comptime_file_read_declared_accepted() {
    let path = corpus("comptime-file-read-declared-accepted.fors");
    let parsed = fors(&["parse", &path]);
    assert_eq!(
        parsed.status.code(),
        Some(0),
        "the directive's verdict: parse-ok"
    );
    let out = fors(&["build", "--counters", &path]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD));
    assert_eq!(
        codes(&out),
        vec!["A0013", "A0013"],
        "PINNED: `@comptime_input(\".config\")` is defined by no chapter; ch04 R13 / ch10 R42 \
         declare a read in the header's `inputs {{ \".config\" }};` clause, which this file \
         does not write: {}",
        text(&out.stderr)
    );
    let line = &comptime_lines(&out)[0];
    assert!(
        line.contains("intrinsic `input_read`") && line.contains("\".config\""),
        "{line}"
    );
}

const DECLARED_TWIN: &str = "\
module app;
needs { };
inputs { \".config\" };
use std.fs;

fn setup() {
    comptime {
        let data: Str = fs.read_to_string(\".config\");
    }
}
";

/// The declared twin: the header's `inputs` clause lists `.config`, the
/// build reads it ONCE, content-hashes it, and the evaluator serves it from
/// the declared-inputs map — accepted, with the counters printed.
#[test]
fn gate_comptime_file_read_declared_twin_is_accepted() {
    let dir = scratch("declared");
    let p = dir.join("declared.fors");
    std::fs::write(&p, DECLARED_TWIN).unwrap();
    std::fs::write(dir.join(".config"), "mode = fast\n").unwrap();
    let out = fors(&["build", "--counters", p.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let c = counters(&out);
    assert_eq!(c.len(), 1);
    assert!(c[0].steps > 0 && c[0].bytes >= 12, "{c:?}");
    // A declared input that is missing is a BUILD error (ch10 R42: total).
    std::fs::remove_file(dir.join(".config")).unwrap();
    let out = fors(&["build", p.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD));
    assert_eq!(codes(&out), vec!["A0013"]);
    assert!(text(&out.stderr).contains("cannot be read"));
}

/// ch04 R13: the read is undeclared; the checker's `A0013` and the
/// evaluator's (`input_read` of an undeclared path) together.
#[test]
fn gate_comptime_file_read_undeclared_rejected() {
    let out = fors(&[
        "build",
        "--counters",
        &corpus("comptime-file-read-undeclared-rejected.fors"),
    ]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD));
    assert_eq!(codes(&out), vec!["A0013", "A0013"], "{}", text(&out.stderr));
    let line = &comptime_lines(&out)[0];
    assert!(line.contains("intrinsic `input_read`"), "{line}");
    assert!(line.contains("not declared"), "{line}");
}

/// ch04 R2a/R12: comptime reaching the ffi-sealed extern `probe` — the
/// checker's `A0002` and the evaluator's, which names the sealed call.
#[test]
fn gate_sealed_op_at_comptime_rejected() {
    let out = fors(&[
        "build",
        "--counters",
        &corpus("sealed-op-at-comptime-rejected.fors"),
    ]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD));
    assert_eq!(codes(&out), vec!["A0002", "A0002"], "{}", text(&out.stderr));
    let line = &comptime_lines(&out)[0];
    assert!(line.contains("sealed operation `probe`"), "{line}");
}

// -- the memo ---------------------------------------------------------------

/// Builds `src` (with `.config` = `config`) in `dir` against `memo`,
/// returning the one evaluation's counter.
fn build_declared(dir: &Path, src: &str, config: &str, memo: &Path) -> Counter {
    let p = dir.join("m.fors");
    std::fs::write(&p, src).unwrap();
    std::fs::write(dir.join(".config"), config).unwrap();
    let out = fors(&[
        "build",
        "--counters",
        "--memo-dir",
        memo.to_str().unwrap(),
        p.to_str().unwrap(),
    ]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    let c = counters(&out);
    assert_eq!(c.len(), 1, "{}", text(&out.stdout));
    c[0].clone()
}

fn with_other(body: &str, other: i64) -> String {
    format!("{body}\nfn other() -> i64 {{\n    return {other};\n}}\n")
}

/// design §6 / §10.2: the memo is keyed by CONTENT. Rebuilding the same
/// sources hits; editing a declaration the block cannot reach still hits
/// (same key); editing the declared input's bytes, or the block itself,
/// misses with a new key.
#[test]
fn comptime_memo_is_content_addressed() {
    let dir = scratch("memo");
    let memo = dir.join("memo");
    let base = with_other(DECLARED_TWIN, 1);
    let a = build_declared(&dir, &base, "mode = fast\n", &memo);
    assert!(!a.hit, "cold");
    let again = build_declared(&dir, &base, "mode = fast\n", &memo);
    assert!(again.hit && again.key == a.key, "warm: {again:?}");
    let unrelated = build_declared(&dir, &with_other(DECLARED_TWIN, 2), "mode = fast\n", &memo);
    assert!(
        unrelated.hit && unrelated.key == a.key,
        "an edit outside the block's call graph keeps the key: {unrelated:?}"
    );
    let input = build_declared(&dir, &base, "mode = slow\n", &memo);
    assert!(!input.hit && input.key != a.key, "input bytes: {input:?}");
    let edited = with_other(
        &DECLARED_TWIN.replace(
            "let data: Str = fs.read_to_string(\".config\");",
            "let data: Str = fs.read_to_string(\".config\");\n        let n: i64 = 7;",
        ),
        1,
    );
    let body = build_declared(&dir, &edited, "mode = fast\n", &memo);
    assert!(!body.hit && body.key != a.key, "block edit: {body:?}");
    let entries = std::fs::read_dir(&memo).unwrap().count();
    assert_eq!(entries, 3, "one persisted entry per distinct key");
}

/// The memo's reproducibility claim (ch06): two SEPARATE processes, each
/// with its own memo directory, write the same key and byte-identical
/// entries.
#[test]
fn comptime_result_identical_across_processes() {
    let dir = scratch("procs");
    let p = dir.join("declared.fors");
    std::fs::write(&p, DECLARED_TWIN).unwrap();
    std::fs::write(dir.join(".config"), "mode = fast\n").unwrap();
    let mut dumps = Vec::new();
    for run in ["one", "two"] {
        let memo = dir.join(run);
        let out = fors(&[
            "build",
            "--memo-dir",
            memo.to_str().unwrap(),
            p.to_str().unwrap(),
        ]);
        assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
        let mut files: Vec<(String, Vec<u8>)> = std::fs::read_dir(&memo)
            .unwrap()
            .map(|e| {
                let e = e.unwrap();
                (
                    e.file_name().to_string_lossy().into_owned(),
                    std::fs::read(e.path()).unwrap(),
                )
            })
            .collect();
        files.sort();
        assert_eq!(files.len(), 1);
        dumps.push(files);
    }
    assert_eq!(
        dumps[0], dumps[1],
        "byte-identical memo entries across processes"
    );
}

// -- COUNTERS ---------------------------------------------------------------

/// The GATE's COUNTERS, printed: steps and bytes per evaluation over every
/// corpus file with a `comptime` block plus the two twins, and the memo hit
/// rate of a cold then a warm build against one memo directory. Errors are
/// not memoised (a miss is correct, just slow), so a rejected block is a
/// miss on both passes.
#[test]
fn f9_counters() {
    let dir = scratch("counters");
    let memo = dir.join("memo");
    std::fs::write(dir.join("clock.fors"), CLOCK_TWIN).unwrap();
    std::fs::write(dir.join("declared.fors"), DECLARED_TWIN).unwrap();
    std::fs::write(dir.join(".config"), "mode = fast\n").unwrap();
    let mut programs: Vec<String> = Vec::new();
    for e in std::fs::read_dir(repo_root().join("tests/conformance/04-authority")).unwrap() {
        let p = e.unwrap().path();
        if p.extension().and_then(|x| x.to_str()) == Some("fors")
            && std::fs::read_to_string(&p).unwrap().contains("comptime {")
        {
            programs.push(p.to_string_lossy().into_owned());
        }
    }
    programs.sort();
    assert_eq!(programs.len(), 5, "the five ch04 comptime files");
    programs.push(dir.join("clock.fors").to_string_lossy().into_owned());
    programs.push(dir.join("declared.fors").to_string_lossy().into_owned());
    let (mut hits, mut lookups) = (0u64, 0u64);
    for pass in ["cold", "warm"] {
        for prog in &programs {
            let out = fors(&[
                "build",
                "--counters",
                "--memo-dir",
                memo.to_str().unwrap(),
                prog,
            ]);
            let name = Path::new(prog).file_name().unwrap().to_string_lossy();
            for c in counters(&out) {
                lookups += 1;
                hits += c.hit as u64;
                eprintln!(
                    "F9 COUNTERS {pass} {name}: steps={} bytes={} memo={}",
                    c.steps,
                    c.bytes,
                    if c.hit { "hit" } else { "miss" }
                );
            }
        }
    }
    eprintln!(
        "F9 COUNTERS memo hit rate over {lookups} evaluations (cold + warm): {hits}/{lookups}"
    );
    // The declared twin is the one block that evaluates successfully: its
    // warm build is the one hit.
    assert_eq!(hits, 1, "only the successful evaluation is memoised");
}

// -- shapes F9 does not evaluate are NAMED, never a clean build -------------

/// Verifier: a VALUE-position block in a helper (`let x: i64 = comptime {
/// 5 };`). Before the repair `fors build` exited 0 (the block was evaluated
/// as a statement and the helper's run-time body silently failed to lower)
/// and `fors run` printed `ok` because `main` never called the helper.
#[test]
fn a_value_position_block_in_a_helper_is_a_named_build_error() {
    let dir = scratch("value-position");
    let p = dir.join("m.fors");
    std::fs::write(
        &p,
        "module app;\nneeds { io.stdout };\nuse std.io;\n\nfn helper() -> i64 {\n    let x: \
         i64 = comptime { 5 };\n    return x;\n}\n\nfn main(inout out: io.Stdout) {\n    \
         out.write_line(\"ok\");\n}\n",
    )
    .unwrap();
    for sub in ["build", "run"] {
        let out = fors(&[sub, p.to_str().unwrap()]);
        assert_eq!(
            out.status.code(),
            Some(EXIT_BUILD),
            "{sub}: {}",
            text(&out.stderr)
        );
        assert_eq!(codes(&out), ["A0011"], "{sub}: {}", text(&out.stderr));
        let line = text(&out.stderr);
        assert!(
            line.contains("m.fors:6:18")
                && line.contains("`helper`")
                && line.contains("used as a value"),
            "{sub}: {line}"
        );
        assert!(!text(&out.stdout).contains("ok"), "{sub} must not run");
    }
}

/// Verifier: a block in a `const` initialiser was neither evaluated nor
/// reported (`fors build` exit 0, no counter line). Now a named `A0011`.
#[test]
fn a_block_in_a_const_initialiser_is_a_named_build_error() {
    let dir = scratch("const-init");
    let p = dir.join("m.fors");
    std::fs::write(
        &p,
        "module app;\nneeds { };\n\nconst K: i64 = comptime { 5 };\n\nfn setup() {\n    let y: \
         i64 = K;\n}\n",
    )
    .unwrap();
    let out = fors(&["build", p.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(EXIT_BUILD), "{}", text(&out.stderr));
    assert_eq!(codes(&out), ["A0011"], "{}", text(&out.stderr));
    let line = text(&out.stderr);
    assert!(
        line.contains("m.fors:4:16")
            && line.contains("`K`")
            && line.contains("`const` initialiser"),
        "{line}"
    );
}
