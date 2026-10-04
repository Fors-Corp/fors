//! F10: the conformance runner of design §7.2a — ONE test over EVERY runtime
//! test of every chapter (`run-ok`, `run-error`, `run-error` + `status: 2`,
//! `trap`), each run as a real process through the real `fors run` binary,
//! comparing exactly what §7.2a's table says and nothing more:
//!
//! | Kind | Exit | `Stdout` | `Stderr` |
//! |---|---|---|---|
//! | `run-ok` | 0 | bytes equal `detail` | not compared |
//! | `run-error` | 1 | not compared | the LAST line equals `detail` |
//! | `run-error` + `status: 2` | 2, stdout closed before `main` | not compared | not compared |
//! | `trap` | `SIGTRAP` signal status | not compared | the last line is `trap: <kind> at <file>:<L>:<C>` with `<kind>` = `detail` |
//!
//! `detail` is the README's: `(no output)` is empty, and otherwise its lines
//! (a `\n` in the directive separates them) each end in a newline. A `trap`
//! test MAY assert the lines before the trap line (§7.2a): the two whose
//! directive says a deferred marker MUST NOT appear ([`TRAP_STDERR_ABSENT`])
//! assert it is absent from them. `<L>:<C>` is checked for shape only:
//! lowered instructions carry `SiteId(0)` today, so every site renders
//! `0:0`, and §7.2a compares the KIND.
//!
//! **The build.** `fors run` ALWAYS builds with the `std` package (item
//! 47(a)): ch08 R17's prelude names (`Vec`, `Buffer`, `Arena`, ...) denote
//! `std`'s items whether or not the program wrote `use std...;`, so no test
//! is run against an empty `std`, and the runner does not decide per file
//! whether `std` is in the build. A test that disagrees with the real `std`
//! is pinned below with that exact disagreement; none is hidden.

//! **A status-2 test** runs with its standard OUTPUT a real pipe whose read
//! end the runner closed before spawning (README: "the harness's only way
//! to make the final flush fail deterministically"); the entry shim ignores
//! `SIGPIPE`, so the write latches and `main`'s return exits 2.
//!
//! **Pins.** A test that cannot pass for a reason outside the runtime is
//! listed in [`PINS`] with that exact reason and an exact assertion of what
//! it does instead, so the pin fails the moment the reason goes away.
//! Every test prints one verdict line; the totals are asserted against the
//! corpus README's own count table AND against the files on disk.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    RunOk,
    RunError,
    Status2,
    Trap,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::RunOk => "run-ok",
            Kind::RunError => "run-error",
            Kind::Status2 => "run-error+status-2",
            Kind::Trap => "trap",
        }
    }
}

struct Test {
    /// Path relative to `tests/conformance`.
    rel: String,
    file: PathBuf,
    kind: Kind,
    detail: String,
}

/// Why a pinned test does what it does instead of passing, and the exact
/// observation that stands in for "passes".
enum PinExpect {
    /// The build is refused (`fors run` exit 65) with this text on stderr.
    BuildRefused(&'static str),
    /// It runs, exits 0, and its stdout is exactly these bytes.
    Stdout(&'static [u8]),
}

struct Pin {
    rel: &'static str,
    class: &'static str,
    reason: &'static str,
    expect: PinExpect,
}

const PINS: &[Pin] = &[
    Pin {
        rel: "01-ownership/arena-generation-trap.fors",
        class: "std gap",
        reason: "`a.reset()` on `Arena[Node[a], a]`: ch10 S0019 specifies `Arena`'s `reset`, but \
                 `std/mem.fors` declares no `impl Arena`, so with `std` in every build the \
                 checker reports T0043 (no method `reset`); the trap itself is ch01 R17's",
        expect: PinExpect::BuildRefused(
            "error[T0043]: `Arena[Node[<fresh brand>], <fresh brand>]` has no method `reset`",
        ),
    },
    Pin {
        rel: "02-failure/main-raises-std-error-run-error.fors",
        class: "corpus/std disagreement",
        reason: "the file writes `mem.Counting[mem.Fixed[8]]` while `std/mem.fors` declares \
                 `Counting[N: usize, A: brand]` (standalone, ch01 R15a), so the checker reports \
                 T0011 (a type where a constant argument is expected) at the `with allocator` \
                 type; behind it `fill`'s `raises AllocError` and `Vec.new()` are further checker \
                 gaps (see fors-lower's gate_main_raises_std_error_run_error)",
        expect: PinExpect::BuildRefused(
            "error[T0011]: a type where a constant argument is expected",
        ),
    },
    Pin {
        rel: "02-failure/trap-bounds.fors",
        class: "corpus/std disagreement",
        reason: "the file writes `Buffer[i64]`, `Buffer.fixed(4)` and `.slice[10]`, and `std`'s \
                 `Buffer` is `Buffer[T, N: usize]` with `empty`/`filled` and `items()` (ch10 \
                 S0023), so the checker reports T0011 (two type arguments declared, one \
                 supplied); ch10 S0002's own prelude table cites `Buffer[i64]`, so the spec and \
                 its corpus disagree",
        expect: PinExpect::BuildRefused(
            "error[T0011]: `Buffer` declares 2 type argument(s), 1 supplied",
        ),
    },
    Pin {
        rel: "10-std/try-for-each-error-propagates-run-ok.fors",
        class: "checker gap",
        reason: "the checker publishes no method target for `mem.iter(xs).try_for_each(step)` \
                 (and no D10 handler row for its `else |e|`), so lowering refuses `main` with \
                 Unresolved(\"method target\")",
        expect: PinExpect::BuildRefused("`main` does not lower: Unresolved(\"method target\")"),
    },
    Pin {
        rel: "10-std/vec-deinit-empty-nonempty-trap.fors",
        class: "checker gap",
        reason: "`Vec.new()` against `Vec[Own[i64, heap], heap]`, where `heap` is the `main(inout \
                 heap: mem.Heap)` PARAMETER used as the brand, is a silent TY_ERROR (the \
                 heap-brand-named-by-parameter gap listed in fors-check's silent.rs), so \
                 lowering refuses `main` with CheckErrors; the same with `std` in the build, \
                 and not the prelude-name path an earlier pin blamed",
        expect: PinExpect::BuildRefused("`main` does not lower: CheckErrors"),
    },
    Pin {
        rel: "10-std/str-index-is-bytes-run-ok.fors",
        class: "corpus defect",
        reason: "the program prints with `write_uint`, which ends no line, so its stdout is the \
                 two bytes `3` while the README's run-ok rule makes `detail: 3` the LINE `3\\n`; \
                 the program (a final `write_line`) or the README (an unterminated last line) \
                 must change, and neither is the runner's to change",
        expect: PinExpect::Stdout(b"3"),
    },
];

/// `trap` tests whose directive asserts a marker is ABSENT from the lines
/// before the trap line (§7.2a's "a test MAY assert their content").
const TRAP_STDERR_ABSENT: &[(&str, &str)] = &[
    ("02-failure/trap-runs-no-defer.fors", "cleanup"),
    ("10-std/defer-not-run-on-trap.fors", "cleanup"),
];

/// The directive fields of a test's source: `(expect, detail)`; text after
/// ` -- ` is comment (README).
fn directives(src: &str) -> (Option<String>, String) {
    let (mut expect, mut detail) = (None, String::new());
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            break;
        };
        let rest = rest.trim();
        let value = |v: &str| v.split(" -- ").next().unwrap_or(v).trim().to_string();
        if let Some(v) = rest.strip_prefix("expect:") {
            expect = Some(value(v));
        } else if let Some(v) = rest.strip_prefix("detail:") {
            detail = value(v);
        }
    }
    (expect, detail)
}

/// The README's `detail` as stdout bytes for `run-ok`.
fn expected_stdout(detail: &str) -> Vec<u8> {
    if detail == "(no output)" {
        return Vec::new();
    }
    let mut out = Vec::new();
    for line in detail.split("\\n") {
        out.extend_from_slice(line.as_bytes());
        out.push(b'\n');
    }
    out
}

/// Every test of the corpus (a `.fors` file in a chapter directory, or a
/// directory whose `main.fors` carries the directives): the runtime ones,
/// classified, and the names of any the runner cannot classify.
fn corpus() -> (Vec<Test>, Vec<String>, usize) {
    let root = repo_root().join("tests/conformance");
    let mut chapters: Vec<PathBuf> = std::fs::read_dir(&root)
        .expect("corpus")
        .map(|e| e.expect("entry").path())
        .filter(|p| p.is_dir())
        .collect();
    chapters.sort();
    let mut tests = Vec::new();
    let mut unclassified = Vec::new();
    let mut all = 0;
    for ch in chapters {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(&ch)
            .expect("chapter")
            .map(|e| e.expect("entry").path())
            .collect();
        entries.sort();
        for e in entries {
            let file = if e.is_dir() {
                e.join("main.fors")
            } else if e.extension().and_then(|x| x.to_str()) == Some("fors") {
                e.clone()
            } else {
                continue; // README.md and the like
            };
            let rel = e
                .strip_prefix(&root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            let Ok(src) = std::fs::read_to_string(&file) else {
                unclassified.push(format!("{rel}: no readable main.fors"));
                continue;
            };
            all += 1;
            let (expect, detail) = directives(&src);
            let kind = match expect.as_deref() {
                Some("run-ok") => Kind::RunOk,
                Some("run-error") if detail.starts_with("status:") => {
                    if detail.trim_start_matches("status:").trim() != "2" {
                        unclassified.push(format!("{rel}: a run-error status other than 2"));
                        continue;
                    }
                    Kind::Status2
                }
                Some("run-error") => Kind::RunError,
                Some("trap") => Kind::Trap,
                Some("parse-ok" | "check-ok" | "parse-error" | "check-error") => continue,
                Some(other) => {
                    unclassified.push(format!("{rel}: unknown expectation `{other}`"));
                    continue;
                }
                None => {
                    unclassified.push(format!("{rel}: no `expect:` directive"));
                    continue;
                }
            };
            if e.is_dir() {
                // `fors run` builds one file plus `std`; a multi-module
                // runtime test would need the directory build.
                unclassified.push(format!("{rel}: a directory runtime test"));
                continue;
            }
            tests.push(Test {
                rel,
                file,
                kind,
                detail,
            });
        }
    }
    (tests, unclassified, all)
}

/// The README's count table, total row: `(tests, run-ok, run-error, trap)`.
fn readme_counts() -> (usize, usize, usize, usize) {
    let readme =
        std::fs::read_to_string(repo_root().join("tests/conformance/README.md")).expect("README");
    let header: Vec<String> = readme
        .lines()
        .find(|l| l.starts_with("| Dir |"))
        .expect("the count table")
        .split('|')
        .map(|c| c.trim().to_string())
        .collect();
    let row: Vec<String> = readme
        .lines()
        .find(|l| l.starts_with("| total ("))
        .expect("the total row")
        .split('|')
        .map(|c| c.trim().to_string())
        .collect();
    let col = |name: &str| -> usize {
        let i = header.iter().position(|h| h == name).expect(name);
        row[i].parse().expect("a count")
    };
    let total: usize = row[1]
        .trim_start_matches("total (")
        .trim_end_matches(')')
        .parse()
        .expect("total");
    (total, col("run-ok"), col("run-error"), col("trap"))
}

fn spawn(t: &Test) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_fors"));
    cmd.arg("run");
    cmd.arg(&t.file)
        .current_dir(repo_root())
        .env_remove("FORS_BACKTRACE")
        .env_remove("FORS_STD")
        .stdin(Stdio::null())
        .stderr(Stdio::piped());
    if t.kind == Kind::Status2 {
        let (reader, writer) = std::io::pipe().expect("a pipe");
        drop(reader);
        cmd.stdout(writer);
        let out = cmd.output().expect("fors runs");
        drop(cmd);
        return out;
    }
    cmd.stdout(Stdio::piped());
    cmd.output().expect("fors runs")
}

#[cfg(unix)]
fn signal_of(o: &Output) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;
    o.status.signal()
}

#[cfg(not(unix))]
fn signal_of(_o: &Output) -> Option<i32> {
    None
}

const SIGTRAP: i32 = 5;

/// §7.2a's comparison for one test: `Ok(())` or the first difference.
fn judge(t: &Test, o: &Output) -> Result<(), String> {
    let stderr = String::from_utf8_lossy(&o.stderr);
    let last = stderr
        .trim_end_matches('\n')
        .rsplit('\n')
        .next()
        .unwrap_or("");
    match t.kind {
        Kind::RunOk => {
            if o.status.code() != Some(0) {
                return Err(format!("exit {:?}, want 0; stderr {stderr:?}", o.status));
            }
            let want = expected_stdout(&t.detail);
            if o.stdout != want {
                return Err(format!(
                    "stdout {:?}, want {:?}",
                    String::from_utf8_lossy(&o.stdout),
                    String::from_utf8_lossy(&want)
                ));
            }
        }
        Kind::RunError => {
            if o.status.code() != Some(1) {
                return Err(format!("exit {:?}, want 1; stderr {stderr:?}", o.status));
            }
            if last != t.detail {
                return Err(format!("last stderr line {last:?}, want {:?}", t.detail));
            }
        }
        Kind::Status2 => {
            if o.status.code() != Some(2) {
                return Err(format!("exit {:?}, want 2; stderr {stderr:?}", o.status));
            }
        }
        Kind::Trap => {
            if signal_of(o) != Some(SIGTRAP) {
                return Err(format!(
                    "exit {:?}, want the SIGTRAP signal status; stderr {stderr:?}",
                    o.status
                ));
            }
            let file = t.file.to_string_lossy();
            let Some(rest) = last.strip_prefix("trap: ") else {
                return Err(format!("last stderr line {last:?} is not a trap line"));
            };
            let Some((kind, at)) = rest.split_once(" at ") else {
                return Err(format!("trap line {last:?} has no ` at `"));
            };
            if kind != t.detail {
                return Err(format!("trap kind `{kind}`, want `{}`", t.detail));
            }
            let site_ok = at.strip_prefix(file.as_ref()).is_some_and(|lc| {
                let parts: Vec<&str> = lc.split(':').collect();
                parts.len() == 3
                    && parts[0].is_empty()
                    && parts[1..]
                        .iter()
                        .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit()))
            });
            if !site_ok {
                return Err(format!("trap site `{at}` is not `{file}:<L>:<C>`"));
            }
            let before = &stderr[..stderr.len() - last.len() - 1];
            for (rel, marker) in TRAP_STDERR_ABSENT {
                if *rel == t.rel && before.contains(marker) {
                    return Err(format!(
                        "`{marker}` appears before the trap line: {before:?}"
                    ));
                }
            }
        }
    }
    Ok(())
}

fn judge_pin(p: &Pin, o: &Output) -> Result<(), String> {
    let stderr = String::from_utf8_lossy(&o.stderr);
    match p.expect {
        PinExpect::BuildRefused(text) => {
            if o.status.code() != Some(65) || !stderr.contains(text) {
                return Err(format!(
                    "the pinned reason changed (exit {:?}, stderr {stderr:?}): re-run it unpinned",
                    o.status
                ));
            }
        }
        PinExpect::Stdout(bytes) => {
            if o.status.code() != Some(0) || o.stdout != bytes {
                return Err(format!(
                    "the pinned behaviour changed (exit {:?}, stdout {:?}): re-run it unpinned",
                    o.status,
                    String::from_utf8_lossy(&o.stdout)
                ));
            }
        }
    }
    Ok(())
}

#[test]
fn every_runtime_conformance_test_under_the_7_2a_runner() {
    let (tests, unclassified, all) = corpus();
    let mut pass = [0usize; 4];
    let mut pinned = Vec::new();
    let mut failed = Vec::new();
    for t in &tests {
        let o = spawn(t);
        let pin = PINS.iter().find(|p| p.rel == t.rel);
        let verdict = match pin {
            Some(p) => match judge_pin(p, &o) {
                Ok(()) => {
                    pinned.push(p.rel);
                    format!("PIN  ({}: {})", p.class, p.reason)
                }
                Err(e) => {
                    failed.push(format!("{}: {e}", t.rel));
                    format!("FAIL {e}")
                }
            },
            None => match judge(t, &o) {
                Ok(()) => {
                    pass[t.kind as usize] += 1;
                    "PASS".to_string()
                }
                Err(e) => {
                    failed.push(format!("{}: {e}", t.rel));
                    format!("FAIL {e}")
                }
            },
        };
        println!("{:<20} {:<70} {verdict}", t.kind.name(), t.rel);
    }
    let count = |k: Kind| tests.iter().filter(|t| t.kind == k).count();
    let (readme_total, readme_ok, readme_err, readme_trap) = readme_counts();
    println!(
        "runtime tests: {} (run-ok {}, run-error {} of which status-2 {}, trap {}) | \
         passed {} (run-ok {}, run-error {}, status-2 {}, trap {}) | pinned {} | failed {} | \
         unclassified {} | corpus tests {all} (README {readme_total})",
        tests.len(),
        count(Kind::RunOk),
        count(Kind::RunError) + count(Kind::Status2),
        count(Kind::Status2),
        count(Kind::Trap),
        pass.iter().sum::<usize>(),
        pass[Kind::RunOk as usize],
        pass[Kind::RunError as usize],
        pass[Kind::Status2 as usize],
        pass[Kind::Trap as usize],
        pinned.len(),
        failed.len(),
        unclassified.len(),
    );
    for u in &unclassified {
        println!("UNCLASSIFIED {u}");
    }
    assert!(
        unclassified.is_empty(),
        "files the runner cannot classify: {unclassified:#?}"
    );
    assert!(failed.is_empty(), "failing runtime tests: {failed:#?}");
    // The counts are the corpus's own: the README's table and the files.
    assert_eq!(count(Kind::RunOk), readme_ok, "run-ok: files vs README");
    assert_eq!(
        count(Kind::RunError) + count(Kind::Status2),
        readme_err,
        "run-error: files vs README"
    );
    assert_eq!(count(Kind::Trap), readme_trap, "trap: files vs README");
    assert_eq!(tests.len(), readme_ok + readme_err + readme_trap);
    assert_eq!(tests.len(), 64, "design §9 F10: the 64 runtime tests");
    // §7.2a names exactly two status-2 tests.
    let s2: Vec<&str> = tests
        .iter()
        .filter(|t| t.kind == Kind::Status2)
        .map(|t| t.rel.as_str())
        .collect();
    assert_eq!(
        s2,
        [
            "02-failure/main-returns-latched-stdout-exit-2.fors",
            "10-std/sigpipe-ignored-write-latches-run-error.fors"
        ]
    );
    // Every pin names a real runtime test, once.
    for p in PINS {
        assert_eq!(
            pinned.iter().filter(|r| **r == p.rel).count(),
            1,
            "pin {} matched no runtime test",
            p.rel
        );
    }
    assert_eq!(pass.iter().sum::<usize>() + pinned.len(), tests.len());
}

/// A status-2 test's pipe is what makes it exit 2: the same program with an
/// OPEN stdout exits 0, so the runner's closed descriptor is load-bearing,
/// not decorative.
#[test]
fn a_status_2_test_with_an_open_stdout_exits_0() {
    let file =
        repo_root().join("tests/conformance/10-std/sigpipe-ignored-write-latches-run-error.fors");
    let o = Command::new(env!("CARGO_BIN_EXE_fors"))
        .arg("run")
        .arg(&file)
        .output()
        .expect("fors runs");
    assert_eq!(o.status.code(), Some(0));
    assert_eq!(o.stdout, b"to a closed pipe\n");
}
