//! F2 gate tests, driven end to end against the REAL conformance corpus
//! files (design §9's F2 paragraph; GATE list is the acceptance criterion),
//! through the full pipeline a `fors build`/`fors run` would use: parse ->
//! resolve -> check -> lower -> verify -> interpret. §7.2a owns what the
//! runner compares for each of the four runtime expectation kinds; this is
//! that runner, extended (per the F2 task) to drive it.
//!
//! A test whose source names `use std.io;` also builds `std/io.fors`
//! alongside it (module name `["std","io"]`, so ch08 R17's "a build that
//! does contain `std` sources... resolves against them like any other
//! module" path fires instead of the prelude's synthetic stand-in — real
//! `Stdout`/`Writer` are not among ch10 R2's eight prelude-opaque names, so
//! there is no synthetic fallback for them). `write_line`'s own stub body
//! (`{}`) is never reached: `fors-lower`'s F1 stand-in (design §5.8
//! mechanism 2) maps any method literally spelled `write_line` straight to
//! the `stdout_write_line` intrinsic, whatever its owner.
//!
//! Two tests need "the standard OUTPUT descriptor closed before `main`"
//! (`tests/conformance/README.md`, §7.2a: `main-returns-latched-stdout-
//! exit-2` and `10-std/sigpipe-ignored-write-latches-run-error`, the latter
//! owner Q8's decision). The runner does exactly that: it creates a real
//! pipe, closes the read end, and hands the write end to the interpreter
//! through `HostEnv::stdout_fd` — after resetting `SIGPIPE` to its default
//! disposition and letting the entry shim's `install_sigpipe_ignore` put
//! `SIG_IGN` back, so the test proves the shim is what turns the write
//! into a latched `io.Error.closed` rather than a signal death. The
//! subprocess differential runner is F10's; nothing here forks.
//!
//! Below the eight gates, a set of inline-source probes covers what the
//! corpus does not yet: a violated `post`, `.off` on a `post`, and a direct
//! inspection of the FMIR dump (no contract-check instruction at all under
//! `.off`; both `check_pre` and `check_post` under `.runtime`).

use std::fs;
use std::path::{Path, PathBuf};

use fors_fmir::op::TrapKind;
use fors_index::{Interner, Segments, module::is_legal_segment};
use fors_interp::shim::{ExitStatus, HostEnv, entry_exit};
use fors_interp::{Config, Program, run_with_host};
use fors_resolve::FileInput;
use fors_syntax::parse_file;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// The four directive lines every conformance test opens with (see
/// `tests/conformance/README.md`).
struct Directive {
    expect: String,
    detail: String,
}

fn parse_directive(src: &str) -> Directive {
    let (mut expect, mut detail) = (String::new(), String::new());
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            break;
        };
        let rest = rest.trim();
        if let Some(v) = rest.strip_prefix("expect:") {
            expect = v.split("--").next().unwrap_or(v).trim().to_string();
        } else if let Some(v) = rest.strip_prefix("detail:") {
            detail = v.split("--").next().unwrap_or(v).trim().to_string();
        }
    }
    Directive { expect, detail }
}

/// The module header's dotted name, or `None` absent one (ch08 R24's
/// fallback-to-file-stem convention, same as `fors-check`'s own harness).
fn header_name(source: &[u8], interner: &mut Interner) -> Option<Segments> {
    let p = parse_file(source);
    if p.tree.is_empty() {
        return None;
    }
    let child = p.tree.children(0).next()?;
    if p.tree.kinds[child] != fors_syntax::NodeKind::ModuleHdr {
        return None;
    }
    let path_node = p.tree.children(child).next()?;
    let (first, end) = p.tree.token_range(path_node);
    let mut out = Vec::new();
    for i in first as usize..end as usize {
        if p.tokens.kinds[i] == fors_lex::TokenKind::Ident {
            out.push(interner.intern(p.tokens.text(i, source)));
        }
    }
    (!out.is_empty()).then_some(out)
}

fn module_name_of(stem: &str, source: &[u8], interner: &mut Interner) -> Segments {
    header_name(source, interner).unwrap_or_else(|| {
        let stem = if is_legal_segment(stem.as_bytes()) {
            stem.to_string()
        } else {
            "m".to_string()
        };
        vec![interner.intern(stem.as_bytes())]
    })
}

/// What a run came to, in the terms this runner compares against a
/// directive (§7.2a's table, F2's slice of it).
#[derive(Debug)]
enum Observed {
    Trap(TrapKind),
    Status(i32, Vec<u8>),
}

/// One built-and-run program: its observable outcome plus the number of
/// contract-check instructions (`check_pre`/`post`/`inv`) in its FMIR
/// dump, so a test can assert on the lowering itself and not only on the
/// run (ch02 R10: `.off` removes the check; design §3.6).
struct Run {
    observed: Observed,
    contract_checks: usize,
}

/// Builds `src` (plus `std/io.fors` when the source names `use std.io;` —
/// a pragmatic stand-in for a real per-file `needs`-to-import resolver,
/// sufficient for the F2 tests that use `io.Stdout`) and runs it under
/// `host`. `label` names the program in failure messages; `stem` is the
/// ch08 R24 module-name fallback.
fn build_and_run(label: &str, stem: &str, src: &[u8], host: &HostEnv) -> Run {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.to_vec()];
    let mut names: Vec<Segments> = vec![module_name_of(stem, src, &mut interner)];
    if String::from_utf8_lossy(src).contains("use std.io;") {
        let io_path = repo_root().join("std/io.fors");
        let io_src = fs::read(&io_path).expect("std/io.fors reads");
        let name: Segments = vec![interner.intern(b"std"), interner.intern(b"io")];
        sources.push(io_src);
        names.push(name);
    }
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(sources.iter())
        .zip(names.iter())
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s,
            name: n.clone(),
        })
        .collect();
    for p in &parsed {
        assert!(p.diags.is_empty(), "{label}: parse diags: {:?}", p.diags);
    }
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    let resolve_diags: Vec<String> = resolved
        .files
        .iter()
        .flat_map(|f| f.diagnostics.iter())
        .map(|d| d.code.as_string())
        .collect();
    assert!(
        resolve_diags.is_empty(),
        "{label}: resolve diags: {resolve_diags:?}"
    );
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let check_diags: Vec<String> = out.diagnostics.iter().map(|d| d.code.as_string()).collect();
    assert!(
        check_diags.is_empty(),
        "{label}: check diags: {check_diags:?}"
    );
    let lowered = fors_lower::lower_build(&inputs, &out, &mut interner);
    for f in &lowered.fns {
        let diags = fors_fmir::verify::verify(&f.decl);
        assert!(
            diags.is_empty(),
            "{label}: lowered {} must verify clean: {diags:?}",
            f.name
        );
    }
    assert!(
        lowered.fns.iter().any(|f| f.name == "main"),
        "{label}: lower diags: {:?}",
        lowered.diags
    );
    let contract_checks = lowered
        .fns
        .iter()
        .flat_map(|f| f.decl.insts.all_rows())
        .filter(|(_, row)| row.op.is_contract_check())
        .count();
    let fns: Vec<_> = lowered
        .fns
        .into_iter()
        .map(|f| fors_interp::ProgFn {
            name: f.name,
            decl: f.decl,
            strings: f.strings,
            intrinsics: f.intrinsics,
        })
        .collect();
    let prog = Program::entry_by_name(fns, "main", Config::v0_1()).expect("a main");
    let outcome = run_with_host(&prog, &out.fir.tys, host).expect("a verified program runs");
    let observed = match entry_exit(&outcome) {
        ExitStatus::Trap(k) => Observed::Trap(k),
        ExitStatus::Status(code) => Observed::Status(code, outcome.stdout),
    };
    Run {
        observed,
        contract_checks,
    }
}

/// Checks `src` against its own directive lines under `host`, returning
/// the run for any further assertion.
fn check_source(label: &str, stem: &str, src: &str, host: &HostEnv) -> Run {
    let d = parse_directive(src);
    let run = build_and_run(label, stem, src.as_bytes(), host);
    match d.expect.as_str() {
        "trap" => {
            let Observed::Trap(k) = run.observed else {
                panic!("{label}: expected trap, got {:?}", run.observed);
            };
            assert_eq!(k.as_str(), d.detail, "{label}: trap kind mismatch");
        }
        "run-ok" => {
            let Observed::Status(code, ref stdout) = run.observed else {
                panic!("{label}: expected run-ok, got {:?}", run.observed);
            };
            assert_eq!(code, 0, "{label}: exit status");
            if d.detail == "(no output)" {
                assert_eq!(stdout, b"", "{label}: stdout");
            } else {
                // `detail` names one line's text; stdout is that line plus
                // `write_line`'s trailing `\n` (§7.2a: `run-ok` compares
                // bytes equal to `detail`, and every F2 `run-ok` gate test
                // here is exactly one `write_line`).
                let mut expected = d.detail.as_bytes().to_vec();
                expected.push(b'\n');
                assert_eq!(*stdout, expected, "{label}: stdout");
            }
        }
        "run-error" => {
            let Observed::Status(code, _) = run.observed else {
                panic!("{label}: expected run-error, got {:?}", run.observed);
            };
            let want: i32 = d
                .detail
                .strip_prefix("status:")
                .expect("F2's run-error tests all pin a status")
                .trim()
                .parse()
                .expect("status is an int");
            assert_eq!(code, want, "{label}: exit status");
        }
        other => panic!("{label}: unhandled expect kind {other:?}"),
    }
    run
}

/// Checks the corpus file `rel` against its own directive under `host`.
fn check_corpus_file(rel: &str, host: &HostEnv) -> Run {
    let path = repo_root().join("tests/conformance").join(rel);
    let src = fs::read_to_string(&path).expect("corpus file reads");
    let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
    check_source(rel, &stem, &src, host)
}

fn gate_test(rel: &str) {
    check_corpus_file(rel, &HostEnv::default());
}

/// `tests/conformance/README.md`: "A `status: 2` test is run with the
/// standard OUTPUT descriptor closed". A real pipe whose read end is
/// closed before `main` runs; the shim's `SIG_IGN` is what makes the
/// write come back as `EPIPE` (latched, ch10 R39) instead of killing the
/// process, and the test starts from `SIG_DFL` to prove that.
#[cfg(unix)]
fn gate_test_closed_stdout(rel: &str) {
    use std::os::fd::AsRawFd;
    use std::sync::Mutex;
    // Signal dispositions are process-wide and the test harness runs
    // tests concurrently: serialise the DFL -> IGN -> write window so one
    // test's reset can never land inside another's.
    static SIGPIPE_WINDOW: Mutex<()> = Mutex::new(());
    let _guard = SIGPIPE_WINDOW.lock().unwrap_or_else(|p| p.into_inner());
    let was = fors_interp::shim::set_sigpipe(fors_interp::shim::SIG_DFL);
    fors_interp::install_sigpipe_ignore();
    let (reader, writer) = std::io::pipe().expect("a pipe");
    drop(reader);
    let host = HostEnv {
        stdout_fd: Some(writer.as_raw_fd()),
    };
    check_corpus_file(rel, &host);
    drop(writer);
    // Leave the harness process as it was found.
    fors_interp::shim::set_sigpipe(was);
}

// -- design §9's F2 GATE (8 tests) -----------------------------------------

#[test]
fn gate_contract_runtime_violation_trap() {
    gate_test("02-failure/contract-runtime-violation-trap.fors");
}

#[test]
fn gate_contract_off_no_check_run_ok() {
    gate_test("02-failure/contract-off-no-check-run-ok.fors");
}

#[test]
#[cfg(unix)]
fn gate_main_returns_latched_stdout_exit_2() {
    gate_test_closed_stdout("02-failure/main-returns-latched-stdout-exit-2.fors");
}

#[test]
fn gate_trap_bounds() {
    gate_test("02-failure/trap-bounds.fors");
}

#[test]
fn gate_trap_div_zero() {
    gate_test("02-failure/trap-div-zero.fors");
}

#[test]
fn gate_trap_shift() {
    gate_test("02-failure/trap-shift.fors");
}

#[test]
fn gate_write_line_without_question_accepted_run_ok() {
    gate_test("10-std/write-line-without-question-accepted-run-ok.fors");
}

#[test]
#[cfg(unix)]
fn gate_sigpipe_ignored_write_latches_run_error() {
    // Owner decision, Q8 (design §11.1): the test expects exit 2.
    gate_test_closed_stdout("10-std/sigpipe-ignored-write-latches-run-error.fors");
}

// -- the dump, not just the outcome (ch02 R9/R10, design §3.6) -------------

#[test]
fn contract_off_lowers_no_check_instruction_at_all() {
    let run = check_corpus_file(
        "02-failure/contract-off-no-check-run-ok.fors",
        &HostEnv::default(),
    );
    assert_eq!(
        run.contract_checks, 0,
        "`.off` must remove the check from the FMIR, not merely skip it"
    );
}

#[test]
fn contract_runtime_lowers_the_check_instruction() {
    let run = check_corpus_file(
        "02-failure/contract-runtime-violation-trap.fors",
        &HostEnv::default(),
    );
    assert_eq!(run.contract_checks, 1, "one `pre` -> one `check_pre`");
}

// -- probes beyond the corpus: `post`, `.off` on `post`, both clauses ------

const POST_VIOLATED: &str = "\
//! name: probe-post-violated
//! rule: 02.R9
//! expect: trap
//! detail: contract

module app.probe;
contracts: .runtime;

fn bump(let n: i64) -> i64
    post n < 0
{
    return n + 1;
}

fn main() {
    let r: i64 = bump(3);
}
";

#[test]
fn probe_post_violated_under_runtime_traps() {
    let run = check_source("post-violated", "probe", POST_VIOLATED, &HostEnv::default());
    assert_eq!(run.contract_checks, 1, "one `post` -> one `check_post`");
}

#[test]
fn probe_post_violated_under_off_runs_ok_with_no_check() {
    let src = POST_VIOLATED
        .replace("//! expect: trap", "//! expect: run-ok")
        .replace("//! detail: contract", "//! detail: (no output)")
        .replace("contracts: .runtime;", "contracts: .off;");
    let run = check_source("post-violated-off", "probe", &src, &HostEnv::default());
    assert_eq!(run.contract_checks, 0);
}

#[test]
fn probe_pre_violated_under_off_runs_ok_with_no_check() {
    let src = "\
//! name: probe-pre-violated-off
//! rule: 02.R10
//! expect: run-ok
//! detail: (no output)

module app.probe;
contracts: .off;

fn half(let n: i64) -> i64
    pre n >= 0
{
    return n / 2;
}

fn main() {
    let r: i64 = half(-4);
}
";
    let run = check_source("pre-violated-off", "probe", src, &HostEnv::default());
    assert_eq!(run.contract_checks, 0);
}

#[test]
fn probe_satisfied_pre_and_post_run_to_completion() {
    // Both clauses present and both hold: the checks are emitted (two
    // instructions) and neither fires; the body's output arrives.
    let src = "\
//! name: probe-pre-post-hold
//! rule: 02.R9
//! expect: run-ok
//! detail: ok

module app.probe;
needs { io.stdout };
use std.io;

fn half(let n: i64) -> i64
    pre n >= 0
    post n >= 0
{
    return n / 2;
}

fn main(inout out: io.Stdout) {
    let r: i64 = half(4);
    out.write_line(\"ok\");
}
";
    let run = check_source("pre-post-hold", "probe", src, &HostEnv::default());
    assert_eq!(run.contract_checks, 2, "`pre` + `post` -> two instructions");
}

#[test]
fn probe_post_is_checked_on_an_explicit_return_path() {
    // The `post` must sit before EVERY `ret`, the explicit `return n;`
    // included — not only the fall-through one `lower_fn` adds.
    let src = "\
//! name: probe-post-explicit-return
//! rule: 02.R9
//! expect: trap
//! detail: contract

module app.probe;

fn pick(let n: i64) -> i64
    post n > 10
{
    if n > 0 {
        return n;
    }
    return 0 - n;
}

fn main() {
    let r: i64 = pick(5);
}
";
    check_source("post-explicit-return", "probe", src, &HostEnv::default());
}

#[test]
#[cfg(unix)]
fn open_pipe_carries_stdout_through_and_exits_0() {
    // The same descriptor path as the closed-pipe gates, with the read
    // end OPEN: nothing latches, status 0, and the bytes arrive both in
    // the pipe and in the oracle's captured image.
    use std::io::Read;
    use std::os::fd::AsRawFd;
    let (mut reader, writer) = std::io::pipe().expect("a pipe");
    let host = HostEnv {
        stdout_fd: Some(writer.as_raw_fd()),
    };
    let run = check_corpus_file(
        "10-std/write-line-without-question-accepted-run-ok.fors",
        &host,
    );
    drop(writer);
    let mut piped = Vec::new();
    reader.read_to_end(&mut piped).unwrap();
    assert_eq!(piped, b"ok\n");
    let Observed::Status(0, ref captured) = run.observed else {
        panic!("expected status 0, got {:?}", run.observed);
    };
    assert_eq!(*captured, b"ok\n");
}
