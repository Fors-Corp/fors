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

/// F7's probe: every `std/*.fors` module, named the way `ch08 R17`'s
/// synthetic table does, so `has_std` goes true and prelude names (`Buffer`,
/// `Vec`, `Str`, `Option`, ...) resolve against the real bodies instead of
/// the signature-only stand-in.
fn std_module_sources() -> Vec<(Vec<Vec<u8>>, Vec<u8>)> {
    let root = repo_root().join("std");
    let files: &[(&str, &[&str])] = &[
        ("io.fors", &["std", "io"]),
        ("mem.fors", &["std", "mem"]),
        ("mem/alloc.fors", &["std", "mem", "alloc"]),
        ("mem/vec.fors", &["std", "mem", "vec"]),
        ("mem/seq.fors", &["std", "mem", "seq"]),
        ("mem/text.fors", &["std", "mem", "text"]),
        ("mem/hashmap.fors", &["std", "mem", "hashmap"]),
        ("fs.fors", &["std", "fs"]),
        ("net.fors", &["std", "net"]),
        ("proc.fors", &["std", "proc"]),
        ("rand.fors", &["std", "rand"]),
        ("time.fors", &["std", "time"]),
        ("env.fors", &["std", "env"]),
        ("ffi.fors", &["std", "ffi"]),
        ("gpu.fors", &["std", "gpu"]),
    ];
    files
        .iter()
        .map(|(rel, segs)| {
            let src = fs::read(root.join(rel)).expect("std module reads");
            let segs: Vec<Vec<u8>> = segs.iter().map(|s| s.as_bytes().to_vec()).collect();
            (segs, src)
        })
        .collect()
}

/// Like [`build_and_run`], but builds the whole `std/` package alongside
/// `src` (F7: real bodies need the real sources in the build, not the
/// synthetic prelude stand-in).
fn build_and_run_with_std(label: &str, stem: &str, src: &[u8], host: &HostEnv) -> Run {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.to_vec()];
    let mut names: Vec<Segments> = vec![module_name_of(stem, src, &mut interner)];
    for (segs, s) in std_module_sources() {
        names.push(
            segs.iter()
                .map(|b| interner.intern(b))
                .collect::<Segments>(),
        );
        sources.push(s);
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
        .enumerate()
        .flat_map(|(i, f)| f.diagnostics.iter().map(move |d| (i, d)))
        .map(|(i, d)| {
            format!(
                "{}: {}: {}",
                names_debug(&inputs, i),
                d.code.as_string(),
                d.message
            )
        })
        .collect();
    assert!(
        resolve_diags.is_empty(),
        "{label}: resolve diags: {resolve_diags:#?}"
    );
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let check_diags: Vec<String> = out
        .diagnostics
        .iter()
        .map(|d| {
            format!(
                "{}:{}: {}: {}",
                names_debug(&inputs, d.file.index()),
                d.start,
                d.code.as_string(),
                d.message
            )
        })
        .collect();
    assert!(
        check_diags.is_empty(),
        "{label}: check diags: {check_diags:#?}"
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

fn names_debug(inputs: &[FileInput], i: usize) -> String {
    format!("{:?}", inputs[i].name)
}

fn gate_test_std(rel: &str) {
    let path = repo_root().join("tests/conformance").join(rel);
    let src = fs::read_to_string(&path).expect("corpus file reads");
    let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
    let d = parse_directive(&src);
    let run = build_and_run_with_std(rel, &stem, src.as_bytes(), &HostEnv::default());
    match d.expect.as_str() {
        "trap" => {
            let Observed::Trap(k) = run.observed else {
                panic!("{rel}: expected trap, got {:?}", run.observed);
            };
            assert_eq!(k.as_str(), d.detail, "{rel}: trap kind mismatch");
        }
        "run-ok" => {
            let Observed::Status(code, ref stdout) = run.observed else {
                panic!("{rel}: expected run-ok, got {:?}", run.observed);
            };
            assert_eq!(code, 0, "{rel}: exit status");
            // README §7.2a: `run-ok`'s stdout bytes equal `detail` EXACTLY
            // (`(no output)` = empty) — no implicit trailing newline. F2's
            // own `check_source` appends one because every F2 test prints
            // with `write_line`; an F7 test may use `write_uint` (no
            // newline), so this runner compares literally instead.
            let expected: &[u8] = if d.detail == "(no output)" {
                b""
            } else {
                d.detail.as_bytes()
            };
            assert_eq!(&stdout[..], expected, "{rel}: stdout");
        }
        "run-error" => {
            let Observed::Status(code, _) = run.observed else {
                panic!("{rel}: expected run-error, got {:?}", run.observed);
            };
            let want: i32 = d
                .detail
                .strip_prefix("status:")
                .expect("run-error detail pins a status")
                .trim()
                .parse()
                .expect("status is an int");
            assert_eq!(code, want, "{rel}: exit status");
        }
        other => panic!("{rel}: unhandled expect kind {other:?}"),
    }
}

/// F7 (a): "`std` must check clean ... and add a workspace test that
/// asserts it (`fors check` over `std/` yields no diagnostic) so it
/// cannot regress silently." `cargo run -p fors-cli -- check std` is NOT
/// this test: it names every module WITHOUT a `std` prefix and checks it
/// as package `std`, which makes `has_std` false (no module is literally
/// named `std.*`) and sends every `use std.mem.alloc;`-shaped import in
/// `std`'s OWN sources through ch08 R17's synthetic-table fallback,
/// silently `Poisoned` rather than resolved — so a real cross-submodule
/// break (verified against this file's earlier state, which this test
/// would have caught) is invisible to it. This test instead builds `std`
/// exactly as a consuming program does (`std`-prefixed module names, real
/// cross-module resolution; see `build_and_run_with_std`), which is what
/// `has_std` actually requires to go true.
#[test]
fn std_checks_clean() {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    let mut names: Vec<Segments> = Vec::new();
    for (segs, s) in std_module_sources() {
        names.push(
            segs.iter()
                .map(|b| interner.intern(b))
                .collect::<Segments>(),
        );
        sources.push(s);
    }
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    for p in &parsed {
        assert!(p.diags.is_empty(), "std/ must parse clean: {:?}", p.diags);
    }
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, None, None);
    let resolve_diags: Vec<String> = resolved
        .files
        .iter()
        .enumerate()
        .flat_map(|(i, f)| f.diagnostics.iter().map(move |d| (i, d)))
        .map(|(i, d)| {
            format!(
                "{}: {}: {}",
                names_debug(&inputs, i),
                d.code.as_string(),
                d.message
            )
        })
        .collect();
    assert!(
        resolve_diags.is_empty(),
        "std/ must resolve clean: {resolve_diags:#?}"
    );
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let check_diags: Vec<String> = out
        .diagnostics
        .iter()
        .map(|d| {
            format!(
                "{}:{}: {}: {}",
                names_debug(&inputs, d.file.index()),
                d.start,
                d.code.as_string(),
                d.message
            )
        })
        .collect();
    assert!(
        check_diags.is_empty(),
        "std/ must check clean: {check_diags:#?}"
    );
}

/// F7 verification: the `str_byte_len`/`str_byte_at`/`str_byte_slice`
/// stand-ins are intercepted for `Str`'s OWN impl only. A user method that
/// merely shares the spelling runs its own body — before the fix it was
/// hijacked into the intrinsic, which then read a non-`Str` receiver as
/// handle `1` and printed `0`.
#[test]
fn user_method_named_like_a_str_intrinsic_keeps_its_body() {
    const SRC: &[u8] = b"\
module app;
needs { io.stdout };
use std.io;

struct B { v: u64 }

impl B {
    fn str_byte_len(let self: Self) -> usize {
        return 7;
    }
}

fn main(inout out: io.Stdout) {
    let b: B = B { v: 1 };
    out.write_uint(b.str_byte_len() as u64);
}
";
    let run = build_and_run_with_std(
        "user_method_named_like_a_str_intrinsic",
        "user_method_named_like_a_str_intrinsic",
        SRC,
        &HostEnv::default(),
    );
    let Observed::Status(code, ref stdout) = run.observed else {
        panic!("expected run-ok, got {:?}", run.observed);
    };
    assert_eq!(code, 0);
    assert_eq!(&stdout[..], b"7", "the user's own body, not the intrinsic");
}

// -- design §9's F7 GATE (6 tests) -----------------------------------------

#[test]
fn gate_str_index_is_bytes_run_ok() {
    gate_test_std("10-std/str-index-is-bytes-run-ok.fors");
}

#[test]
#[ignore = "HELD OUT: `s.slice(0, 2) else |e| { ... }` needs the Handler/\
            try_br machinery (F3), which `fors-lower` rejects outright \
            today (NodeKind::Handler/TryExpr/RaiseStmt => LowerError::\
            Failure) — F3 waits on I10 per the task brief. `Str.slice`'s \
            own body (std/mem/text.fors) is real and would lower once \
            `raise` does; the test itself needs the `else` handler too."]
fn gate_str_slice_non_boundary_raises_run_ok() {
    gate_test_std("10-std/str-slice-non-boundary-raises-run-ok.fors");
}

#[test]
#[ignore = "HELD OUT: `Buffer.empty()` (std/mem.fors) must produce a \
            Buffer[T, N] for an UNBOUNDED T, which needs an \
            uninitialised-aggregate construction primitive no Fors \
            syntax or FMIR op exposes today (no `T::default`, no \
            `@memset` call surface, no `rawptr` accessor to target one \
            manually — the same rawptr-read gap `SliceIter.load`/\
            `Scalars.decode` document). Separately, `fors-lower`'s \
            general `Bracket` path only lowers a RANGE index \
            (`lower_slice_range` rejects a bare scalar index with \
            `LowerError::Unsupported(\"indexing\")`), so `buf[10] = 1` \
            has no general lowering to read (d)'s new `BodyFacts::\
            IndexImpl` fact from yet, for ANY receiver, not only a user \
            nominal one. Both are pre-existing lowering-engine gaps \
            bigger than F7's named scope; (d) itself is done and \
            probed (`crates/fors-check/tests/probes.rs::\
            f7_user_index_records_its_resolved_impl`)."]
fn gate_buffer_index_past_len_trap() {
    gate_test_std("10-std/buffer-index-past-len-trap.fors");
}

#[test]
#[ignore = "HELD OUT: needs the `else |e| { ... }` handler (F3's try_br, \
            not lowered today — see `gate_str_slice_non_boundary_raises_\
            run_ok`'s note) AND `for`/`while` loops in a std body \
            (`SliceIter.next` iterates; any `for`/`while` statement \
            anywhere in a function's subtree is `LowerError::Loop` in \
            `fors-lower` today, a pre-existing, undocumented-in-F7 gap \
            bigger than this increment: NONE of F1's own 19-test gate \
            exercises a loop body either, despite the design doc listing \
            `plain-for-accumulator-accepted-run-ok`, which has no #[test] \
            wiring it up)."]
fn gate_try_for_each_error_propagates_run_ok() {
    gate_test_std("10-std/try-for-each-error-propagates-run-ok.fors");
}

#[test]
#[ignore = "HELD OUT, for three independent reasons named in the task \
            brief and confirmed empirically: `a.create(1)?`/`v.push(...)\
            ?` need `?`/try_br (F3, not lowered); `fill[A, L](...)` and \
            `Vec[Own[i64, A], A]` are generic (fors-lower refuses a call \
            to, or a body with, an unresolved generic — see `gate_\
            buffer_index_past_len_trap`'s note on the same monomorphisation \
            gap); and the allocator obligation machinery is F6's lowering \
            half, which the task brief explicitly permits holding out \
            pending I8b."]
fn gate_vec_deinit_empty_nonempty_trap() {
    gate_test_std("10-std/vec-deinit-empty-nonempty-trap.fors");
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

// -- design §9's F5 GATE (8 tests) -----------------------------------------
//
// Same mechanics as the F2 gates above — parse, resolve, check, lower,
// verify, run, then compare against the file's own `expect:`/`detail:`
// lines. What F5 adds to the pipeline underneath them: array literals and
// `slice_range` in `fors-lower`, the `Slice` descriptor and `reduce_tree`
// in `fors-interp`, and the shape itself in `fors-fmir::reduce`.
//
// Two documented stand-ins carry these files, both in the genre F2
// established for `Buffer.fixed` (design §5.8):
//   * **[HOLE-7]**: no checker increment types ch03 R11's `reduce`, so the
//     call is poisoned and `fors-lower` hard-codes the primitive's typing
//     (`reduce_stub_ranges` names all three sites).
//   * `Slice[T]` has no std body until F7, so `slice_range` builds a
//     three-cell `{ base, start, len }` descriptor and `reduce_tree` is its
//     only consumer (`fors-interp::exec::slice_parts`).
// Nothing else about these eight files is special-cased: the values they
// pin come out of the tree.

#[test]
fn gate_reduce_n1_shape_run_ok() {
    gate_test("03-numerics/reduce-n1-shape-run-ok.fors");
}

#[test]
fn gate_reduce_n7_shape_run_ok() {
    gate_test("03-numerics/reduce-n7-shape-run-ok.fors");
}

#[test]
fn gate_reduce_n8_shape_run_ok() {
    gate_test("03-numerics/reduce-n8-shape-run-ok.fors");
}

#[test]
fn gate_reduce_n9_shape_run_ok() {
    gate_test("03-numerics/reduce-n9-shape-run-ok.fors");
}

#[test]
fn gate_reduce_n257_shape_run_ok() {
    gate_test("03-numerics/reduce-n257-shape-run-ok.fors");
}

#[test]
fn gate_reduce_n0_with_identity_run_ok() {
    gate_test("03-numerics/reduce-n0-with-identity-run-ok.fors");
}

#[test]
fn gate_reduce_n0_without_identity_trap() {
    gate_test("03-numerics/reduce-n0-without-identity-trap.fors");
}

#[test]
fn gate_reduce_identity_no_effect_n3_run_ok() {
    gate_test("03-numerics/reduce-identity-no-effect-n3-run-ok.fors");
}

// -- the other half of ch03 R12 (owner decision Q3): the EXPLICIT tree ------

/// Rebuilds the s-expression a straight-line FMIR chain computes, so the
/// emitted instructions can be compared against `fors_fmir::reduce`'s own
/// explicit tree rather than merely counted. `field` reads of the operand
/// aggregate are the atoms `x{i}`; every binary op is a node with its left
/// operand first.
fn sexpr_of_last_binary(decl: &fors_fmir::decl::DeclFmir) -> Option<String> {
    use fors_fmir::value::ValDef;
    let mut by_inst: Vec<Option<fors_fmir::ids::ValId>> = vec![None; decl.insts.len()];
    for (v, row) in decl.vals.all_rows() {
        if let ValDef::Inst(i) = ValDef::decode(row.def)
            && (i.index()) < by_inst.len()
        {
            by_inst[i.index()] = Some(v);
        }
    }
    let mut text: std::collections::HashMap<u32, String> = std::collections::HashMap::new();
    let mut last = None;
    for (id, row) in decl.insts.all_rows() {
        let Some(v) = by_inst[id.index()] else {
            continue;
        };
        let rendered = match row.op {
            fors_fmir::op::Op::Field => format!("x{}", row.b),
            op if op.is_trapping_arith()
                || matches!(
                    op,
                    fors_fmir::op::Op::Fadd(_)
                        | fors_fmir::op::Op::Fsub(_)
                        | fors_fmir::op::Op::Fmul(_)
                        | fors_fmir::op::Op::Fdiv(_)
                        | fors_fmir::op::Op::Frem(_)
                ) =>
            {
                let l = text.get(&row.a)?.clone();
                let r = text.get(&row.b)?.clone();
                last = Some(format!("({l} {r})"));
                last.clone().unwrap()
            }
            _ => continue,
        };
        text.insert(v.0, rendered);
    }
    last
}

const REDUCE_OVER_ARRAY: &str = "\
//! name: probe-reduce-comptime-n
//! rule: 03.R12
//! expect: run-ok
//! detail: ok

module m;
needs { io.stdout };
use std.io;

fn main(inout out: io.Stdout) {
    var data: Array[f64, 7] = [1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0];
    var r: f64 = reduce(-, data);
    if r == 83.0 {
        out.write_line(\"ok\");
    } else {
        out.write_line(\"fail\");
    }
}
";

#[test]
fn comptime_known_n_lowers_to_the_explicit_tree() {
    // ch03 R12, as reworded by owner decision Q3 (2026-10-02): "where `n`
    // is comptime-known the tree MUST be explicit". `Array[f64, 7]` carries
    // its length in its type, so lowering emits the tree itself — no
    // `reduce_tree` instruction at all — and the chain it emits is
    // byte-for-byte `fors_fmir::reduce::unrolled(7, B, L)`.
    let mut interner = Interner::new();
    let src = REDUCE_OVER_ARRAY.as_bytes().to_vec();
    let io_src = fs::read(repo_root().join("std/io.fors")).expect("std/io.fors reads");
    let names: Vec<Segments> = vec![
        module_name_of("probe", &src, &mut interner),
        vec![interner.intern(b"std"), interner.intern(b"io")],
    ];
    let sources = [src, io_src];
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let lowered = fors_lower::lower_build(&inputs, &out, &mut interner);
    let main = lowered
        .fns
        .iter()
        .find(|f| f.name == "main")
        .unwrap_or_else(|| panic!("main must lower: {:?}", lowered.diags));
    assert!(
        fors_fmir::verify::verify(&main.decl).is_empty(),
        "the explicit tree must verify clean"
    );
    assert!(
        main.decl
            .insts
            .all_rows()
            .all(|(_, r)| r.op != fors_fmir::op::Op::ReduceTree),
        "a comptime-known `n` emits no `reduce_tree` instruction"
    );
    let want = fors_fmir::reduce::render(
        &fors_fmir::reduce::unrolled(
            7,
            fors_fmir::reduce::REDUCE_BLOCK,
            fors_fmir::reduce::REDUCE_LANES,
        )
        .unwrap(),
    );
    assert_eq!(
        sexpr_of_last_binary(&main.decl).as_deref(),
        Some(want.as_str()),
        "the emitted chain must be the normative explicit tree"
    );
    // And it runs to the same pinned value the `Slice` form gives.
    check_source(
        "reduce-over-array",
        "probe",
        REDUCE_OVER_ARRAY,
        &HostEnv::default(),
    );
}

#[test]
fn runtime_n_emits_one_reduce_tree_with_literal_b_and_l() {
    // The other branch: a `Slice[f64]` operand has no comptime length, so
    // the shape travels as `reduce_tree`'s own `(B, L)` literal operands —
    // "given its final shape in FMIR ... before parallel lowering".
    let path = repo_root().join("tests/conformance/03-numerics/reduce-n7-shape-run-ok.fors");
    let src = fs::read_to_string(&path).expect("corpus file reads");
    let mut interner = Interner::new();
    let bytes = src.as_bytes().to_vec();
    let io_src = fs::read(repo_root().join("std/io.fors")).expect("std/io.fors reads");
    let names: Vec<Segments> = vec![
        module_name_of("reduce-n7", &bytes, &mut interner),
        vec![interner.intern(b"std"), interner.intern(b"io")],
    ];
    let sources = [bytes, io_src];
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let lowered = fors_lower::lower_build(&inputs, &out, &mut interner);
    let main = lowered.fns.iter().find(|f| f.name == "main").expect("main");
    let reduces: Vec<_> = main
        .decl
        .insts
        .all_rows()
        .filter(|(_, r)| r.op == fors_fmir::op::Op::ReduceTree)
        .collect();
    assert_eq!(reduces.len(), 1, "one `reduce` call -> one `reduce_tree`");
    let row = &main.decl.insts.reduces[reduces[0].1.a as usize];
    assert_eq!(row.b, fors_fmir::reduce::REDUCE_BLOCK);
    assert_eq!(row.l, fors_fmir::reduce::REDUCE_LANES);
    assert_eq!(
        row.identity.0,
        fors_fmir::ids::ABSENT,
        "no `identity:` was written"
    );
}

// -- block layout regression (found by the F5 verifier, pre-existing) -------

/// An `if` nested in a THEN-branch. Its three blocks are sealed before the
/// enclosing else-block is entered, so block-id order is not emission
/// order; `BlockDraft::first` is recorded at `seal` for exactly this.
/// Before that fix the else-block's range covered the inner then-block's
/// instructions and this program printed `inner-else`.
const NESTED_IF_IN_THEN: &str = "\
//! name: probe-nested-if-in-then
//! rule: 05.R1
//! expect: run-ok
//! detail: ok

module m;
needs { io.stdout };
use std.io;

fn main(inout out: io.Stdout) {
    var a: f64 = 1.0;
    var w: f64 = 1.0;
    if a == 1.0 {
        if a == w {
            out.write_line(\"ok\");
        } else {
            out.write_line(\"inner-else\");
        }
    } else {
        out.write_line(\"outer-else\");
    }
}
";

#[test]
fn probe_nested_if_in_then_branch_runs_the_inner_then() {
    check_source(
        "nested-if-in-then",
        "probe",
        NESTED_IF_IN_THEN,
        &HostEnv::default(),
    );
}
