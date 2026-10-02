//! F1, F2, F3, F4, F5, F6 and F7 gate tests, driven end to end against the REAL
//! conformance corpus files (design §9's per-increment GATE lists are the
//! acceptance criteria),
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

/// A directive's `detail`, as BYTES: `\n` in the line is a real newline
/// (ch01 R23a's defer tests pin several lines in one `detail`, e.g.
/// `3\n2\n1`). `\\` escapes a literal backslash; nothing else is special.
fn detail_bytes(detail: &str) -> Vec<u8> {
    let mut out = Vec::new();
    let mut it = detail.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.extend_from_slice(c.to_string().as_bytes());
            continue;
        }
        match it.next() {
            Some('n') => out.push(b'\n'),
            Some('t') => out.push(b'\t'),
            Some('\\') => out.push(b'\\'),
            Some(other) => {
                out.push(b'\\');
                out.extend_from_slice(other.to_string().as_bytes());
            }
            None => out.push(b'\\'),
        }
    }
    out
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
    /// Every byte the program wrote through a `write_*` stand-in, whatever
    /// the outcome. §7.2a lets a `trap` test assert the content of the
    /// lines BEFORE the trap line, which is exactly how `trap-runs-no-defer`
    /// and `10-std/defer-not-run-on-trap` observe that no deferred body
    /// ran; F1's §5.8 stand-in routes `Stderr.write_line` through the same
    /// `stdout_write_line` intrinsic, so this image is where those lines
    /// would appear if a body HAD run.
    written: Vec<u8>,
    /// F3: what the RUNTIME wrote to the standard error descriptor — ch02
    /// R17(b)'s one `error: ` line on an error exit of `main`.
    stderr: Vec<u8>,
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
    // F-mono: an instantiated body's types live in the lowering-owned store.
    let tys = lowered.tys;
    let names = lowered.names;
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
    let prog = Program::entry_by_name(fns, "main", Config::v0_1())
        .expect("a main")
        .with_names(names);
    let outcome = run_with_host(&prog, &tys, host).expect("a verified program runs");
    let written = outcome.stdout.clone();
    let stderr = outcome.stderr.clone();
    let observed = match entry_exit(&outcome) {
        ExitStatus::Trap(k) => Observed::Trap(k),
        ExitStatus::Status(code) => Observed::Status(code, outcome.stdout),
    };
    Run {
        observed,
        contract_checks,
        written,
        stderr,
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
                // `detail` names the LINES' text; stdout is those lines
                // each followed by `write_line`'s own `\n` (§7.2a:
                // `run-ok` compares bytes equal to `detail`). A `detail`
                // with embedded `\n`s (ch01 R23a's defer order tests) is
                // several lines, so the separator is a real newline too.
                let mut expected = detail_bytes(&d.detail);
                expected.push(b'\n');
                assert_eq!(*stdout, expected, "{label}: stdout");
            }
        }
        "run-error" => assert_run_error(label, &d, &run),
        other => panic!("{label}: unhandled expect kind {other:?}"),
    }
    run
}

/// design §7.2a's `run-error` row. Two shapes:
/// - `detail: status: N` (ch10 R40(d)'s latched-`Stdout` row, F2): the exit
///   status is `N`;
/// - otherwise (ch02 R17, F3): the status is 1 and the LAST line of the
///   process's stderr equals `detail` — "last", because `main`'s own deferred
///   bodies may write to `Stderr` first (`main-raises-after-defer-run-error`).
///   The runtime's line is the whole of [`Run::stderr`], so it must also be
///   exactly ONE line.
fn assert_run_error(label: &str, d: &Directive, run: &Run) {
    let Observed::Status(code, _) = run.observed else {
        panic!("{label}: expected run-error, got {:?}", run.observed);
    };
    if let Some(status) = d.detail.strip_prefix("status:") {
        let want: i32 = status.trim().parse().expect("status is an int");
        assert_eq!(code, want, "{label}: exit status");
        return;
    }
    assert_eq!(
        code, 1,
        "{label}: an error out of `main` exits 1 (ch02 R17(c))"
    );
    let text = String::from_utf8_lossy(&run.stderr);
    assert!(
        text.ends_with('\n') && text.matches('\n').count() == 1,
        "{label}: ch02 R17(b) writes exactly ONE line, got {text:?}"
    );
    let last = text
        .trim_end_matches('\n')
        .rsplit('\n')
        .next()
        .unwrap_or("");
    assert_eq!(
        last, d.detail,
        "{label}: the last stderr line (design §7.2a)"
    );
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
    // The program AND `std` must check clean, save for the listed
    // owner-decision conflicts in `std` (`STD_OWNER_CONFLICTS`).
    let (check_diags, _) = split_std_owner_conflicts(&inputs, &interner, &out.diagnostics);
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
    // F-mono: an instantiated body's types live in the lowering-owned store.
    let tys = lowered.tys;
    let names = lowered.names;
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
    let prog = Program::entry_by_name(fns, "main", Config::v0_1())
        .expect("a main")
        .with_names(names);
    let outcome = run_with_host(&prog, &tys, host).expect("a verified program runs");
    let written = outcome.stdout.clone();
    let stderr = outcome.stderr.clone();
    let observed = match entry_exit(&outcome) {
        ExitStatus::Trap(k) => Observed::Trap(k),
        ExitStatus::Status(code) => Observed::Status(code, outcome.stdout),
    };
    Run {
        observed,
        contract_checks,
        written,
        stderr,
    }
}

fn names_debug(inputs: &[FileInput], i: usize) -> String {
    format!("{:?}", inputs[i].name)
}

/// The `std` diagnostics that stay until the owner decides (I8b; the same
/// rows as `STD_CONFLICTS` in fors-check's `conformance.rs`): `Vec.push`
/// (std.mem.vec, parameter `v`) and `Map.insert` (std.mem.hashmap,
/// parameter `k`) drop a sunk parameter on the allocation-failure exit,
/// which ch01 R22c forbids for a rigid `T` — as true of the real body
/// (reserve, then store) as of the `// STUB` raise, because the failure
/// exit exists either way; only a signature change fixes it (hand the value
/// back in the error, a `Droppable` bound, or a reserve-first total push).
/// Each row is `(module, dropped parameter)`. This list MUST shrink the
/// moment the owner decides, and MUST never grow.
const STD_OWNER_CONFLICTS: &[(&str, &str)] = &[("std.mem.vec", "v"), ("std.mem.hashmap", "k")];

/// Splits a build's check diagnostics into everything that is NOT a listed
/// owner conflict (formatted, to be asserted empty) and the listed rows
/// that were seen — matched by the module's resolved name, the code and
/// the parameter dropped at a `raise`, never by position, so an incidental
/// line shift elsewhere in `std` cannot mask a real regression.
fn split_std_owner_conflicts<'a>(
    inputs: &[FileInput],
    interner: &Interner,
    diags: &[fors_check::Diagnostic],
) -> (Vec<String>, Vec<&'a (&'a str, &'a str)>) {
    let module_name = |i: usize| -> String {
        inputs[i]
            .name
            .iter()
            .map(|s| String::from_utf8_lossy(interner.resolve(*s)).into_owned())
            .collect::<Vec<_>>()
            .join(".")
    };
    let mut seen = Vec::new();
    let mut rest = Vec::new();
    for d in diags {
        let module = module_name(d.file.index());
        let code = d.code.as_string();
        let hit = STD_OWNER_CONFLICTS.iter().find(|(m, p)| {
            code == "T0057"
                && module == *m
                && d.message.contains(&format!("`{p}`"))
                && d.message.contains("dropped at the `raise`")
        });
        match hit {
            Some(h) => seen.push(h),
            None => rest.push(format!("{module}:{}: {code}: {}", d.start, d.message)),
        }
    }
    (rest, seen)
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
            // README §7.2a: `run-ok`'s stdout bytes equal `detail` (`(no
            // output)` = empty). `detail` names the printed TEXT: a program
            // that prints with `write_line` ends it with that call's own
            // `\n` (F2's `check_source` appends exactly one), while an F7
            // test may print with `write_uint`, which adds none
            // (`str-index-is-bytes-run-ok`). So one trailing `\n`, when
            // present, is `write_line`'s and not part of the text.
            let expected: &[u8] = if d.detail == "(no output)" {
                b""
            } else {
                d.detail.as_bytes()
            };
            let text = stdout.strip_suffix(b"\n").unwrap_or(&stdout[..]);
            assert_eq!(text, expected, "{rel}: stdout");
        }
        "run-error" => assert_run_error(rel, &d, &run),
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

    // I8b (ch01 R22 linear obligations): `std/` must check clean EXCEPT for
    // exactly the `STD_OWNER_CONFLICTS` rows, each of which must still be
    // reported — a row that goes quiet is deleted here and in fors-check's
    // `STD_CONFLICTS`, never left stale.
    let (check_diags, seen) = split_std_owner_conflicts(&inputs, &interner, &out.diagnostics);
    assert!(
        check_diags.is_empty(),
        "std/ must check clean outside the listed owner-decision conflicts: {check_diags:#?}"
    );
    for row in STD_OWNER_CONFLICTS {
        assert!(
            seen.contains(&row),
            "expected the {} owner-decision conflict (parameter `{}` dropped at a `raise`) to \
             still be reported; if it is gone, DELETE its row in STD_OWNER_CONFLICTS and the \
             matching STD_CONFLICTS row in fors-check's conformance.rs instead of leaving it stale",
            row.0,
            row.1
        );
    }
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

/// Ran as of F3: `s.slice(0, 2) else |e| { .. }` is a `try_br` on the call
/// to `Str.slice`'s real body (`std/mem/text.fors`), which `raise`s
/// `Utf8Error.not_a_boundary` into the handler.
#[test]
fn gate_str_slice_non_boundary_raises_run_ok() {
    gate_test_std("10-std/str-slice-non-boundary-raises-run-ok.fors");
}

#[test]
#[ignore = "HELD OUT, with the F-mono reasons REPLACED by two narrower ones \
            (both verified by un-ignoring this test). Monomorphisation is no \
            longer a blocker: F-mono instantiates generic callees, and with \
            it `std`'s own generic bodies lower — `Buffer.empty`, \
            `Buffer.push`, `Buffer.pop`, `Buffer.cap`, `Buffer.into_iter`, \
            `Buffer`'s and `Vec`'s `Index`/`IndexMut` `at`/`at_mut`, \
            `Option.is_some`/`unwrap_or`, `slice.fill`/`swap`/`sort`, \
            `Vec.push`/`pop`/`deinit` and the rest no longer report at all \
            (the std diagnostic list dropped from ~160 rows to the ~44 that \
            were F3's `?`/`raise`, and F3 took it to ONE: `from_utf8`'s \
            value-position `if`). `Buffer.empty`'s self-recursive stand-in \
            is GONE too: `std/mem.fors` now has a real body over the \
            uninitialised-aggregate primitive `buffer_uninit_data`, which \
            lowers to `fors-interp`'s `agg_uninit` (a read before write is \
            `ub: uninit-read` with its site — see `gate.rs`'s \
            `gate_buffer_empty_cells_are_uninitialised_not_zero`, and \
            `gate_buffer_push_pop_index_at_two_instantiations` for \
            push/pop/index on a `Buffer`-shaped type at `[i64, 4]` and \
            `[Str, 2]`). \
            What still blocks this test, both OUTSIDE this increment's \
            editable crates: \
            (1) `Buffer` is a ch08 R17 PRELUDE type name, so \
            `fors-resolve` answers `Entity::PreludeType` for it, and \
            `fors-check`'s R45 qualified-call path (`call.rs`'s \
            `qualified_callee`) and its struct-literal path both require an \
            `Entity::Item`. So `Buffer.empty()` is a silent `TY_ERROR` with \
            NO diagnostic even though `std`'s declaration is in the build, \
            and `prescan` refuses `main` with `CheckErrors` before any \
            instantiation question is reached. Verified minimally: a \
            fixture-declared `Vault[T, N]` of the same shape, reached as \
            `Vault.empty()`, lowers and runs; renaming it to `Buffer` makes \
            the same program `CheckErrors`. The fix is one arm in \
            `fors-check`/`fors-resolve`, a parallel increment's crates. \
            (2) `buf[10] = 1` goes through `IndexMut::at_mut`, which \
            returns `scoped(self) Self.Output` — a PLACE — while all four \
            FMIR call opcodes produce a value (design §3.10), so \
            `fors-lower::lower_index_assign` still reports that case by \
            name rather than dropping the store. That is an FMIR surface \
            question (a place-returning call form), not a monomorphisation \
            one."]
fn gate_buffer_index_past_len_trap() {
    gate_test_std("10-std/buffer-index-past-len-trap.fors");
}

#[test]
#[ignore = "HELD OUT on CHECKER defects (re-verified by un-ignoring after \
            F3, which lowers `?`/`else |e|`/`raise` and is no longer a \
            reason): (1) `step`'s `raise AllocError.out_of_memory;` through \
            `use std.mem;` leaves a node `TY_ERROR` with no diagnostic \
            (`fors-lower` refuses `step` with `CheckErrors`) — the same \
            prelude-opaque `AllocError` path that makes a signature's \
            `raises AllocError` lower to `TY_ERROR` (see \
            `gate_main_raises_std_error_run_error`); (2) the handler on \
            `mem.iter(xs).try_for_each(step) else |e| { .. }` gets no D10 \
            `HandlerRow`, so `main` is refused with the named \
            `LowerError::Failure(\"an `else |e|` handler the checker \
            published no D10 row for\")`. Both are fors-check's."]
fn gate_try_for_each_error_propagates_run_ok() {
    gate_test_std("10-std/try-for-each-error-propagates-run-ok.fors");
}

#[test]
#[ignore = "HELD OUT on a CHECKER defect (re-verified by un-ignoring after \
            F3): `main` is `CheckErrors` — `Vec.new()` is R45's qualified \
            form on the PRELUDE type name `Vec`, the silent `TY_ERROR` \
            described on `gate_buffer_index_past_len_trap`. The older \
            reasons are gone: `?`/`try_br` lower as of F3, the allocator \
            obligation machinery is F6's and in, monomorphisation exists, \
            and `&x` arguments lower (F6)."]
fn gate_vec_deinit_empty_nonempty_trap() {
    gate_test_std("10-std/vec-deinit-empty-nonempty-trap.fors");
}

/// `tests/conformance/README.md`: "A `status: 2` test is run with the
/// standard OUTPUT descriptor closed". A real pipe whose read end is
/// closed before `main` runs; the shim's `SIG_IGN` is what makes the
/// write come back as `EPIPE` (latched, ch10 R39) instead of killing the
/// process, and the test starts from `SIG_DFL` to prove that.
#[cfg(unix)]
// Signal dispositions are process-wide and the test harness runs tests
// concurrently: serialise every DFL -> IGN -> write window so one test's
// reset can never land inside another's (`gate_test_closed_stdout` and F3's
// `f3_latched_stdout_then_raise_exits_1_and_stdout_precedes_the_error_line`).
static SIGPIPE_WINDOW: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn gate_test_closed_stdout(rel: &str) {
    use std::os::fd::AsRawFd;
    let _guard = SIGPIPE_WINDOW.lock().unwrap_or_else(|p| p.into_inner());
    let was = fors_interp::shim::set_sigpipe(fors_interp::shim::SIG_DFL);
    fors_interp::install_sigpipe_ignore();
    let (reader, writer) = std::io::pipe().expect("a pipe");
    drop(reader);
    let host = HostEnv {
        stdout_fd: Some(writer.as_raw_fd()),
        ..HostEnv::default()
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
        ..HostEnv::default()
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
// One documented stand-in carries these files, in the genre F2 established
// for `Buffer.fixed` (design §5.8) — the other, [HOLE-7]'s hard-coded
// `reduce` typing, is gone: I10 publishes a D11 `ReduceRow` per call and F3
// lowers from it:
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

// ---- F1's gate (design §9, the "F1" paragraph) ---------------------------
//
// The F1 increment's acceptance criterion is a named list of 19 corpus
// tests. Eighteen of them run here through the same `gate_test` runner F2
// and F5 use; the nineteenth is held out with its reason on the `#[ignore]`.
// Until this increment they had no `#[test]` wiring them up at all: only
// `float-default-no-fma-run-ok` and `02-failure/trap-overflow` existed
// anywhere, as inline-source probes in `crates/fors-lower/tests/gate.rs`.

#[test]
fn gate_overflow_trap_add() {
    gate_test("03-numerics/overflow-trap-add.fors");
}

#[test]
fn gate_overflow_trap_sub() {
    gate_test("03-numerics/overflow-trap-sub.fors");
}

#[test]
fn gate_overflow_trap_mul() {
    gate_test("03-numerics/overflow-trap-mul.fors");
}

#[test]
fn gate_div_zero_trap() {
    gate_test("03-numerics/div-zero-trap.fors");
}

#[test]
fn gate_shift_width_trap() {
    gate_test("03-numerics/shift-width-trap.fors");
}

#[test]
fn gate_checked_as_exact_accepted_run_ok() {
    gate_test("03-numerics/checked-as-exact-accepted-run-ok.fors");
}

#[test]
fn gate_checked_as_lossy_trap() {
    gate_test("03-numerics/checked-as-lossy-trap.fors");
}

#[test]
fn gate_wrap_add_no_trap_run_ok() {
    gate_test("03-numerics/wrap-add-no-trap-run-ok.fors");
}

#[test]
fn gate_sat_add_saturates_run_ok() {
    gate_test("03-numerics/sat-add-saturates-run-ok.fors");
}

#[test]
fn gate_wrap_as_truncates_run_ok() {
    gate_test("03-numerics/wrap-as-truncates-run-ok.fors");
}

#[test]
fn gate_sat_as_clamps_run_ok() {
    gate_test("03-numerics/sat-as-clamps-run-ok.fors");
}

#[test]
fn gate_trunc_as_truncates_run_ok() {
    gate_test("03-numerics/trunc-as-truncates-run-ok.fors");
}

#[test]
fn gate_implicit_widen_with_as_accepted() {
    gate_test("03-numerics/implicit-widen-with-as-accepted.fors");
}

#[test]
fn gate_int_fixed_width_i64_accepted_run_ok() {
    gate_test("03-numerics/int-fixed-width-i64-accepted-run-ok.fors");
}

/// ch03 R9: `N as i32` from a `comptime_int` constant is the converted
/// CONSTANT, folded at lowering (`FnLower::fold_comptime_cast`). Ran as of
/// F3: I10 made `comptime_int` a resolved prelude type, and the checker folds
/// the constant's value.
#[test]
fn gate_comptime_int_explicit_conversion_accepted() {
    gate_test("03-numerics/comptime-int-explicit-conversion-accepted.fors");
}

#[test]
fn gate_float_default_no_fma_run_ok() {
    gate_test("03-numerics/float-default-no-fma-run-ok.fors");
}

#[test]
fn gate_fastmath_scope_ends_run_ok() {
    gate_test("03-numerics/fastmath-scope-ends-run-ok.fors");
}

#[test]
fn gate_plain_for_accumulator_accepted_run_ok() {
    gate_test("03-numerics/plain-for-accumulator-accepted-run-ok.fors");
}

#[test]
fn gate_trap_overflow() {
    gate_test("02-failure/trap-overflow.fors");
}

// ---------------------------------------------------------------- F4's gate
//
// design §9's F4 list, the LOWERING half: `defer`/`errdefer` read from the
// checker's D7 facts, one FMIR scope per `defer` statement so ch01 R23a's
// textual cut is structural, and an exit edge on every static exit carrying
// the pending bodies in R23a's order.
//
// The last two of the nine were held out on F3's failure edges and run as of
// F3: `01-ownership/errdefer-skipped-on-return-run-ok` is written with an
// `else |e| { }` handler (a normal exit: the `errdefer` stays pending) and
// `02-failure/main-raises-after-defer-run-error` with `raise` out of `main`
// (an error exit: the `defer` runs BEFORE ch02 R17's line).

#[test]
fn gate_errdefer_skipped_on_return_run_ok() {
    gate_test("01-ownership/errdefer-skipped-on-return-run-ok.fors");
}

#[test]
fn gate_main_raises_after_defer_run_error() {
    gate_test("02-failure/main-raises-after-defer-run-error.fors");
}

#[test]
fn gate_defer_reverse_order_run_ok() {
    gate_test("01-ownership/defer-reverse-order-run-ok.fors");
}

#[test]
fn gate_defer_runs_on_return_run_ok() {
    gate_test("01-ownership/defer-runs-on-return-run-ok.fors");
}

#[test]
fn gate_defer_per_iteration_run_ok() {
    gate_test("01-ownership/defer-per-iteration-run-ok.fors");
}

#[test]
fn gate_defer_nested_scope_order_run_ok() {
    gate_test("01-ownership/defer-nested-scope-order-run-ok.fors");
}

#[test]
fn gate_defer_result_evaluated_first_run_ok() {
    gate_test("01-ownership/defer-result-evaluated-first-run-ok.fors");
}

/// ch02 R7 / design §5.3: a `trap` has no successor, so it runs NO deferred
/// body. §7.2a makes the absence observable — the marker would be among the
/// lines before the trap line — and that is what this asserts, not merely
/// the trap kind.
#[test]
fn gate_trap_runs_no_defer() {
    let run = check_corpus_file("02-failure/trap-runs-no-defer.fors", &HostEnv::default());
    assert!(
        !String::from_utf8_lossy(&run.written).contains("cleanup"),
        "a trap runs no deferred body (ch02 R7), so `cleanup` must not have been written: {:?}",
        String::from_utf8_lossy(&run.written)
    );
}

#[test]
fn gate_defer_not_run_on_trap() {
    let run = check_corpus_file("10-std/defer-not-run-on-trap.fors", &HostEnv::default());
    assert!(
        !String::from_utf8_lossy(&run.written).contains("cleanup"),
        "ch10 R40(b), ch02 R7: no deferred body runs on the trap path: {:?}",
        String::from_utf8_lossy(&run.written)
    );
}

/// F4's verifier obligation, over the WHOLE corpus: "the verifier check
/// that every exit edge carries exactly the right multiset" (design §9's
/// F4). Every `.fors` file under `tests/conformance` that lowers at all is
/// walked, and for each lowered declaration this asserts, against
/// `fors_fmir::exit::expected_pending` directly and not only through
/// `verify()`:
///
/// - every exit edge's `pending` IS `expected_pending`'s answer for the
///   scopes it leaves and its kind (ch01 R23a's reverse textual order, R23b's
///   `errdefer`-only-on-error filter);
/// - every `DeferRow` in the pool is reached by at least one edge — a body
///   the lowering recorded but no exit ever runs would be a silently dropped
///   `defer`, which `verify()` cannot see;
/// - a `trap`-terminated block carries NO edge at all (ch01 R23f, ch02 R7:
///   a trap runs no deferred body);
/// - one FMIR scope per `DeferRow` beyond the body's root, which is how ch01
///   R23a's textual cut is made structural rather than filtered.
///
/// It also prints F4's COUNTER (design §9, risk R6): what inlining the
/// bodies at every edge would cost as a ratio of body size. Lowering emits
/// one copy per body and jumps to it (ch01 R23a's explicitly permitted
/// form), so the ratio is what the OTHER form would have added.
#[test]
fn f4_exit_edges_carry_expected_pending_over_the_corpus() {
    let root = repo_root().join("tests/conformance");
    let mut files: Vec<PathBuf> = Vec::new();
    collect_fors(&root, &mut files);
    files.sort();
    assert!(files.len() > 50, "the corpus should be found: {files:?}");
    let mut with_defers = 0usize;
    let mut edges_checked = 0usize;
    let mut body_insts = 0u64;
    let mut inlined_insts = 0u64;
    let mut decl_insts = 0u64;
    for path in &files {
        let Ok(src) = fs::read(path) else { continue };
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        let Some(lowered) = try_lower(&stem, &src) else {
            continue;
        };
        for f in &lowered {
            let decl = &f.decl;
            decl_insts += decl.insts.len() as u64;
            let n_defers = decl.defers.len() as u32;
            if n_defers > 0 {
                with_defers += 1;
            }
            // ch01 R23a's textual cut, made structural: NO scope holds two
            // `defer` rows, so the scopes an exit leaves ARE the bodies
            // whose statement precedes it and innermost-first IS reverse
            // textual order. (A `with arena`/`with allocator` block adds a
            // scope of its own, so the count is a bound, not an equality.)
            assert!(
                decl.scopes.len() as u32 > n_defers,
                "{}: {n_defers} `defer` rows need at least that many scopes plus the \
                 body's root",
                f.name
            );
            for (id, scope) in decl.scopes.all_rows() {
                assert!(
                    scope.defers.end.saturating_sub(scope.defers.start) <= 1,
                    "{}: scope {} holds more than one `defer` row, which would need \
                     ch01 R23a's textual cut as a second filter",
                    f.name,
                    id.0
                );
            }
            let mut seen = vec![false; n_defers as usize];
            for (id, row) in decl.exits.all_rows() {
                edges_checked += 1;
                let leaving = decl.exits.scopes(row.scopes.clone());
                let want = fors_fmir::exit::expected_pending(
                    &decl.scopes,
                    &decl.defers,
                    leaving,
                    row.kind,
                );
                let got = decl.exits.pending(row.pending.clone()).to_vec();
                assert_eq!(
                    got, want,
                    "{}: exit edge {} carries the wrong pending multiset",
                    f.name, id.0
                );
                let term = decl.blocks.row(row.from).term.op;
                assert_ne!(
                    term,
                    fors_fmir::op::Op::Trap,
                    "{}: a `trap` is not an exit (ch01 R23f, ch02 R7)",
                    f.name
                );
                for d in &got {
                    if (d.0 as usize) < seen.len() {
                        seen[d.0 as usize] = true;
                    }
                    let body = decl.defers.get(d.0..d.0 + 1)[0].body;
                    inlined_insts += u64::from(decl.blocks.row(body).inst_len);
                }
            }
            for (i, hit) in seen.iter().enumerate() {
                let row = decl.defers.get(i as u32..i as u32 + 1)[0];
                // An `ErrDefer` body on no edge is CORRECT (ch01 R23b: it runs
                // on error exits only, and a body whose function has no error
                // exit — `handler-makes-normal-exit` — has none). A plain
                // `defer` on no edge would be a dropped body.
                assert!(
                    *hit || row.kind == fors_fmir::scope::DeferKind::ErrDefer,
                    "{}: defer row {i} is on no exit edge, so its body would never run",
                    f.name
                );
                body_insts += u64::from(decl.blocks.row(row.body).inst_len);
            }
        }
    }
    assert!(
        with_defers >= 6,
        "the corpus's `defer` files should lower: only {with_defers} bodies carried a \
         `DeferRow`"
    );
    assert!(edges_checked >= with_defers, "every edge is checked");
    let ratio = if decl_insts == 0 {
        0.0
    } else {
        inlined_insts as f64 / decl_insts as f64
    };
    println!(
        "F4 COUNTER (design §9, risk R6): inlined-body growth = {inlined_insts} instructions \
         across {edges_checked} exit edges against {decl_insts} lowered instructions = \
         {ratio:.4}x of body size. Emitted instead as {body_insts} instructions of \
         one-copy-per-body (ch01 R23a's \"emit one copy and jump to it\"), i.e. \
         {:.4}x.",
        if decl_insts == 0 {
            0.0
        } else {
            body_insts as f64 / decl_insts as f64
        }
    );
    assert!(
        ratio < 1.0,
        "F4's R6 risk: inlining every pending body would more than double the corpus's \
         lowered size ({ratio:.4}x)"
    );
}

/// Every `.fors` file under `dir`, recursively.
fn collect_fors(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect_fors(&p, out);
        } else if p.extension().map(|x| x == "fors").unwrap_or(false) {
            out.push(p);
        }
    }
}

/// Parse + resolve + check + lower, returning the lowered functions when
/// the pipeline got that far and `None` when it did not. Unlike
/// [`build_and_run`] this asserts nothing: the corpus holds deliberate
/// parse-error and check-error files, and an F4 property is about the
/// bodies that DO lower.
fn try_lower(stem: &str, src: &[u8]) -> Option<Vec<fors_lower::LoweredFn>> {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.to_vec()];
    let mut names: Vec<Segments> = vec![module_name_of(stem, src, &mut interner)];
    if String::from_utf8_lossy(src).contains("use std.io;") {
        let io_path = repo_root().join("std/io.fors");
        let io_src = fs::read(&io_path).ok()?;
        let name: Segments = vec![interner.intern(b"std"), interner.intern(b"io")];
        sources.push(io_src);
        names.push(name);
    }
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    if parsed.iter().any(|p| !p.diags.is_empty()) {
        return None;
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let lowered = fors_lower::lower_build(&inputs, &out, &mut interner);
    for f in &lowered.fns {
        let diags = fors_fmir::verify::verify(&f.decl);
        assert!(
            diags.is_empty(),
            "{stem}: lowered {} must verify clean: {diags:?}",
            f.name
        );
    }
    Some(lowered.fns)
}

// ---------------------------------------------------------------- F6's gate
//
// design §9's F6 list, the LOWERING half: `with arena`/`with allocator` and
// their fresh brands, `arena_alloc`/`arena_deref`/`arena_reset`, `@alloc`/
// `@free` through the allocator intrinsics, and the obligation/discharge
// machinery of D8. The interpreter half (`ArenaVal`/`RefVal`, generation
// checks, the `ub:` reports, the borrow stack's SharedRO groups) landed
// earlier on hand-written FMIR fixtures; these are the SOURCE-level twins.

#[test]
fn gate_arena_generation_trap() {
    gate_test("01-ownership/arena-generation-trap.fors");
}

/// F6's D8 obligation machinery, over the whole corpus: **no obligation is
/// left undischarged on any exit edge**, which is the lowering-side half of
/// "a leak is impossible by construction (the checker rejected it)". ch01
/// R22i rejects a leak before lowering sees the body, so an edge missing a
/// discharge would be a compiler bug — and design §3.5/§5.2 are explicit
/// that such a bug is `ub: linear-leak`, status 70, and **never a trap**:
/// ch02 R15's kind list is closed at eight. That last clause is
/// `ub_linear_leak_is_not_a_trap` re-asserted at the lowering boundary.
#[test]
fn f6_no_obligation_is_undischarged_and_a_leak_is_not_a_trap() {
    let root = repo_root().join("tests/conformance");
    let mut files: Vec<PathBuf> = Vec::new();
    collect_fors(&root, &mut files);
    files.sort();
    let mut obligations_seen = 0usize;
    for path in &files {
        let Ok(src) = fs::read(path) else { continue };
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        let Some(lowered) = try_lower(&stem, &src) else {
            continue;
        };
        for f in &lowered {
            let decl = &f.decl;
            for (id, row) in decl.exits.all_rows() {
                let leaving = decl.exits.scopes(row.scopes.clone());
                let mut owed: Vec<fors_fmir::ids::PlaceId> = Vec::new();
                for s in leaving {
                    owed.extend_from_slice(decl.obligations.get(decl.scopes.row(*s).obligations));
                }
                let got = decl.exits.discharges(row.discharges.clone());
                obligations_seen += owed.len();
                for p in &owed {
                    assert!(
                        got.iter().any(|d| d.place == *p),
                        "{}: exit edge {} leaves place {} with an undischarged linear \
                         obligation (ch01 R22h); the checker rejected every leak, so this \
                         would be a compiler bug",
                        f.name,
                        id.0,
                        p.0
                    );
                }
            }
        }
    }
    // `ub_linear_leak_is_not_a_trap`, at this boundary: the class the
    // interpreter would report is not one of ch02 R15's eight trap kinds.
    assert!(
        !fors_fmir::op::TrapKind::KINDS.contains(&fors_interp::UbClass::LinearLeak.as_str()),
        "a linear leak is a `ub:` report, never a trap (ch02 R15's list is closed at eight)"
    );
    println!("F6: {obligations_seen} obligation-edge pairs checked over the corpus");
}

// ------------------------------------------------------- the lowering counter
//
// design §9's F3 asks for a COUNTER in the gate output: how many corpus
// targets fail to lower. A "target" is one function body of a corpus file
// whose build checks clean (the corpus also holds deliberate parse-error and
// check-error files, whose bodies lowering never sees), plus every body of
// the `std` package built as a consuming program builds it. Each refusal is
// a named `LowerError`; the census groups them by variant and prints the
// totals, so the next increment can see what remains without re-running a
// hand experiment.
//
// Measured when F3 landed: BEFORE, 552 corpus bodies (482 check-clean files)
// plus 43 std bodies were refused, 409 + 43 of them `Failure` (`?`/`else
// |e|`/`raise`; most corpus rows are `std/io.fors`'s nine raising bodies,
// built with every file that names `use std.io;`). AFTER, 143 + 1, and no
// `Failure` at all; the census asserts that last fact, so a ch02 form that
// stops lowering is a test failure, not a number nobody reads.

/// One refusal row: `(target label, function name, error)`.
type Refusal = (String, String, fors_lower::LowerError);

/// The bodies of `src` (plus `std/io.fors` when it names it) that do NOT
/// lower, when the build checks clean; `None` when it does not.
fn census_file(stem: &str, src: &[u8]) -> Option<Vec<Refusal>> {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.to_vec()];
    let mut names: Vec<Segments> = vec![module_name_of(stem, src, &mut interner)];
    if String::from_utf8_lossy(src).contains("use std.io;") {
        sources.push(fs::read(repo_root().join("std/io.fors")).ok()?);
        names.push(vec![interner.intern(b"std"), interner.intern(b"io")]);
    }
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    if parsed.iter().any(|p| !p.diags.is_empty()) {
        return None;
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    if resolved.files.iter().any(|f| !f.diagnostics.is_empty()) {
        return None;
    }
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    if !out.diagnostics.is_empty() {
        return None;
    }
    let lowered = fors_lower::lower_build(&inputs, &out, &mut interner);
    Some(
        lowered
            .diags
            .into_iter()
            .map(|d| (stem.to_string(), d.name, d.error))
            .collect(),
    )
}

/// The `std` package's own refusals, built with `std`-prefixed module names
/// exactly as [`std_checks_clean`] builds it.
fn census_std() -> Vec<Refusal> {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    let mut names: Vec<Segments> = Vec::new();
    for (segs, s) in std_module_sources() {
        names.push(segs.iter().map(|b| interner.intern(b)).collect());
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, None, None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let lowered = fors_lower::lower_build(&inputs, &out, &mut interner);
    lowered
        .diags
        .into_iter()
        .map(|d| ("std".to_string(), d.name, d.error))
        .collect()
}

/// A `LowerError`'s variant name, for grouping.
fn refusal_kind(e: &fors_lower::LowerError) -> &'static str {
    use fors_lower::LowerError as L;
    match e {
        L::CheckErrors => "CheckErrors",
        L::Generic(_) => "Generic",
        L::Projection => "Projection",
        L::Closure => "Closure",
        L::Match => "Match",
        L::Failure(_) => "Failure",
        L::Loop => "Loop",
        L::Comptime(_) => "Comptime",
        L::Unsupported(_) => "Unsupported",
        L::Unresolved(_) => "Unresolved",
        L::InvalidUtf8Literal(_) => "InvalidUtf8Literal",
    }
}

#[test]
fn lowering_refusal_counter_over_the_corpus_and_std() {
    let root = repo_root().join("tests/conformance");
    let mut files: Vec<PathBuf> = Vec::new();
    collect_fors(&root, &mut files);
    files.sort();
    let mut corpus: Vec<Refusal> = Vec::new();
    let mut clean_files = 0usize;
    for path in &files {
        let Ok(src) = fs::read(path) else { continue };
        let stem = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .with_extension("")
            .to_string_lossy()
            .into_owned();
        let leaf = path.file_stem().unwrap().to_string_lossy().into_owned();
        if let Some(rows) = census_file(&leaf, &src) {
            clean_files += 1;
            corpus.extend(rows.into_iter().map(|(_, f, e)| (stem.clone(), f, e)));
        }
    }
    let std_rows = census_std();
    let mut by_kind: std::collections::BTreeMap<&str, (usize, usize)> = Default::default();
    for (_, _, e) in &corpus {
        by_kind.entry(refusal_kind(e)).or_default().0 += 1;
    }
    for (_, _, e) in &std_rows {
        by_kind.entry(refusal_kind(e)).or_default().1 += 1;
    }
    println!(
        "LOWERING COUNTER: {} corpus bodies refused across {clean_files} check-clean corpus \
         files; {} std bodies refused",
        corpus.len(),
        std_rows.len()
    );
    for (k, (c, s)) in &by_kind {
        println!("  {k:<12} corpus {c:>3}  std {s:>3}");
    }
    for (t, f, e) in corpus.iter().chain(std_rows.iter()) {
        println!("  refused: {t} :: {f}: {e:?}");
    }
    let failures: Vec<&Refusal> = corpus
        .iter()
        .chain(std_rows.iter())
        .filter(|(_, _, e)| matches!(e, fors_lower::LowerError::Failure(_)))
        .collect();
    assert!(
        failures.is_empty(),
        "F3: every ch02 failure form in a check-clean body lowers; refused: {failures:#?}"
    );
}

// ---------------------------------------------------------------- F3's gate
//
// design §9's F3 list: `try_br`, error edges, at most one `ErrorFrom` per
// edge, the handler form, and ch02 R17's five-step exit sequence with the
// full `render` clause list. Each `run-error` row asserts status 1 and the
// EXACT last stderr line (design §7.2a), which is the runtime's one line.

#[test]
fn gate_main_raises_unit_variant_run_error() {
    gate_test("02-failure/main-raises-unit-variant-run-error.fors");
}

#[test]
fn gate_main_raises_payload_run_error() {
    gate_test("02-failure/main-raises-payload-run-error.fors");
}

#[test]
fn gate_main_raises_nested_payload_run_error() {
    gate_test("02-failure/main-raises-nested-payload-run-error.fors");
}

/// PINNED, not run: the row cannot reach lowering, and the three reasons are
/// all outside F3's crates (verified by running it, and by running a copy
/// with reason (1) corrected):
/// 1. a CORPUS/STD disagreement — the file writes `mem.Counting[mem.Fixed[8]]`
///    while `std/mem.fors` declares `Counting[N: usize, A: brand]` ("Standalone,
///    not a wrapper: ch01 R15a forbids holding a parent allocator in a field"),
///    so the checker correctly reports T0011 ("a type where a constant argument
///    is expected") at the `with allocator` type;
/// 2. with that corrected to `mem.Counting[8]`, `fill`'s signature `raises
///    AllocError` (the prelude-opaque std name, reached through `use std.mem;`)
///    lowers to `TY_ERROR` with NO diagnostic, so `fill(&counting)?` gets no
///    D10 `TryRow` and `fors-lower` refuses `main` with the named
///    `LowerError::Failure("a `?` the checker published no D10 row for")` —
///    a fors-check defect;
/// 3. `fill`'s own body is `TY_ERROR` throughout (`Vec.new()` is R45's
///    qualified call on the PRELUDE type name `Vec`, the silent `TY_ERROR`
///    `gate_vec_deinit_empty_nonempty_trap` documents).
///
/// The rendering this row pins — a std error by its fully-qualified path — is
/// covered at source level by `f3_std_error_renders_by_its_fully_qualified_path`.
/// This test asserts reason (1) exactly, so it fails the moment the corpus or
/// std changes and the row must be re-tried.
#[test]
fn gate_main_raises_std_error_run_error() {
    let path =
        repo_root().join("tests/conformance/02-failure/main-raises-std-error-run-error.fors");
    let src = fs::read(&path).expect("corpus file reads");
    let codes = std_build_check_codes(&src);
    assert_eq!(
        codes,
        vec!["T0011".to_string()],
        "the pinned blocker changed: re-try `gate_test_std` on this row"
    );
}

/// The check diagnostics (codes, owner conflicts excepted) of `src` built
/// with the whole `std` package, as [`build_and_run_with_std`] builds it.
fn std_build_check_codes(src: &[u8]) -> Vec<String> {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.to_vec()];
    let mut names: Vec<Segments> = vec![module_name_of("main", src, &mut interner)];
    for (segs, s) in std_module_sources() {
        names.push(segs.iter().map(|b| interner.intern(b)).collect());
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
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let (rest, _) = split_std_owner_conflicts(&inputs, &interner, &out.diagnostics);
    rest.iter()
        .map(|d| d.split(": ").nth(1).unwrap_or(d).to_string())
        .collect()
}

/// The source-level twin of `main-raises-std-error-run-error`'s rendering
/// (ch02 R17: "an enum value renders as its type's fully-qualified path"): a
/// std error raised by a callee, propagated by `?` with R2's equal types, out
/// of `main`.
#[test]
fn f3_std_error_renders_by_its_fully_qualified_path() {
    const SRC: &[u8] = b"\
module main;
needs { };
use std.mem.alloc;

fn step() raises alloc.AllocError {
    raise alloc.AllocError.too_large;
}

fn main() raises alloc.AllocError {
    step()?;
}
";
    let run = build_and_run_with_std("std_error_path", "main", SRC, &HostEnv::default());
    let Observed::Status(code, ref stdout) = run.observed else {
        panic!("expected status 1, got {:?}", run.observed);
    };
    assert_eq!(code, 1);
    assert_eq!(stdout, b"", "R17(c): nothing is written to `Stdout`");
    assert_eq!(run.stderr, b"error: std.mem.alloc.AllocError.too_large\n");
}

#[test]
fn gate_main_raises_flushes_stdout_run_error() {
    let run = check_corpus_file(
        "02-failure/main-raises-flushes-stdout-run-error.fors",
        &HostEnv::default(),
    );
    // R17(a): the buffered `Stdout` content still arrives.
    assert_eq!(run.written, b"buffered\n", "R17(a): stdout is flushed");
}

#[test]
fn gate_handler_makes_normal_exit() {
    gate_test("02-failure/handler-makes-normal-exit.fors");
}

#[test]
fn gate_main_raises_exit_status_one_run_error() {
    gate_test("10-std/main-raises-exit-status-one-run-error.fors");
}

/// ch02 R17(b)-(c) at the descriptor: the runtime's line goes to the
/// standard error descriptor unbuffered and whole, and when that write fails
/// the status is STILL 1 — no retry, no other destination, no trap. The
/// failing descriptor is one no process opens (EBADF), so nothing else in
/// the harness can be written to by mistake.
#[cfg(unix)]
#[test]
fn f3_error_line_reaches_the_stderr_descriptor_and_a_failed_write_still_exits_1() {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    let rel = "02-failure/main-raises-unit-variant-run-error.fors";
    let (mut reader, writer) = std::io::pipe().expect("a pipe");
    let host = HostEnv {
        stderr_fd: Some(writer.as_raw_fd()),
        ..HostEnv::default()
    };
    let run = check_corpus_file(rel, &host);
    drop(writer);
    let mut got = Vec::new();
    reader.read_to_end(&mut got).expect("the pipe reads");
    assert_eq!(got, b"error: main.Error.boom\n");
    assert_eq!(run.stderr, got, "the captured line is the written one");
    // R17's last paragraph: the write fails (EBADF) and the run still
    // settles at status 1 — `check_corpus_file` asserts the directive.
    let host = HostEnv {
        stderr_fd: Some(1_000_000),
        ..HostEnv::default()
    };
    check_corpus_file(rel, &host);
}

// ------------------------------------------------- F3's verifier probes
//
// Inline programs the corpus gates do not cover, each asserted on the EXACT
// bytes: the `write_line` image (the order every pending body ran in), the
// runtime's one stderr line and the status. Written by F3's independent
// verifier; the shapes it found no corpus row for.

/// One probe: its source, the expected status, the expected `write_line`
/// image and, for status 1, the runtime's exact stderr line.
struct Probe {
    name: &'static str,
    src: &'static str,
    status: i32,
    written: &'static str,
    stderr: &'static str,
}

const F3_PROBES: &[Probe] = &[
    // `?` in a loop under a per-iteration `defer` AND `errdefer`, failing on
    // the second iteration: the first iteration's normal exit runs only its
    // `defer`; the error exit runs both, innermost first (ch01 R23a/R23b),
    // then the function's own, then `main`'s line.
    Probe {
        name: "q_in_loop_error_path",
        src: "module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom }\n\
              fn step(let i: usize) raises E { if i == 1 { raise E.boom; } }\n\
              fn work(inout o: io.Stdout) raises E {\n    defer o.write_line(\"fn-defer\");\n    errdefer o.write_line(\"fn-errdefer\");\n    let n: usize = 3;\n    for i in 0 ..< n {\n        defer o.write_line(\"defer\");\n        errdefer o.write_line(\"errdefer\");\n        o.write_line(\"body\");\n        step(i)?;\n    }\n    o.write_line(\"not reached\");\n}\n\
              fn main(inout o: io.Stdout) raises E { work(&o)?; }\n",
        status: 1,
        written: "body\ndefer\nbody\nerrdefer\ndefer\nfn-errdefer\nfn-defer\n",
        stderr: "error: m.E.boom\n",
    },
    // The same shape on the normal path: no `errdefer` body runs anywhere.
    Probe {
        name: "q_in_loop_normal_path",
        src: "module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom }\n\
              fn step(let i: usize) raises E { if i == 9 { raise E.boom; } }\n\
              fn work(inout o: io.Stdout) raises E {\n    defer o.write_line(\"fn-defer\");\n    errdefer o.write_line(\"fn-errdefer\");\n    let n: usize = 2;\n    for i in 0 ..< n {\n        defer o.write_line(\"defer\");\n        errdefer o.write_line(\"errdefer\");\n        o.write_line(\"body\");\n        step(i)?;\n    }\n    o.write_line(\"end\");\n}\n\
              fn main(inout o: io.Stdout) raises E { errdefer o.write_line(\"main-errdefer\"); work(&o)?; o.write_line(\"main-end\"); }\n",
        status: 0,
        written: "body\ndefer\nbody\ndefer\nend\nfn-defer\nmain-end\n",
        stderr: "",
    },
    // A `?` INSIDE a handler block propagates the second error (ch02 R16:
    // the handler then makes an error exit, so `main`'s `errdefer` runs).
    Probe {
        name: "q_inside_handler_propagates",
        src: "module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom, bang }\n\
              fn a() -> i32 raises E { raise E.boom; }\nfn b() -> i32 raises E { raise E.bang; }\n\
              fn main(inout o: io.Stdout) raises E {\n    errdefer o.write_line(\"main-errdefer\");\n    let n: i32 = a() else |e| { b()? };\n    o.write_line(\"not reached\");\n}\n",
        status: 1,
        written: "main-errdefer\n",
        stderr: "error: m.E.bang\n",
    },
    // A handler that re-raises its binding.
    Probe {
        name: "handler_reraises",
        src: "module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom }\n\
              fn a() raises E { raise E.boom; }\n\
              fn main(inout o: io.Stdout) raises E {\n    errdefer o.write_line(\"main-errdefer\");\n    a() else |e| { o.write_line(\"in-handler\"); raise e; };\n    o.write_line(\"not reached\");\n}\n",
        status: 1,
        written: "in-handler\nmain-errdefer\n",
        stderr: "error: m.E.boom\n",
    },
    // Three frames deep: each frame's bodies run innermost first, callee
    // before caller, all before the runtime's line.
    Probe {
        name: "three_frames_defer_order",
        src: "module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom }\n\
              fn inner(inout o: io.Stdout) raises E {\n    defer o.write_line(\"inner-defer\");\n    errdefer o.write_line(\"inner-errdefer\");\n    raise E.boom;\n}\n\
              fn outer(inout o: io.Stdout) raises E {\n    defer o.write_line(\"outer-defer\");\n    errdefer o.write_line(\"outer-errdefer\");\n    inner(&o)?;\n}\n\
              fn main(inout o: io.Stdout) raises E {\n    defer o.write_line(\"main-defer\");\n    outer(&o)?;\n}\n",
        status: 1,
        written: "inner-errdefer\ninner-defer\nouter-errdefer\nouter-defer\nmain-defer\n",
        stderr: "error: m.E.boom\n",
    },
    // ch01 R23c's own escape inside an `errdefer` body: a handler that
    // neither raises nor returns, walked by the verifier (F3), run here.
    Probe {
        name: "handler_inside_errdefer_body",
        src: "module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom, other }\n\
              fn step2() raises E { raise E.other; }\n\
              fn main(inout o: io.Stdout) raises E {\n    errdefer step2() else |e| { o.write_line(\"handled-in-errdefer\"); };\n    raise E.boom;\n}\n",
        status: 1,
        written: "handled-in-errdefer\n",
        stderr: "error: m.E.boom\n",
    },
    // R17's scalar clauses on one line: a negative integer, `bool`, `()`,
    // every `Str` escape, `u8`'s and `i64`'s extremes.
    Probe {
        name: "render_scalar_clauses",
        src: "module m;\nneeds { };\nenum E { code(i32, bool, (), Str, u8, i64, i64) }\n\
              fn main() raises E {\n    raise E.code(-7, true, (), \"a\\\"b\\\\c\\td\\re\\nf\", 255, 9223372036854775807, -9223372036854775808);\n}\n",
        status: 1,
        written: "",
        stderr: "error: m.E.code(-7, true, (), \"a\\\"b\\\\c\\td\\re\\nf\", 255, 9223372036854775807, -9223372036854775808)\n",
    },
    // A struct payload inside a nested enum, and a tuple payload.
    Probe {
        name: "render_nested_struct_and_tuple",
        src: "module m;\nneeds { };\nstruct P { x: i32, y: i64 }\nenum Inner { deep(P) }\nenum E { wrap(Inner, (i32, bool)) }\n\
              fn main() raises E { raise E.wrap(Inner.deep(P { x: 1, y: -2 }), (3, false)); }\n",
        status: 1,
        written: "",
        stderr: "error: m.E.wrap(m.Inner.deep(m.P{ x: 1, y: -2 }), (3, false))\n",
    },
];

#[test]
fn f3_verifier_probes_run_with_exact_bodies_lines_and_status() {
    for p in F3_PROBES {
        let run = build_and_run(p.name, "m", p.src.as_bytes(), &HostEnv::default());
        let Observed::Status(code, _) = run.observed else {
            panic!("{}: expected a status, got {:?}", p.name, run.observed);
        };
        assert_eq!(code, p.status, "{}: exit status", p.name);
        assert_eq!(
            String::from_utf8_lossy(&run.written),
            p.written,
            "{}: the write_line image",
            p.name
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stderr),
            p.stderr,
            "{}: the runtime's stderr",
            p.name
        );
    }
}

/// ch02 R17(a)-(c) against ch10 R40(d): `Stdout` already LATCHED when `main`
/// raises still exits 1 (R17(c) "whether or not (a) succeeded"), never 2.
/// And with both descriptors on ONE pipe, every `Stdout` byte precedes the
/// runtime's line (R17(a) flushes before (b) writes).
#[cfg(unix)]
#[test]
fn f3_latched_stdout_then_raise_exits_1_and_stdout_precedes_the_error_line() {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    const SRC: &[u8] = b"module m;\nneeds { io.stdout };\nuse std.io;\nenum E { boom }\n\
        fn main(inout out: io.Stdout) raises E { out.write_line(\"one\"); out.write_line(\"two\"); raise E.boom; }\n";
    // One pipe for both descriptors: the order is observable.
    let (mut reader, writer) = std::io::pipe().expect("a pipe");
    let host = HostEnv {
        stdout_fd: Some(writer.as_raw_fd()),
        stderr_fd: Some(writer.as_raw_fd()),
    };
    let run = build_and_run("shared_pipe", "m", SRC, &host);
    drop(writer);
    let mut got = Vec::new();
    reader.read_to_end(&mut got).expect("the pipe reads");
    assert_eq!(got, b"one\ntwo\nerror: m.E.boom\n");
    assert!(matches!(run.observed, Observed::Status(1, _)));
    // The read end closed before `main`: the first write latches (ch10 R39)
    // and the raise still exits 1.
    let _guard = SIGPIPE_WINDOW.lock().unwrap_or_else(|p| p.into_inner());
    let was = fors_interp::shim::set_sigpipe(fors_interp::shim::SIG_DFL);
    fors_interp::install_sigpipe_ignore();
    let (closed_r, closed_w) = std::io::pipe().expect("a pipe");
    drop(closed_r);
    let host = HostEnv {
        stdout_fd: Some(closed_w.as_raw_fd()),
        stderr_fd: None,
    };
    let run = build_and_run("latched_then_raise", "m", SRC, &host);
    assert!(
        matches!(run.observed, Observed::Status(1, _)),
        "R17(c): status 1 even though (a)'s flush had nothing left and `Stdout` was latched: {:?}",
        run.observed
    );
    assert_eq!(run.stderr, b"error: m.E.boom\n");
    drop(closed_w);
    fors_interp::shim::set_sigpipe(was);
}
