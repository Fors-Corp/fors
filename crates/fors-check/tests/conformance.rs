//! The ch09 conformance corpus, checker view (design §11).
//!
//! A test is classified `Rejected(code)` — exactly one diagnostic whose code
//! is the one its `detail` line names — `Accepted` (zero diagnostics), or
//! `Pending(increment)` in [`PENDING_09`], whose length every increment
//! lowers and whose upper bound is asserted here.

use std::fs;
use std::path::{Path, PathBuf};

use fors_index::{Interner, Segments, module::is_legal_segment};
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

struct Case {
    name: String,
    chapter: u8,
    rule: u16,
    expect: String,
    detail: String,
}

fn parse_directives(src: &str) -> Case {
    let (mut name, mut chapter, mut rule, mut expect, mut detail) =
        (String::new(), 0u8, 0u16, String::new(), String::new());
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            break;
        };
        let rest = rest.trim();
        if let Some(v) = rest.strip_prefix("name:") {
            name = v.trim().to_string();
        } else if let Some(v) = rest.strip_prefix("rule:") {
            if let Some((ch, r)) = v.trim().split_once('.')
                && let Some(k) = r.strip_prefix('R').or_else(|| r.strip_prefix('S'))
            {
                let k = &k[..k.find(|c: char| !c.is_ascii_digit()).unwrap_or(k.len())];
                if let (Ok(c), Ok(n)) = (ch.parse::<u8>(), k.parse::<u16>()) {
                    chapter = c;
                    rule = n;
                }
            }
        } else if let Some(v) = rest.strip_prefix("expect:") {
            expect = v.split("--").next().unwrap_or(v).trim().to_string();
        } else if let Some(v) = rest.strip_prefix("detail:") {
            detail = v.trim().to_string();
        }
    }
    Case {
        name,
        chapter,
        rule,
        expect,
        detail,
    }
}

/// The code a `check-error` test's `detail` names, as `("T", 26)`.
fn expected_code(detail: &str) -> Option<(char, u16)> {
    let b = detail.as_bytes();
    if b.len() < 5 {
        return None;
    }
    let c = b[0] as char;
    if !matches!(c, 'T' | 'N' | 'A' | 'O' | 'F' | 'D') {
        return None;
    }
    let n: u16 = detail.get(1..5)?.parse().ok()?;
    Some((c, n))
}

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

/// Resolves and checks one corpus target, returning every diagnostic the
/// checker produced (the resolver's are asserted by `fors-resolve`'s own
/// harness and are not this one's business).
fn check_target(path: &Path) -> (Vec<String>, Vec<String>) {
    let (a, b, _) = check_target_full(path);
    (a, b)
}

/// [`check_target`] plus the whole `CheckOutput`, for the tests that read
/// the store and the CHECK-position trace rather than the diagnostics.
fn check_target_full(path: &Path) -> (Vec<String>, Vec<String>, fors_check::CheckOutput) {
    check_target_in(path, !is_std_package(path))
}

/// The `std/` source root itself: the one target that is checked WITHOUT a
/// second copy of `std` beside it. Every other target is built with package
/// `std` in the build (item 47(a): ch08 R17's prelude names always denote
/// std's items, so `std` is never absent from a program's build).
fn is_std_package(path: &Path) -> bool {
    path.is_dir() && path.file_name().is_some_and(|n| n == "std")
}

/// Every `std/*.fors` module under the name ch08 R17's synthetic table gives
/// it (`std.mem`, `std.mem.alloc`, ...) — the same 15 files, in the same
/// order, as `fors-lower`'s `std_checks_clean` and `silent.rs`'s sweep, so
/// the build has package `std` in it and ch10 R2's prelude names bind to
/// std's real declarations (I10c).
fn std_module_sources() -> Vec<(Vec<&'static str>, Vec<u8>)> {
    let root = repo_root().join("std");
    let files: &[(&str, &[&'static str])] = &[
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
            (segs.to_vec(), src)
        })
        .collect()
}

/// [`check_target_full`], optionally with every `std` module in the build
/// after the target's own files. Only the TARGET's diagnostics are
/// returned: `std`'s own are `no_new_diagnostics_outside_ch09`'s business.
fn check_target_in(
    path: &Path,
    with_std: bool,
) -> (Vec<String>, Vec<String>, fors_check::CheckOutput) {
    if std::env::var("FORS_TRACE").is_ok() {
        eprintln!("== {}", path.display());
    }
    let mut interner = Interner::new();
    let mut names: Vec<Segments> = Vec::new();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    let mut root = None;

    if path.is_dir() {
        fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
            let Ok(entries) = fs::read_dir(dir) else {
                return;
            };
            let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
            entries.sort();
            for p in entries {
                if p.is_dir() {
                    walk(&p, out);
                } else if p.extension().is_some_and(|e| e == "fors") {
                    out.push(p);
                }
            }
        }
        let mut paths = Vec::new();
        walk(path, &mut paths);
        for p in &paths {
            let src = fs::read(p).unwrap();
            let rel = p.strip_prefix(path).unwrap_or(p);
            let comps: Vec<_> = rel.components().collect();
            let mut segs = Vec::new();
            for (i, c) in comps.iter().enumerate() {
                let os = c.as_os_str().to_string_lossy();
                let seg = if i + 1 == comps.len() {
                    os.strip_suffix(".fors").unwrap_or(&os).to_string()
                } else {
                    os.to_string()
                };
                segs.push(interner.intern(seg.as_bytes()));
            }
            if comps.len() == 1 && rel.file_stem().is_some_and(|s| s == "main") {
                root = Some(sources.len());
            }
            names.push(segs);
            sources.push(src);
        }
    } else {
        let src = fs::read(path).unwrap();
        let name = header_name(&src, &mut interner).unwrap_or_else(|| {
            let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
            let stem = if is_legal_segment(stem.as_bytes()) {
                stem
            } else {
                "m".to_string()
            };
            vec![interner.intern(stem.as_bytes())]
        });
        names.push(name);
        sources.push(src);
        root = Some(0);
    }

    let own = sources.len();
    if with_std {
        for (segs, s) in std_module_sources() {
            names.push(segs.iter().map(|b| interner.intern(b.as_bytes())).collect());
            sources.push(s);
        }
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
    let package = path.file_name().map(|n| n.as_encoded_bytes().to_vec());
    let resolved =
        fors_resolve::resolve_in_package(&mut interner, &inputs, root, package.as_deref());
    let resolver: Vec<String> = resolved
        .files
        .iter()
        .take(own)
        .flat_map(|f| f.diagnostics.iter())
        .map(|d| d.code.as_string())
        .collect();
    let mut out = fors_check::check_build(&inputs, &resolved, &mut interner);
    // The TARGET's diagnostics only, for every consumer of the output: std's
    // own are `no_new_diagnostics_outside_ch09`'s business (item 47(a)).
    out.diagnostics.retain(|d| d.file.index() < own);
    if let Some(defs) = out.defs.as_ref() {
        out.facts
            .retain(|(def, _)| defs.get(*def).is_some_and(|r| r.file.index() < own));
    }
    let checker: Vec<String> = out.diagnostics.iter().map(|d| d.code.as_string()).collect();
    (checker, resolver, out)
}

fn corpus_targets(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(dir) else {
        return out;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() || p.extension().is_some_and(|e| e == "fors") {
            out.push(p);
        }
    }
    out
}

fn directive_source(target: &Path) -> String {
    if target.is_dir() {
        fs::read_to_string(target.join("main.fors")).unwrap_or_default()
    } else {
        fs::read_to_string(target).unwrap_or_default()
    }
}

include!("data/pending_09.rs");
include!("data/pending_05.rs");
include!("data/pending_02.rs");
include!("data/pending_03.rs");
include!("data/pending_04.rs");

#[test]
fn ch09_types_corpus_checker_view() {
    let dir = repo_root().join("tests/conformance/09-types");
    let targets = corpus_targets(&dir);
    assert!(
        targets.len() >= 150,
        "09-types corpus not found or truncated: {}",
        targets.len()
    );
    let mut failures = Vec::new();
    let mut on = 0usize;
    let mut pending = 0usize;
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        assert_eq!(
            case.chapter, 9,
            "{}: every 09-types test cites 09.Rk",
            case.name
        );
        let key = case.name.replace('_', "-");
        if PENDING_09.iter().any(|&(n, _)| n == key) {
            pending += 1;
            // A pending test must still be SILENT: an increment that has not
            // reached a rule must not guess at it. The one exception is a
            // file whose OTHER declarations break a rule the checker has
            // reached, listed with its reason in `PENDING_SPEAKS`; there the
            // obligation is that the test's OWN code is still unreported.
            let (got, _, _) = check_target_full(target);
            let want = expected_code(&case.detail).map(|(c, n)| format!("{c}{n:04}"));
            match PENDING_SPEAKS.iter().find(|&&(n, _)| n == key) {
                Some(_) => {
                    if got.is_empty() {
                        failures.push(format!(
                            "{key}: listed in PENDING_SPEAKS, but the checker is silent on it now"
                        ));
                    } else if let Some(w) = want
                        && got.contains(&w)
                    {
                        failures.push(format!(
                            "{key}: PENDING, but the checker already reports its own code {w}: {got:?}"
                        ));
                    }
                }
                None => {
                    if !got.is_empty() {
                        failures.push(format!("{key}: PENDING, but the checker spoke: {got:?}"));
                    }
                }
            }
            continue;
        }
        on += 1;
        let (got, _, _) = check_target_full(target);
        match case.expect.as_str() {
            "check-ok" => {
                if !got.is_empty() {
                    failures.push(format!("{key}: expected check-ok, got {got:?}"));
                }
            }
            "check-error" => {
                let want = expected_code(&case.detail).map(|(c, n)| format!("{c}{n:04}"));
                // A ch09 test whose code is another PHASE's (`N0026`,
                // `N0027`: ch08 R26/R27 decide them and say so) is that
                // phase's to report; the checker's obligation is silence.
                if matches!(expected_code(&case.detail), Some(('N', _)) | Some(('A', _))) {
                    let w = want.unwrap();
                    let (_, res, _) = check_target_full(target);
                    if !got.is_empty() || res.len() != 1 || res[0] != w {
                        failures.push(format!("{key}: expected the resolver alone to say {w}; resolver {res:?}, checker {got:?}"));
                    }
                    continue;
                }
                match want {
                    Some(w) => {
                        if got.len() != 1 || got[0] != w {
                            failures.push(format!(
                                "{key} (09.R{}): expected exactly one {w}, got {got:?}",
                                case.rule
                            ));
                        }
                    }
                    None => {
                        if got.len() != 1 {
                            failures.push(format!(
                                "{key}: expected exactly one diagnostic, got {got:?}"
                            ));
                        }
                    }
                }
            }
            other => failures.push(format!("{key}: unexpected expectation {other:?}")),
        }
    }
    eprintln!(
        "ch09 checker view: {on} on, {pending} pending, {} total, every one checked with std",
        targets.len()
    );
    assert!(
        failures.is_empty(),
        "ch09 corpus (checker view) failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The ch05 (`05-ir`) corpus, checker view (owner Q5). `fors-cli check`
/// never runs `fors-lower`/`fors-fmir::verify` (see `data/pending_05.rs`'s
/// header), so every one of these 22 files must be SILENT under it today:
/// the six `check-error` tests because [`PENDING_05`] says so (their rule is
/// real and FMIR-enforced, cited there; `fors check` just cannot see it
/// yet), and the sixteen `parse-ok` tests because they are IR-only or
/// lowering-reachable placeholders that assert nothing is checker-visible
/// at all. A `check-ok`/`run-ok` ch05 test would be a corpus mistake: ch05
/// names no such tests.
#[test]
fn ch05_ir_corpus_checker_view() {
    let dir = repo_root().join("tests/conformance/05-ir");
    let targets = corpus_targets(&dir);
    assert_eq!(
        targets.len(),
        22,
        "05-ir corpus not found or changed size: {} (ch05 names exactly 22 conformance tests)",
        targets.len()
    );
    let mut failures = Vec::new();
    let mut on = 0usize;
    let mut pending = 0usize;
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        assert_eq!(
            case.chapter, 5,
            "{}: every 05-ir test cites 05.Rk",
            case.name
        );
        let key = case.name.replace('_', "-");
        if PENDING_05.iter().any(|&(n, _)| n == key) {
            pending += 1;
            assert_eq!(
                case.expect, "check-error",
                "{key}: PENDING_05 lists a test whose own file does not expect check-error"
            );
            let (got, _) = check_target(target);
            if !got.is_empty() {
                failures.push(format!("{key}: PENDING, but the checker spoke: {got:?}"));
            }
            continue;
        }
        on += 1;
        if case.expect != "parse-ok" {
            failures.push(format!(
                "{key}: expected parse-ok for a non-pending 05-ir test, got {:?}",
                case.expect
            ));
            continue;
        }
        let (got, _) = check_target(target);
        if !got.is_empty() {
            failures.push(format!("{key}: expected silence, got {got:?}"));
        }
    }
    eprintln!(
        "ch05 checker view: {on} on (IR-only/lowering-reachable), {pending} pending, {} total",
        targets.len()
    );
    assert!(
        failures.is_empty(),
        "05-ir corpus (checker view) failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn pending_05_is_shrinking() {
    assert!(
        PENDING_05.len() <= PENDING_05_MAX,
        "PENDING_05 grew to {} (bound {PENDING_05_MAX}); an increment must lower it, never raise it",
        PENDING_05.len()
    );
    let dir = repo_root().join("tests/conformance/05-ir");
    let names: Vec<String> = corpus_targets(&dir)
        .iter()
        .map(|t| {
            parse_directives(&directive_source(t))
                .name
                .replace('_', "-")
        })
        .collect();
    for (n, _) in PENDING_05 {
        assert!(
            names.iter().any(|x| x == n),
            "PENDING_05 names a test that is not in the corpus: {n}"
        );
    }
}

// ------------------------------------------------- increment I10's gate

/// A `check-error` test of chapter 2 or 3 whose code is NOT its own
/// chapter's `F00nn`/`D00nn`, because another chapter's corpus asserts a
/// different code for the very same fault: `(test, code, why)`.
const CH02_CODED_ELSEWHERE: &[(&str, &str, &str)] = &[(
    "handler-block-mismatched-type-rejected",
    "T0026",
    "`09-types/handler-block-type-rejected` is the same program (a handler block yielding `true` \
     for an `i64` call) and its detail line names T0026 (ch09 R36: the block is checked against \
     the success type, R26's mismatch); this file names only `02.R5`. The message cites ch02 R5. \
     One code per fault is the owner's call (the I10 report flags it)",
)];
const CH03_CODED_ELSEWHERE: &[(&str, &str, &str)] = &[];

/// Diagnostics a ch02/ch03 file draws BESIDE its own (or, for an accepted
/// file, at all), each because the file itself breaks another chapter's
/// rule the checker already enforces: `(test, code, count, why)`. A row
/// whose code stops appearing fails the view, so none can go stale.
const CH02_ALSO_SPEAKS: &[(&str, &str, usize, &str)] = &[
    (
        "error-from-single-hop-two-hops-rejected",
        "O0003",
        2,
        "ch01 R3: both `fn from(let e: ..) { return X.wrapped(e); }` move the `let` parameter `e` \
         into a payload, and neither error enum is `Copyable`",
    ),
    (
        "error-from-single-hop",
        "O0003",
        1,
        "ch01 R3: `fn from(let e: NetError) -> AppError { return AppError.wrapped(e); }` moves the \
         `let` parameter `e`; `NetError` is not `Copyable`",
    ),
    (
        "trap-bounds",
        "T0011",
        1,
        "item 47(a) (`std` is in every build): the program writes `Buffer[i64]` and `Buffer.fixed(4)`, \
         and `std`'s `Buffer` is `Buffer[T, N: usize]` with `empty`/`filled` (ch10 S0023), so ch09 \
         reports T0011 (one type argument supplied, two declared). ch10 S0002's own table cites \
         `Buffer[i64]` for the prelude; the corpus and S0023 disagree",
    ),
    (
        "main-raises-std-error-run-error",
        "T0011",
        1,
        "item 47(a): the `with allocator` header writes `mem.Counting[mem.Fixed[8]]`, and `std`'s \
         `Counting` is `Counting[N: usize, A: brand]` (ch10 S0021, standalone by ch01 R15a), so ch09 \
         reports T0011 (a type where a constant argument is expected) at that type; with it \
         spelled `mem.Counting[8]` the file checks clean (see fors-lower's \
         `gate_main_raises_std_error_run_error`)",
    ),
];
const CH03_ALSO_SPEAKS: &[(&str, &str, usize, &str)] = &[
    (
        "generics-specialize-enforced-in-simd",
        "T0057",
        1,
        "ch09 R57: `fn add[T](let a: T, let b: T) -> T { return a + b; }` declares no `Add` bound",
    ),
    (
        "generics-specialize-applied-accepted",
        "T0057",
        1,
        "ch09 R57: the same unbounded `add[T]` as its rejected twin",
    ),
    (
        "generics-specialize-applied-accepted",
        "T0026",
        1,
        "ch09 R29/R47: `v[i]` indexes with the `i32` the range `0 ..< 8` synthesises, and an index \
         is a `usize` (the rejected twin's per-declaration budget is spent on D0018 first)",
    ),
    (
        "svec-accepted-as-simd-local",
        "T0030",
        1,
        "ch09 R30: `v as SVec[f64]` — `as` converts between numeric primitives only, and no rule \
         converts a `vector` into an `SVec`; the `SVec[f64]` local itself is accepted (ch03 R20)",
    ),
    (
        "array-lit-generic-argument-synthesised",
        "O0004",
        1,
        "ch01 R4a(c): `return a[0];` moves an element out of `Array[T, N]` for an unbounded `T`",
    ),
];

/// The ch02/ch03 checker view (design §13's I10 GATE). A `check-error`
/// test reports exactly its code — its chapter's letter and its rule's
/// number, unless [`CH02_CODED_ELSEWHERE`]/[`CH03_CODED_ELSEWHERE`] says
/// otherwise — at its site, beside nothing but its listed `ALSO_SPEAKS`
/// rows; every `check-ok`, `run-ok`, `run-error`, `trap` and `parse-ok`
/// test is silent save for those rows (a program that must run, or that
/// the corpus calls accepted, type-checks); a `parse-error` test is the
/// parser's.
///
/// `resolver_letter`: chapter 4's rules are split between the phases —
/// `fors_resolve::authority` decides what names alone decide (A0001, A0008)
/// and the checker the rest — so its view reads the resolver's diagnostics
/// of the chapter's OWN letter too (never another chapter's: a resolver
/// N-code is ch08's harness's business).
struct View<'t> {
    dir: &'t str,
    chapter: u8,
    letter: char,
    resolver_letter: Option<char>,
    count: usize,
    pending: &'t [(&'t str, &'t str)],
    coded: &'t [(&'t str, &'t str, &'t str)],
    also: &'t [(&'t str, &'t str, usize, &'t str)],
}

fn chapter_checker_view(v: View<'_>) {
    let View {
        dir,
        chapter,
        letter,
        resolver_letter,
        count,
        pending,
        coded,
        also,
    } = v;
    let targets = corpus_targets(&repo_root().join("tests/conformance").join(dir));
    assert_eq!(
        targets.len(),
        count,
        "{dir} corpus not found or changed size: {}",
        targets.len()
    );
    let mut failures = Vec::new();
    let (mut on, mut pend) = (0usize, 0usize);
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        // `02.Definitions` (the trap kinds) cites the chapter, not a rule.
        assert!(
            case.chapter == chapter || src.contains(&format!("//! rule: {chapter:02}.Definitions")),
            "{}: every {dir} test cites {chapter:02}.Rk",
            case.name
        );
        let key = case.name.replace('_', "-");
        if case.expect == "parse-error" {
            continue;
        }
        let (chk, res) = check_target(target);
        let mut got = chk.clone();
        if let Some(l) = resolver_letter {
            got.extend(res.iter().filter(|c| c.starts_with(l)).cloned());
        }
        let mut rest = got.clone();
        for &(n, code, k, _) in also.iter().filter(|r| r.0 == key) {
            for _ in 0..k {
                match rest.iter().position(|c| c == code) {
                    Some(i) => {
                        rest.remove(i);
                    }
                    None => failures.push(format!(
                        "{n}: ALSO_SPEAKS lists {k} x {code}, but the checker said {got:?}"
                    )),
                }
            }
        }
        if pending.iter().any(|&(n, _)| n == key) {
            pend += 1;
            if !rest.is_empty() {
                failures.push(format!("{key}: PENDING, but the checker spoke: {got:?}"));
            }
            continue;
        }
        on += 1;
        match case.expect.as_str() {
            "check-error" => {
                let want = coded
                    .iter()
                    .find(|r| r.0 == key)
                    .map(|r| r.1.to_string())
                    .or_else(|| expected_code(&case.detail).map(|(c, n)| format!("{c}{n:04}")))
                    .unwrap_or_else(|| format!("{letter}{:04}", case.rule));
                if rest != [want.clone()] {
                    failures.push(format!(
                        "{key} ({chapter:02}.R{}): expected exactly {want}, got {got:?}",
                        case.rule
                    ));
                }
                // The code's rule has its `rules.rs` row, implemented —
                // when it is the CHECKER's code (the resolver's ch04 codes
                // are traced in `fors_resolve::authority`).
                if want.starts_with(letter) && chk.contains(&want) {
                    let table: &[fors_check::rules::RuleEntry] = match letter {
                        'F' => &fors_check::rules::CH02_RULES,
                        'D' => &fors_check::rules::CH03_RULES,
                        _ => &fors_check::rules::CH04_RULES,
                    };
                    let n: u16 = want[1..].parse().unwrap_or(0);
                    if !table.iter().any(|e| {
                        e.code == Some(n) && e.status == fors_check::rules::RuleStatus::Implemented
                    }) {
                        failures.push(format!("{key}: {want} has no implemented row in rules.rs"));
                    }
                }
            }
            "check-ok" | "run-ok" | "run-error" | "trap" | "parse-ok" => {
                if !rest.is_empty() {
                    failures.push(format!(
                        "{key}: a {} test must type-check, got {got:?}",
                        case.expect
                    ));
                }
            }
            other => failures.push(format!("{key}: unexpected expectation {other:?}")),
        }
    }
    eprintln!(
        "{dir} checker view: {on} on, {pend} pending, {} total",
        targets.len()
    );
    assert!(
        failures.is_empty(),
        "{dir} corpus (checker view) failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// ch02 (`02-failure`, 36 files), checker view: every `check-error` test
/// reports `F00nn` (design §14 Q1) — or the code [`CH02_CODED_ELSEWHERE`]
/// names — and every program that must run type-checks.
#[test]
fn ch02_failure_corpus_checker_view() {
    chapter_checker_view(View {
        dir: "02-failure",
        chapter: 2,
        letter: 'F',
        resolver_letter: None,
        count: 36,
        pending: PENDING_02,
        coded: CH02_CODED_ELSEWHERE,
        also: CH02_ALSO_SPEAKS,
    });
}

/// ch03 (`03-numerics`, 46 files), checker view: every `check-error` test
/// reports `D00nn`, and every program that must run type-checks.
#[test]
fn ch03_numerics_corpus_checker_view() {
    chapter_checker_view(View {
        dir: "03-numerics",
        chapter: 3,
        letter: 'D',
        resolver_letter: None,
        count: 46,
        pending: PENDING_03,
        coded: CH03_CODED_ELSEWHERE,
        also: CH03_ALSO_SPEAKS,
    });
}

/// A `check-error` test of chapter 4 whose code is not `A00` + its cited
/// rule: `(test, code, why)`.
const CH04_CODED_ELSEWHERE: &[(&str, &str, &str)] = &[(
    "main-root-capability-missing-from-needs-rejected",
    "A0001",
    "ch04 R8 itself sends this case to R1 — the capability of a `main` parameter's type \
     \"MUST be declared in the root module's `needs { ... }` (Rule 1)\" — so the resolver \
     reports it under R1's code: one cause, one code (`fors_resolve::authority::check_main_impl`)",
)];

/// Diagnostics a ch04 file draws beside its own: `(test, code, count, why)`.
const CH04_ALSO_SPEAKS: &[(&str, &str, usize, &str)] = &[
    (
        "main-generic-rejected",
        "A0008",
        1,
        "ch04 R8 bars a type-parameter-typed `main` parameter too (\"not ... a type parameter\"): \
         `inout out: W` is the second, independent fault, which the resolver reports beside \
         `main[W: io.Writer]` being generic",
    ),
    (
        "comptime-declared-file-read-accepted",
        "A0013",
        1,
        "the file declares its read with `@comptime_input(\".config\")`, an attribute no chapter \
         defines; ch04 R13 and ch10 R42 name the header's `inputs { \".config\" };` clause, which \
         this file does not write, so the read IS undeclared. The file is `parse-ok`, which says \
         nothing about the checker; its owner should write the `inputs` clause",
    ),
];

/// ch04 (`04-authority`, 34 targets), the build's view: every `check-error`
/// test reports `A00nn` — from the checker, or for R1/R8 from the
/// resolver — or the code [`CH04_CODED_ELSEWHERE`] names, and every program
/// that must run is silent. [`PENDING_04`] holds what needs a manifest, an
/// evaluator or a corpus fix.
#[test]
fn ch04_authority_corpus_checker_view() {
    chapter_checker_view(View {
        dir: "04-authority",
        chapter: 4,
        letter: 'A',
        resolver_letter: Some('A'),
        count: 34,
        pending: PENDING_04,
        coded: CH04_CODED_ELSEWHERE,
        also: CH04_ALSO_SPEAKS,
    });
}

#[test]
fn pending_04_is_shrinking() {
    pending_is_shrinking("04-authority", PENDING_04, PENDING_04_MAX, "PENDING_04");
}

fn pending_is_shrinking(dir: &str, pending: &[(&str, &str)], max: usize, table: &str) {
    assert!(
        pending.len() <= max,
        "{table} grew to {} (bound {max}); an increment must lower it, never raise it",
        pending.len()
    );
    let names: Vec<String> = corpus_targets(&repo_root().join("tests/conformance").join(dir))
        .iter()
        .map(|t| {
            parse_directives(&directive_source(t))
                .name
                .replace('_', "-")
        })
        .collect();
    for (n, _) in pending {
        assert!(
            names.iter().any(|x| x == n),
            "{table} names a test that is not in the corpus: {n}"
        );
    }
}

#[test]
fn pending_02_is_shrinking() {
    pending_is_shrinking("02-failure", PENDING_02, PENDING_02_MAX, "PENDING_02");
}

#[test]
fn pending_03_is_shrinking() {
    pending_is_shrinking("03-numerics", PENDING_03, PENDING_03_MAX, "PENDING_03");
}

/// D10 for FMIR F3: every `?`, handler and `raise` of the ch02 corpus's
/// accepted programs is published, with the propagation edge decided.
#[test]
fn d10_failure_facts_are_published_for_fmir_f3() {
    use fors_check::facts::Propagation;
    let all = |name: &str| {
        let (checker, _, out) = check_target_full(&target_named("02-failure", name));
        (checker, out)
    };
    // `?` with equal error types: `Propagation::Same`, E and F recorded.
    let (c, out) = all("postfix-try-propagate");
    assert!(c.is_empty(), "accepted: {c:?}");
    let tries: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.failure.tries.iter().copied())
        .collect();
    assert!(!tries.is_empty(), "D10: the `?` is published");
    assert!(
        tries
            .iter()
            .all(|t| t.edge == Propagation::Same && t.callee_raises == t.target)
    );
    // `?` across one `ErrorFrom` hop: the impl and its `from` are named.
    let (_, out) = all("error-from-single-hop");
    let hop: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.failure.tries.iter().copied())
        .collect();
    assert!(
        hop.iter()
            .any(|t| matches!(t.edge, Propagation::ErrorFrom { .. }) && t.callee_raises != t.target),
        "D10: the ErrorFrom edge is decided once, here: {hop:?}"
    );
    // A handler: its binding is the callee's `raises` type, its block yields
    // the success type.
    let (c, out) = all("handler-block-value-accepted");
    assert!(c.is_empty(), "accepted: {c:?}");
    let hs: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.failure.handlers.iter().copied())
        .collect();
    assert_eq!(hs.len(), 1, "D10: one handler: {hs:?}");
    assert!(!hs[0].diverges && hs[0].binding != hs[0].success);
    // A `raise` of a named unit variant records the variant.
    let (c, out) = all("raise-in-raises-fn-accepted");
    assert!(c.is_empty(), "accepted: {c:?}");
    let rs: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.failure.raises.iter().copied())
        .collect();
    assert!(
        !rs.is_empty() && rs.iter().all(|r| r.variant.is_some()),
        "D10: `raise Err.empty;` names its variant: {rs:?}"
    );
}

/// D11: ch03 R4/R6's methods resolve to their prelude declarations, typed,
/// and `reduce` carries its element type.
#[test]
fn d11_numeric_facts_are_published() {
    use fors_check::facts::{ArithOp, NumericMethod};
    let rows = |name: &str| {
        let (checker, _, out) = check_target_full(&target_named("03-numerics", name));
        assert!(checker.is_empty(), "{name} is accepted: {checker:?}");
        out
    };
    let out = rows("sat-add-saturates");
    let calls: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.numeric.calls.iter().copied())
        .collect();
    assert_eq!(calls.len(), 1, "{calls:?}");
    assert_eq!(calls[0].kind, NumericMethod::Sat(ArithOp::Add));
    assert_eq!(
        calls[0].recv, calls[0].result,
        "Rule 4 keeps the receiver's type"
    );
    let out = rows("wrap-as-truncates");
    let conv: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.numeric.calls.iter().copied())
        .collect();
    assert_eq!(conv.len(), 1, "{conv:?}");
    assert_eq!(conv[0].kind, NumericMethod::WrapAs);
    assert_ne!(conv[0].recv, conv[0].result, "Rule 6 converts to `U`");
    let out = rows("reduce-empty-with-identity");
    let red: Vec<_> = out
        .facts
        .iter()
        .flat_map(|(_, f)| f.numeric.reduces.iter().copied())
        .collect();
    assert_eq!(red.len(), 1, "{red:?}");
    assert!(red[0].identity.is_some());
}

/// A non-ch09 `check-ok` test that ch09 rejects anyway. Each of these is a
/// corpus conflict, not a checker bug: the test is accepted by ITS OWN
/// chapter's rules and violates a ch09 rule the same corpus asserts
/// elsewhere. They are listed, with the clause, rather than silenced.
const CROSS_CHAPTER: &[(&str, &str)] = &[
    (
        "same_method_in_two_impls_accepted",
        "ch08 R27 is per block, so ch08 accepts it; ch09 R48 rejects `fn get` beside the field `get` AND the second          inherent `get` outright (`method-named-as-field-rejected`, `duplicate-method-across-impls-rejected` assert          exactly this)",
    ),
    (
        "projection_second_segment_deferred_accepted",
        "ch08 R16/R22 defer `I.Item` to the checker, which is all this test asserts; ch09 R61(c) then rejects it          because the unbounded `I` has no bound declaring `Item` (`projection-unknown-assoc-type-rejected`)",
    ),
    (
        "closure_param_named_self_in_free_fn_accepted",
        "ch08 R18 is about the NAME `self`, which ch09 agrees is ordinary here; the closure is nonetheless in SYNTH          position (`let g = |self| self;`), where ch09 R35 requires every cparam to carry a type          (`closure-synth-unannotated-rejected` asserts exactly this clause)",
    ),
    (
        "closure_param_shadows_prelude_accepted",
        "same clause as the row above: ch08 asserts the shadowing, ch09 R35 rejects the un-annotated cparam of a          SYNTH-mode closure",
    ),
    (
        "sibling_scopes_reuse_accepted",
        "ch08 R18 asserts the two `match` statements may reuse `k`; ch09 R31 checks a statement-form `match` that is          not the block's tail against `()`, and this one's arms are `i32` (`defer-body-with-value-rejected` asserts the          same clause for a deferred block)",
    ),
    (
        "body_mention_of_std_module_adds_no_edge_accepted",
        "ch08 R7 asserts only that `io.len` on a LOCAL named `io` adds no module edge; `io: Str` and std's `len` is a          METHOD of `Str` (`impl Str { pub fn len(let self) }`), so ch09 R42 rejects the un-called `.len` (there are no          method values; only `Slice`/`Array`/`vector` have a built-in `len` field) — added by the I2/I3 verification,          which closed R42's silence on primitive receivers",
    ),
    (
        "checker_questions_not_diagnosed_accepted",
        "the test's whole point is that ch08 leaves these to the checker; `-> K` names a `const` in type position,          which ch09 R11 rejects (`local-shadowing-prelude-type-as-type-head-rejected` is the same clause)",
    ),
    (
        "with_arena_brand_type_accepted",
        "ch08 R19 asserts only that the `with arena` binding `a` is one binding, usable as a value and in type          position; the body then writes `discard v;` on a `v: Own[i32, a]`, and `Own` is linear by language rule, so          ch01 R22d rejects the `discard` (`linear-discard-rejected` asserts exactly this clause)",
    ),
    (
        "with_brand_in_closure_type_accepted",
        "same clause as the row above: ch08 asserts the brand's visibility in a nested block, a closure and a          sibling `with`, and all three bodies `discard` an `Own`, which ch01 R22d rejects",
    ),
    (
        "scoped_parameter_accepted",
        "ch08 R19/R20 asserts only that `scoped(x)` names the parameter `x`; the body writes `Own.alloc(x, 1)`, and `std`'s `impl Own` (ch10 S0022; `std.mem` is `Own`'s defining module, S0002) declares no `alloc`, so ch09 T0043 reports the missing associated function once `std` is in the build (item 47(a))",
    ),
    (
        "use_std_item_path_accepted",
        "ch08 R3/R12 asserts only that `use std.io.Writer;` binds the item `Writer`; the body writes `let w: Writer` in type position, and `Writer` is a TRAIT, which ch09 R11 allows as a type only after `dyn`, in a bound or in an `impl` header (T0011) — visible only once `std.io` is in the build (item 47(a))",
    ),
    (
        "use_std_mem_accepted",
        "same clause as the row above: ch08 asserts the `use std.mem;` binding, and the body writes `mem.Allocator` in type position, a trait, which ch09 R11 rejects (T0011) with `std` in the build (item 47(a))",
    ),
    (
        "use_std_module_accepted",
        "ch08 R3 asserts only that `use std.io;` binds the module; the body writes `out.write_line(\"x\")?`, and `std`'s `Stdout.write_line` is total and latching (ch10 Rule 39) and declares no `raises`, so ch02 R2's F0002 (`?` on a call that does not raise) is reported once `std.io` is in the build (item 47(a))",
    ),
    (
        "pattern_variant_through_alias_accepted",
        "ch08 R25 asserts only that the two-segment path through the alias reaches the variant as a reference; its          `Color` has exactly two variants (`Red`, `Rgb`), both matched, so ch09 R53/R54 (I7) find the trailing          `let other` arm unreachable — the SAME clause `unreachable-arm-rejected` asserts for a non-aliased enum",
    ),
];

/// A `std` declaration ch09 rejects: each entry is a declaration `std`
/// itself marks `// STUB`. The three known R48 conflicts (`Block.align`,
/// `Addr.v6`, `Addr.port`) were fixed by renaming, so no entry here is a
/// rule dispute. An entry whose call resolves, or whose move stops being a
/// partial one, must be deleted here, not left to excuse a regression (the
/// count assertion below enforces it).
///
/// F7 emptied the list. The three undeclared-method stubs (`BufferIter::
/// next`'s `take_at`, `SliceIter::next`'s `load`, `Scalars::next`'s
/// `decode`) are now declared, real SIGNATURES with a self-referencing
/// stand-in body (the shape of `std.mem.alloc.own_raw`/`disown_raw`): the
/// two readers need a `rawptr` READ primitive no increment has added yet
/// (ch09 R57), and `take_at`'s only surface-language body, `move
/// self.data[i]`, is the partial move ch01 R4a(c) forbids — I8's flow pass
/// reported it as O0004 the moment `std` was checked under it. I8's one row
/// (`Buffer::into_iter`, the same O0004 for `move self.data`) is gone too:
/// `std` now writes the destructuring form R22d(ii) prescribes.
///
/// I8b (ch01 R22 linear obligations) emptied the list again and then added
/// back exactly two PERMANENT rows. `Option::unwrap_or`'s conflict (the
/// `some` arm's `discard fallback;` with a bare rigid `T`) was a signature
/// gap, not a stub body, and is fixed in `std/mem.fors`: the method moved
/// into its own `impl[T: Droppable] Option[T]` block, amending ch10 S0027's
/// declaration, so it no longer appears here. `Vec::push` and `Map::insert`
/// stay: their declared signatures (ch10 S0024/S0025, `sink v: T`/`sink
/// k: K, sink v: V ... raises AllocError`, no `Droppable` bound) drop the
/// sunk value on the allocation-failure exit, which ch01 R22c forbids for a
/// rigid type — and that is true of the REAL body (reserve, then store) as
/// much as of the `// STUB` raise, because the failure exit exists either
/// way. This is an owner decision (hand the value back in the error, add a
/// `Droppable` bound, or a reserve-first total push/insert), not something
/// a body rewrite can fix, so these two rows are expected to stay until the
/// owner picks one; a row here must still be deleted the moment its call
/// resolves or its signature changes, never left to excuse a regression.
const STD_CONFLICTS: &[(&str, &str)] = &[
    (
        "Map::insert",
        "std/mem/hashmap.fors: the body is `raise alloc.AllocError.out_of_memory; // STUB`, which drops the `sink k: K` and `sink v: V` parameters on the error exit; ch01 R22c reports T0057 on the first until the real body stores them",
    ),
    (
        "Vec::push",
        "std/mem/vec.fors: the body is `raise alloc.AllocError.out_of_memory; // STUB`, which drops the `sink v: T` parameter on the error exit; ch01 R22c reports T0057 until the real body stores it",
    ),
];

/// The no-regression assertion the I2 gate names: outside the tests this
/// increment turned on, the checker stays silent on every program another
/// chapter's corpus calls WELL-TYPED (`check-ok`/`run-ok`), except for the
/// listed cross-chapter conflicts. On a `check-error` test of another chapter
/// the checker MAY speak — the program is ill-formed by that chapter's own
/// statement, and a ch09 rule finding its own fault in it is not a
/// regression — but it must not panic and must not exceed one diagnostic per
/// declaration.
#[test]
fn no_new_diagnostics_outside_ch09() {
    let root = repo_root();
    let mut dirs: Vec<PathBuf> = vec![
        root.join("tests/conformance/01-ownership"),
        root.join("tests/conformance/02-failure"),
        root.join("tests/conformance/03-numerics"),
        root.join("tests/conformance/04-authority"),
        root.join("tests/conformance/05-ir"),
        root.join("tests/conformance/07-grammar"),
        root.join("tests/conformance/08-names"),
        root.join("tests/conformance/10-std"),
    ];
    if root.join("std").is_dir() {
        dirs.push(root.join("std"));
    }
    let mut failures = Vec::new();
    for dir in dirs {
        if dir.file_name().is_some_and(|n| n == "std") {
            let (got, _) = check_target(&dir);
            // `std` is real source and must type-check, save for the listed
            // conflicts: one diagnostic per listed declaration.
            if got.len() != STD_CONFLICTS.len() {
                failures.push(format!(
                    "std/: expected only the {} listed conflicts, got {got:?}",
                    STD_CONFLICTS.len()
                ));
            }
            continue;
        }
        for target in corpus_targets(&dir) {
            let src = directive_source(&target);
            let case = parse_directives(&src);
            // Only a test the corpus itself says the CHECKER decides is this
            // assertion's business: a `parse-ok`/`parse-error` test is ch07's
            // and is under no obligation to be a well-typed program.
            if !matches!(case.expect.as_str(), "check-ok" | "run-ok") {
                continue;
            }
            if CROSS_CHAPTER.iter().any(|&(n, _)| n == case.name) {
                continue;
            }
            let (got, _) = check_target(&target);
            if !got.is_empty() {
                failures.push(format!(
                    "{}/{}: the checker spoke: {got:?}",
                    dir.file_name().unwrap().to_string_lossy(),
                    case.name
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "regressions outside ch09 ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every listed conflict is real: the test still exists and the checker still
/// speaks on it. A list entry that has become stale fails here rather than
/// quietly excusing a future regression.
#[test]
fn cross_chapter_conflicts_are_live() {
    let root = repo_root();
    for (name, why) in CROSS_CHAPTER {
        let mut found = false;
        for dir in [
            "01-ownership",
            "02-failure",
            "03-numerics",
            "04-authority",
            "07-grammar",
            "08-names",
            "10-std",
        ] {
            for target in corpus_targets(&root.join("tests/conformance").join(dir)) {
                if parse_directives(&directive_source(&target)).name != *name {
                    continue;
                }
                found = true;
                let (got, _) = check_target(&target);
                assert!(
                    !got.is_empty(),
                    "CROSS_CHAPTER lists {name} ({why}) but the checker is silent on it now"
                );
            }
        }
        assert!(
            found,
            "CROSS_CHAPTER names a test that is not in the corpus: {name}"
        );
    }
}

/// The [`CROSS_CHAPTER`] rows item 47(a) added (`std` in every build), each
/// pinned to the EXACT codes the checker reports on it, so the row cannot
/// quietly excuse a different diagnostic: [`cross_chapter_conflicts_are_live`]
/// only asks that the checker speak at all.
const CROSS_CHAPTER_STD_PINS: &[(&str, &str, &[&str])] = &[
    ("08-names", "scoped_parameter_accepted", &["T0043"]),
    ("08-names", "use_std_item_path_accepted", &["T0011"]),
    ("08-names", "use_std_mem_accepted", &["T0011"]),
    ("08-names", "use_std_module_accepted", &["F0002"]),
];

#[test]
fn cross_chapter_std_rows_report_exactly_their_pinned_codes() {
    let root = repo_root();
    let mut failures = Vec::new();
    for &(dir, name, want) in CROSS_CHAPTER_STD_PINS {
        assert!(
            CROSS_CHAPTER.iter().any(|&(n, _)| n == name),
            "{name} is pinned here but not listed in CROSS_CHAPTER"
        );
        let target = corpus_targets(&root.join("tests/conformance").join(dir))
            .into_iter()
            .find(|t| parse_directives(&directive_source(t)).name == name)
            .unwrap_or_else(|| panic!("{dir}/{name} is not in the corpus"));
        let (got, _) = check_target(&target);
        if got != want {
            failures.push(format!("{name}: pinned to {want:?}, got {got:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "item 47(a) CROSS_CHAPTER pins ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The ch09 rows I10c deleted from `PENDING_09` by checking them with `std`
/// in the build. Item 47(a) made that the only build there is, so these are
/// ordinary rows now; the list stays as the names whose reported code needs
/// `Iterator`'s provided methods from `std/mem/seq.fors`.
const CH09_ON_ONLY_WITH_STD: &[&str] = &[
    "adaptor-annotated-binding-mismatch-rejected",
    "adaptor-map-closure-returns-linear-rejected",
];

/// These two report exactly their own code, because `std` is always in the
/// build (`Iterator`'s provided `map`/`take` and `Mapped`/`Taken` exist only
/// in `std/mem/seq.fors`, so a build without it could not type their
/// bodies — and no such build exists, item 47(a)).
#[test]
fn ch09_std_mode_is_what_turns_them_on() {
    let dir = repo_root().join("tests/conformance/09-types");
    let mut failures = Vec::new();
    for &name in CH09_ON_ONLY_WITH_STD {
        let target = dir.join(format!("{name}.fors"));
        let case = parse_directives(&directive_source(&target));
        let want = expected_code(&case.detail).map(|(c, n)| format!("{c}{n:04}"));
        let (with, _, _) = check_target_full(&target);
        if want.is_none() || with.len() != 1 || Some(&with[0]) != want.as_ref() {
            failures.push(format!(
                "{name}: with std expected exactly {want:?}, got {with:?}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn pending_09_is_shrinking() {
    assert!(
        PENDING_09.len() <= PENDING_09_MAX,
        "PENDING_09 grew to {} (bound {PENDING_09_MAX}); an increment must lower it, never raise it",
        PENDING_09.len()
    );
    let dir = repo_root().join("tests/conformance/09-types");
    let names: Vec<String> = corpus_targets(&dir)
        .iter()
        .map(|t| {
            parse_directives(&directive_source(t))
                .name
                .replace('_', "-")
        })
        .collect();
    for (n, _) in PENDING_09 {
        assert!(
            names.iter().any(|x| x == n),
            "PENDING_09 names a test that is not in the corpus: {n}"
        );
    }
}

#[test]
fn no_panic_over_whole_corpus() {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
        entries.sort();
        for p in entries {
            if p.is_dir() {
                out.push(p.clone());
                walk(&p, out);
            }
        }
    }
    let mut dirs = vec![repo_root().join("tests/conformance")];
    walk(&repo_root().join("tests/conformance"), &mut dirs);
    for d in dirs {
        for t in corpus_targets(&d) {
            let _ = check_target(&t);
        }
    }
}

// ------------------------------------------------- increment I3's gate

/// design §11: the recorded `(parent, slot)` trace of every CHECK position
/// the corpus reaches EQUALS the declared table. A position that calls
/// `check` from a parent the table does not name is a silent change to
/// ch03 R25; a table row nothing reaches has rotted.
#[test]
fn check_positions_match_ch03_r25() {
    use fors_check::body::{CHECK_SITES, CheckSite};
    let mut seen: Vec<CheckSite> = Vec::new();
    for dir in [
        "09-types",
        "01-ownership",
        "02-failure",
        "03-numerics",
        "04-authority",
        "08-names",
        "10-std",
    ] {
        for target in corpus_targets(&repo_root().join("tests/conformance").join(dir)) {
            let (_, _, out) = check_target_full(&target);
            for s in out.check_sites {
                if !seen
                    .iter()
                    .any(|x| x.parent == s.parent && x.slot == s.slot)
                {
                    seen.push(s);
                }
            }
        }
    }
    let mut unauthorised = Vec::new();
    for s in &seen {
        if !CHECK_SITES
            .iter()
            .any(|r| r.parent == s.parent && r.slot == s.slot)
        {
            unauthorised.push(format!("{:?}/{:?}", s.parent, s.slot));
        }
    }
    assert!(
        unauthorised.is_empty(),
        "these CHECK positions are not in ch03 R25's table (or ch09's addenda): {unauthorised:?}"
    );
    let mut unreached = Vec::new();
    for r in CHECK_SITES {
        if r.corpus
            && !seen
                .iter()
                .any(|s| s.parent == r.parent && s.slot == r.slot)
        {
            unreached.push(format!("{:?}/{:?} (R{})", r.parent, r.slot, r.rule));
        }
    }
    assert!(
        unreached.is_empty(),
        "CHECK_SITES rows marked `corpus` that nothing reached: {unreached:?}"
    );
}

/// design §11: recovery. Every `check-error` test now on yields EXACTLY
/// one diagnostic — one root cause per declaration, no cascade.
#[test]
fn every_check_error_test_yields_exactly_one_diagnostic() {
    let dir = repo_root().join("tests/conformance/09-types");
    let mut failures = Vec::new();
    for target in corpus_targets(&dir) {
        let case = parse_directives(&directive_source(&target));
        if case.expect != "check-error" {
            continue;
        }
        let key = case.name.replace('_', "-");
        if PENDING_09.iter().any(|&(n, _)| n == key) {
            continue;
        }
        if matches!(expected_code(&case.detail), Some(('N', _)) | Some(('A', _))) {
            continue;
        }
        let (got, _, _) = check_target_full(&target);
        if got.len() != 1 {
            failures.push(format!("{key}: {} diagnostics {got:?}", got.len()));
        }
    }
    assert!(
        failures.is_empty(),
        "not exactly one diagnostic ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// design §11's store invariant: after checking the corpus every `Param`
/// row in the type store names a parameter some declaration really
/// declares. Nothing the body phase interns is a slot awaiting an answer —
/// there is no such thing in this checker, and this is the assertion from
/// the store's side.
#[test]
fn no_infer_variable_is_interned() {
    use fors_fir::ty::TyTag;
    use fors_index::ids::DefId;
    let mut failures = Vec::new();
    for dir in [
        "09-types",
        "01-ownership",
        "03-numerics",
        "08-names",
        "10-std",
    ] {
        for target in corpus_targets(&repo_root().join("tests/conformance").join(dir)) {
            let (_, _, out) = check_target_full(&target);
            let fir = &out.fir;
            for i in 0..fir.tys.len() {
                let t = fors_fir::ty::TyId(i as u32);
                if fir.tys.tag(t) != TyTag::Param {
                    continue;
                }
                let owner = DefId(fir.tys.a(t));
                let ord = fir.tys.b(t) as usize;
                let g = fir.sigs.generics(owner);
                if owner.index() >= fir.sigs.len() || ord >= fir.sigs.generics_store.count(g) {
                    failures.push(format!(
                        "{}: Param({}, {}) names no declared parameter",
                        target.display(),
                        owner.0,
                        ord
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "fabricated parameter rows ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// design §9: a body's `DepSet` is recorded, is a SET in `DefId` order, and
/// names only declarations this build has. Its `key` is order-free and
/// moves when a signature it names moves — the property I9's invalidation
/// test rests on.
#[test]
fn every_body_records_its_dep_set() {
    let dir = repo_root().join("tests/conformance/09-types");
    let mut bodies = 0usize;
    let mut with_deps = 0usize;
    for target in corpus_targets(&dir) {
        let (_, _, out) = check_target_full(&target);
        for (def, set) in &out.deps {
            bodies += 1;
            assert!(
                set.defs().windows(2).all(|w| w[0].0 < w[1].0),
                "{}: a DepSet must be sorted and deduplicated",
                target.display()
            );
            assert!(
                set.defs().iter().all(|d| d.index() < out.fir.sigs.len()),
                "{}: a DepSet names a declaration this build does not have",
                target.display()
            );
            // A body always reads at least its own signature.
            assert!(
                set.defs().contains(def),
                "{}: a body must record its own signature",
                target.display()
            );
            if set.len() > 1 {
                with_deps += 1;
            }
        }
    }
    assert!(
        bodies > 300,
        "only {bodies} bodies recorded a DepSet over the ch09 corpus"
    );
    assert!(
        with_deps > 100,
        "only {with_deps} bodies read another declaration's signature"
    );
}

// ------------------------------------------------- increment I4's gate

/// ch08 Rule 11's own carve-out: "because finding the member needs the
/// type, the checker enforces this clause". `fors-resolve`'s harness
/// listed `private_field_cross_module_rejected` in `PENDING_08` until
/// this increment; design §11 says "`PENDING_08` empties at I4", and
/// this is where the positive assertion lands, since only this crate has
/// the checker.
#[test]
fn private_field_cross_module_rejected() {
    let target = repo_root().join("tests/conformance/08-names/private-field-cross-module-rejected");
    assert!(
        target.is_dir(),
        "the ch08 target is a multi-module directory"
    );
    let case = parse_directives(&directive_source(&target));
    assert_eq!(case.name, "private_field_cross_module_rejected");
    let (checker, resolver) = check_target(&target);
    assert!(
        resolver.is_empty(),
        "the resolver defers this one to the checker, so it must stay clean: {resolver:?}"
    );
    // ch09 R49 reports ch08's code, not one of its own (design §10).
    assert_eq!(checker, vec!["N0011"]);
}

/// design §11, "member coverage": every name-use node ch08 Rule 22
/// DEFERRED to the checker ([`DeferReason::Member`]) is decided by it —
/// given a type, a member target or a callee — inside every body the
/// checker typed. A body whose declaration produced a diagnostic is
/// exempt: the per-declaration budget stops the walk at the root cause
/// (design §10), and the nodes after it are not "undecided", they are
/// unvisited on purpose.
#[test]
fn every_deferred_node_is_decided() {
    use fors_check::facts::{FactCallee, MemberTarget};
    use fors_fir::ty::NO_TY;
    use fors_resolve::target::{DeferReason, ResolvedTarget};

    let dir = repo_root().join("tests/conformance/09-types");
    let mut deferred = 0usize;
    let mut decided = 0usize;
    let mut failures = Vec::new();
    for target in corpus_targets(&dir) {
        // One tree per build, so a node index is unambiguous.
        if target.is_dir() {
            continue;
        }
        let case = parse_directives(&directive_source(&target));
        let key = case.name.replace('_', "-");
        let src = fs::read(&target).unwrap();
        let mut interner = Interner::new();
        let name = header_name(&src, &mut interner).unwrap_or_else(|| vec![interner.intern(b"m")]);
        let p = parse_file(&src);
        let inputs = [FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: &src,
            name,
        }];
        let resolved =
            fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
        let out = fors_check::check_build(&inputs, &resolved, &mut interner);
        let uses = &resolved.files[0].name_uses;
        // Rule 22 leaves a member tail to the checker in two shapes: a
        // whole path that is nothing but the tail (`DeferReason::Member`),
        // and a multi-segment path whose head resolved and whose
        // remaining segments did not (`consumed` below the path's segment
        // count). Both are this assertion's subject.
        let mut tails: Vec<u32> = Vec::new();
        for (i, &n) in uses.node.iter().enumerate() {
            let segs = fors_resolve::paths::own_span(&p.tree, n as usize);
            let segs = (segs.0 as usize..(segs.1 as usize).min(p.tokens.kinds.len()))
                .filter(|&t| p.tokens.kinds[t] == fors_lex::TokenKind::Ident)
                .count();
            let member = matches!(
                uses.target[i],
                ResolvedTarget::Deferred {
                    reason: DeferReason::Member
                }
            );
            if member || (segs > 0 && (uses.consumed[i] as usize) < segs) {
                tails.push(n);
            }
        }
        tails.sort_unstable();
        // The budget is one diagnostic per DECLARATION and the corpus's
        // `check-error` tests yield exactly one for the whole file, so
        // "this file spoke" and "this body's declaration spoke" coincide
        // over this corpus; the coarser test needs no byte arithmetic.
        let spoke = !out.diagnostics.is_empty();
        for (_, facts) in &out.facts {
            let (start, end) = facts.range();
            for n in start..end.min(p.tree.kinds.len() as u32) {
                if tails.binary_search(&n).is_err() {
                    continue;
                }
                deferred += 1;
                if facts.ty_of(n) != NO_TY
                    || facts.member_of(n) != MemberTarget::None
                    || !matches!(facts.callee_of(n), FactCallee::Undecided)
                {
                    decided += 1;
                } else if !spoke {
                    failures.push(format!(
                        "{key}: node {n} is a deferred member nobody decided"
                    ));
                }
            }
        }
    }
    eprintln!("deferred member nodes: {decided}/{deferred} decided");
    assert!(
        deferred > 250,
        "only {deferred} deferred member nodes over the ch09 corpus: the probe found nothing"
    );
    assert!(
        failures.is_empty(),
        "undecided deferred nodes ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ------------------------------------------------- increment I8's gate

/// The nine ch01-coded ch09 tests design §11 names ("The 9 ch01-coded
/// tests assert `Code::O(rule)` plus the clause letter in the message"),
/// with the code each one must carry. They are exactly the nine files
/// that were pending before I8 and pre-date round 6 — the other half of
/// §13's I8 GATE, "`PENDING_09` empty over the **186** pre-round-6 ch09
/// tests".
const CH01_CODED_09: &[(&str, &str)] = &[
    ("brand-param-as-value-type-rejected", "O0015"),
    ("copy-without-copyable-rejected", "O0003"),
    ("implicit-receiver-move-in-closure-rejected", "O0004"),
    ("implicit-receiver-move-in-loop-rejected", "O0004"),
    ("implicit-receiver-move-of-field-rejected", "O0004"),
    ("implicit-receiver-move-of-inout-param-rejected", "O0004"),
    ("implicit-receiver-move-of-let-param-rejected", "O0003"),
    ("implicit-receiver-move-then-use-rejected", "O0004"),
    ("qualified-call-sink-receiver-needs-move-rejected", "O0002"),
];

/// One corpus target's diagnostics as `(code, message)`.
fn check_target_messages(path: &Path) -> Vec<(String, String)> {
    let (_, _, out) = check_target_full(path);
    out.diagnostics
        .iter()
        .map(|d| (d.code.as_string(), d.message.clone()))
        .collect()
}

fn target_named(dir: &str, name: &str) -> PathBuf {
    let d = repo_root().join("tests/conformance").join(dir);
    corpus_targets(&d)
        .into_iter()
        .find(|t| {
            parse_directives(&directive_source(t))
                .name
                .replace('_', "-")
                == name
        })
        .unwrap_or_else(|| panic!("{dir} has no test named {name}"))
}

/// The clause a ch01-coded test's own `detail` line cites, as the first
/// word pair of that line (`ch01 R4a(c)`, `ch01 R3`, `ch01 R15d`).
fn cited_clause(detail: &str) -> String {
    detail
        .split("--")
        .next()
        .unwrap_or(detail)
        .trim()
        .trim_end_matches(',')
        .to_string()
}

#[test]
fn ch01_coded_tests_assert_their_code_and_clause() {
    let mut failures = Vec::new();
    for &(name, code) in CH01_CODED_09 {
        assert!(
            !PENDING_09.iter().any(|&(n, _)| n == name),
            "{name} is one of the nine ch01-coded tests and must not be pending"
        );
        let target = target_named("09-types", name);
        let clause = cited_clause(&parse_directives(&directive_source(&target)).detail);
        assert!(
            clause.starts_with("ch01 R"),
            "{name}: its detail line must cite a ch01 clause, found {clause:?}"
        );
        let got = check_target_messages(&target);
        if got.len() != 1 {
            failures.push(format!(
                "{name}: expected exactly one diagnostic, got {got:?}"
            ));
            continue;
        }
        if got[0].0 != code {
            failures.push(format!("{name}: expected {code}, got {}", got[0].0));
        }
        if !got[0].1.contains(&clause) {
            failures.push(format!(
                "{name}: the message must cite {clause:?}; got {:?}",
                got[0].1
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "ch01-coded ch09 tests ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The two `check-ok` halves §13's I8 GATE names beside the nine: an
/// implicit receiver move on a `sink` local is accepted, and a `Copyable`
/// receiver is COPIED, so it stays usable for a second call.
#[test]
fn implicit_receiver_moves_that_are_legal_are_accepted() {
    for name in [
        "implicit-receiver-move-accepted",
        "sink-receiver-copyable-not-moved-accepted",
    ] {
        let got = check_target_messages(&target_named("09-types", name));
        assert!(got.is_empty(), "{name} must be accepted, got {got:?}");
    }
}

/// ch09 Rule 46's NORMATIVE diagnostic requirement, asserted as the
/// rendered string (design §11: "the R46 test asserts the rendered
/// string"). The two positions are read out of the corpus file itself, so
/// the assertion pins the SHAPE of the sentence and the facts it names
/// without pinning the file's line numbering.
#[test]
fn r46_message_names_the_consuming_call_and_the_sink_self_declaration() {
    let target = target_named("09-types", "implicit-receiver-move-then-use-rejected");
    let src = fs::read_to_string(&target).unwrap();
    // The `//!` directive block quotes the program, so the search starts
    // at the first declaration rather than at byte 0.
    let code = src
        .find("module m;")
        .expect("the corpus file names its module");
    let at = |needle: &str| {
        let byte = code
            + src[code..]
                .find(needle)
                .expect("the corpus file still writes this");
        let (l, c) = fors_diag::line_col(src.as_bytes(), byte as u32);
        format!("{l}:{c}")
    };
    let decl_at = at("fn finish(");
    // The consuming call is the one in `f`, after the `impl` block.
    let body = code + src[code..].find("fn f(").expect("the test still has `f`");
    let call_byte = body + src[body..].find("b.finish()").expect("`f` calls it");
    let (cl, cc) = fors_diag::line_col(src.as_bytes(), call_byte as u32);
    let call_at = format!("{cl}:{cc}");
    let want = format!(
        "`b` was moved by the call `b.finish()` at {call_at}, because `Builder.finish` takes \
         `sink self` (declared at {decl_at})"
    );
    let got = check_target_messages(&target);
    assert_eq!(got.len(), 1, "one diagnostic, got {got:?}");
    assert_eq!(got[0].0, "O0004", "the code stays ch01's (ch09 R46)");
    assert!(
        got[0].1.ends_with(&want),
        "R46's mandatory sentence must close the message.\nwant suffix: {want}\ngot:         {}",
        got[0].1
    );
}

/// ch01's own marker corpus, which §13's I8 GATE names ("From ch01: the 6
/// `01.R2` marker tests and the two `01.R1` tests"). The three `01.R2`
/// `check-error` files are the checker's — `call::conv_marker`, O0002 —
/// and the three accepted ones must stay silent. The two `01.R1` files
/// are the PARSER's: a parameter with no convention keyword does not
/// parse as a parameter at all, which is why Rule 1 has no checker code.
#[test]
fn ch01_convention_and_marker_tests() {
    let mut failures = Vec::new();
    for (name, expect) in [
        ("conv-missing-inout-marker-rejected", Some("O0002")),
        ("conv-missing-move-rejected", Some("O0002")),
        ("conv-missing-set-marker-rejected", Some("O0002")),
        ("conv-inout-marker-present-accepted", None),
        ("conv-move-present-accepted", None),
        ("conv-set-marker-present-accepted", None),
    ] {
        let target = target_named("01-ownership", name);
        let case = parse_directives(&directive_source(&target));
        assert_eq!(case.rule, 2, "{name} must cite 01.R2");
        let got = check_target_messages(&target);
        match expect {
            Some(code) => {
                if got.len() != 1 || got[0].0 != code {
                    failures.push(format!("{name}: expected one {code}, got {got:?}"));
                } else if !got[0].1.contains("ch01 R2") {
                    failures.push(format!("{name}: the message must cite ch01 R2: {got:?}"));
                }
            }
            None => {
                if !got.is_empty() {
                    failures.push(format!("{name}: expected silence, got {got:?}"));
                }
            }
        }
    }
    // 01.R1 is a grammar fact, so these two are asserted at the parser.
    for (name, parses) in [
        ("conv-convention-present-accepted", true),
        ("conv-missing-convention-rejected", false),
    ] {
        let target = target_named("01-ownership", name);
        let case = parse_directives(&directive_source(&target));
        assert_eq!(case.rule, 1, "{name} must cite 01.R1");
        let src = fs::read(&target).unwrap();
        let p = parse_file(&src);
        if p.diags.is_empty() != parses {
            failures.push(format!(
                "{name}: expected the parser to {}, got {:?}",
                if parses { "accept" } else { "reject" },
                p.diags
            ));
        }
        if parses {
            let got = check_target_messages(&target);
            if !got.is_empty() {
                failures.push(format!("{name}: the checker must stay silent, got {got:?}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "ch01 convention/marker tests ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// ch01 Rule 8's own two corpus files (I8 verification, 2026-10-02): a
/// move on the `if` branch with the `else` branch leaving the place live
/// is the disagreement, O0008 citing ch01 R8, reported once; consuming on
/// both branches resolves it. The `check-ok` half is `parse-ok` in the
/// corpus, so `no_new_diagnostics_outside_ch09` does not cover it.
#[test]
fn ch01_merge_liveness_tests() {
    let got = check_target_messages(&target_named(
        "01-ownership",
        "merge-liveness-disagreement-rejected",
    ));
    assert_eq!(got.len(), 1, "one diagnostic, got {got:?}");
    assert_eq!(got[0].0, "O0008");
    assert!(got[0].1.contains("ch01 R8"), "got {:?}", got[0].1);
    let got = check_target_messages(&target_named(
        "01-ownership",
        "merge-liveness-resolved-accepted",
    ));
    assert!(got.is_empty(), "both branches consume: got {got:?}");
}

// ----------------------------------------- increment I10's ch01 half (B)

/// design §13's I10 GATE, ch01 side: "the type-dependent subset of ch01's
/// [`check-error`] tests ... scoped in this increment from the rule list"
/// R14-R18 and R21-R21d (brands and `Shared`; R14's `secret` composition
/// has no `check-error` file). Each row is `(test, code, clause)`: exactly
/// one checker diagnostic, of that code, whose message cites `ch01` and the
/// clause the file's own `//! rule:` line names. Same assertion shape as
/// [`CH01_CODED_09`].
///
/// `brand-param-two-arenas-rejected` keeps ch09's T0026: the ch09 corpus
/// asserts T0026 for exactly this program shape
/// (`09-types/two-brands-one-param-rejected`, "A is bound to `two` by the
/// first argument; the second argument's brand `one` disagrees"), so the
/// one code per fault is ch09's and the message names R15d.
const I10_CH01_CODED: &[(&str, &str, &str)] = &[
    ("arena-binding-move-rejected", "O0015", "R15a"),
    ("arena-no-constructor", "O0015", "R15a"),
    ("brand-kind-closed", "O0015", "R15d"),
    ("brand-param-two-arenas-rejected", "T0026", "R15d"),
    ("arena-brand-mismatch-rejected", "O0016", "R16"),
    ("atomic-outside-shared-rejected", "O0021", "R21"),
    (
        "shared-atomic-field-without-shared-impl-rejected",
        "O0021",
        "R21",
    ),
    ("shared-fieldwise-check-rejected", "O0021", "R21a"),
    ("shared-impl-enum-payload-checked", "O0021", "R21a"),
    ("shared-impl-generic-field-needs-bound", "O0021", "R21a"),
];

/// The accepted twins of the same rules (`parse-ok` in the corpus, so no
/// other assertion reaches them): the new checks must stay silent on them.
const I10_CH01_ACCEPTED: &[&str] = &[
    "arena-brand-match-accepted",
    "brand-param-helper-accepted",
    "brand-field-requires-param-accepted",
    "shared-fieldwise-check-accepted",
    "shared-impl-generic-field-with-bound",
    "shared-unsafe-impl-form-accepted",
    "shared-generic-bound-accepted",
];

/// The three ch01 tests whose programs disagree with the real `std`, which is
/// in every build (item 47(a): ch08 R17's prelude names always denote std's
/// items). Alone, each was checked against OPAQUE prelude rows and was
/// silent; against `std`'s declarations each reports exactly the listed
/// code, and that exact observation is the pin (it fails the moment the
/// disagreement is resolved, so the row must then move back to
/// [`I10_CH01_CODED`] / [`I10_CH01_ACCEPTED`]):
///
/// * `with-allocator-brand` (`O0018` expected) and
///   `with-allocator-brand-match-accepted`: both write `heap.create(n)`
///   bare, and `std`'s `Allocator.create` is `raises AllocError` (ch10 S0012), so ch02
///   R1's `F0001` is reported first and (in the first) is the one
///   diagnostic, masking the brand mismatch;
/// * `secret-iso-composition-accepted`: `Buffer[u8]`, the one-argument
///   spelling ch10 S0002's own table cites for `Buffer`, against ch10
///   S0023's `Buffer[T, N: usize]`: `T0011`, two type arguments declared.
///
/// The corpus and ch10 disagree with each other here; neither is the
/// checker's to change.
const I10_CH01_STD_CONFLICTS: &[(&str, &str)] = &[
    ("with-allocator-brand", "F0001"),
    ("with-allocator-brand-match-accepted", "F0001"),
    ("secret-iso-composition-accepted", "T0011"),
];

/// The in-scope (R14-R18, R21-R21d) `check-error` tests this increment does
/// NOT turn on, each with the phase or fix that decides it. The checker is
/// silent on every one (asserted below), because the fault is already
/// reported before it, or the file cannot reach it.
const I10_CH01_WAITING: &[(&str, &str)] = &[
    (
        "arena-brand-nonescape-rejected",
        "ch01 R15: the brand `x` in `fn leak() -> Ref[Node[x], x]` has no spelling outside its \
         `with` block, so the resolver reports N0014 at both uses (ch08 R14) — the escape is \
         impossible to WRITE, which is R15's own non-escape argument (a)",
    ),
    (
        "brand-field-requires-param",
        "ch01 R15d: `struct Holder { r: Ref[Node[A], A] }` declares no `A`, so `A` is unbound \
         and the resolver reports N0014 twice; the checker never sees a brand to judge",
    ),
    (
        "shared-blanket-impl-rejected",
        "ch01 R21a's blanket clause is decided twice already: ch08 R21's orphan rule (N0021, \
         `Shared` is a prelude trait and `T` no item) and ch09 R18 (T0018); a third code for one \
         fault would be noise",
    ),
    (
        "shared-impl-outside-defining-module-rejected",
        "ch01 R21a's defining-module clause IS ch08 R21's orphan rule for a prelude trait; and \
         the directory test's layout breaks ch08 R24 (`holder.fors` declares `module \
         lib.counter;`, `main.fors` `module app;`: N0001 twice, N0004, N0014), so the impl's \
         head never resolves and the definite-only `Shared` pass stays silent",
    ),
];

/// The directive's own `rule:` text (`01.R15a`).
fn directive_rule(src: &str) -> String {
    src.lines()
        .find_map(|l| l.strip_prefix("//! rule:"))
        .map(|r| r.trim().to_string())
        .unwrap_or_default()
}

#[test]
fn i10_ch01_brand_and_shared_tests_assert_their_code_and_clause() {
    let mut failures = Vec::new();
    for &(name, code, clause) in I10_CH01_CODED {
        let target = target_named("01-ownership", name);
        let src = directive_source(&target);
        if directive_rule(&src) != format!("01.{clause}") {
            failures.push(format!(
                "{name}: the table names {clause}, the file cites {}",
                directive_rule(&src)
            ));
        }
        let got = check_target_messages(&target);
        if got.len() != 1 {
            failures.push(format!(
                "{name}: expected exactly one diagnostic, got {got:?}"
            ));
            continue;
        }
        if got[0].0 != code {
            failures.push(format!("{name}: expected {code}, got {}", got[0].0));
        }
        if !got[0].1.contains("ch01 ") || !got[0].1.contains(clause) {
            failures.push(format!(
                "{name}: the message must cite ch01 {clause}; got {:?}",
                got[0].1
            ));
        }
        if let Some(num) = code.strip_prefix('O') {
            let n: u16 = num.parse().unwrap();
            if !fors_check::rules::CH01_RULES.iter().any(|e| {
                e.code == Some(n) && e.status == fors_check::rules::RuleStatus::Implemented
            }) {
                failures.push(format!("{name}: {code} has no implemented CH01_RULES row"));
            }
        }
    }
    for &name in I10_CH01_ACCEPTED {
        let got = check_target_messages(&target_named("01-ownership", name));
        if !got.is_empty() {
            failures.push(format!("{name}: expected silence, got {got:?}"));
        }
    }
    for &(name, code) in I10_CH01_STD_CONFLICTS {
        let got = check_target_messages(&target_named("01-ownership", name));
        if got.len() != 1 || got[0].0 != code {
            failures.push(format!(
                "{name}: pinned to exactly one {code} (a std conflict), got {got:?}"
            ));
        }
    }
    for &(name, _) in I10_CH01_WAITING {
        let target = target_named("01-ownership", name);
        assert_eq!(
            parse_directives(&directive_source(&target)).expect,
            "check-error",
            "{name}: I10_CH01_WAITING lists check-error files only"
        );
        let got = check_target_messages(&target);
        if !got.iter().all(|(c, _)| c == "T0018") || got.len() > 1 {
            failures.push(format!("{name}: waiting, but the checker said {got:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "I10's ch01 brand/Shared tests ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ------------------------------------------------ increment I8b's gate

/// design §13's I8b GATE, by rule group. Round 6 (ch01 O1-O3) added these
/// `check-error` files to `01-ownership`; before this increment the
/// checker was required to stay SILENT on every one of them (nothing
/// asserted them, and `no_new_diagnostics_outside_ch09` covers only
/// `check-ok`/`run-ok`). **The harness expectation flips here and nowhere
/// else**: each of them must now yield EXACTLY ONE diagnostic. The code is
/// not pinned per row because most of these files' `detail` lines cite a
/// ch01 clause rather than a code, and several cite two (a `?` that leaks
/// AND an `errdefer` that can never run); what the design fixes is that
/// there is one root cause and the checker finds it.
const I8B_CH01_REJECTED: &[(&str, &str)] = &[
    // R22h/R22i (9)
    ("linear-local-dropped-at-block-end-rejected", "R22h"),
    ("linear-local-dropped-at-return-rejected", "R22h"),
    ("linear-local-dropped-at-question-rejected", "R22h"),
    ("linear-local-dropped-at-break-rejected", "R22h"),
    ("linear-temporary-expression-statement-rejected", "R22h"),
    ("linear-let-underscore-rejected", "R22h"),
    ("linear-var-overwritten-rejected", "R22h"),
    ("linear-sink-parameter-unconsumed-rejected", "R22h"),
    (
        "user-linear-type-diagnostic-names-consumer-rejected",
        "R22i",
    ),
    // R22d-R22g (the `-rejected` half of the group's 18)
    (
        "linear-consumed-by-struct-literal-then-aggregate-rejected",
        "R22a(b)",
    ),
    ("linear-match-underscore-rejected", "R22d(ii)"),
    ("linear-match-omitted-field-rejected", "R22d(ii)"),
    ("linear-consume-rejected", "R22d"),
    ("linear-discard-rejected", "R22d"),
    ("linear-in-loop-consumed-once-rejected", "R4a(b)"),
    ("linear-field-partial-move-rejected", "R4a(c)"),
    ("linear-captured-by-closure-still-owed-rejected", "R22g"),
    ("linear-with-block-exit-rejected", "R22g"),
    ("linear-trap-does-not-consume-rejected", "R22d"),
    ("linear-impl-with-bound-rejected", "R22"),
    // R23-R23f, check side (the `-rejected` half of the group's 20)
    ("errdefer-normal-exit-unconsumed-rejected", "R22h"),
    ("defer-place-moved-before-exit-rejected", "R23d(a)"),
    ("defer-in-loop-moves-outer-rejected", "R23d(d)"),
    ("defer-return-inside-rejected", "R23c"),
    ("defer-raise-inside-rejected", "R23c"),
    ("defer-question-inside-rejected", "R23c"),
    ("defer-break-outer-loop-rejected", "R23c"),
    ("errdefer-without-error-exit-rejected", "R23b"),
    ("errdefer-after-fallible-call-rejected", "R23b"),
    (
        "linear-enum-payload-one-arm-unconsumed-rejected",
        "R22d(ii)",
    ),
    // R19c/R19d: the first needs no `std`; the second's adaptor chain needs
    // it, and item 47(a) put it in every build.
    ("closure-returned-with-local-capture-rejected", "R19d"),
    ("closure-capture-in-chain-returned-rejected", "R19d"),
];

/// The `check-ok` halves of the same groups: the programs round 6 calls
/// well-formed, which the new machinery must not reject. Together with the
/// list above these are design §13's I8b GATE minus the files whose rules
/// still silent with `std` (listed in `I8B_R19C_GAPS`).
const I8B_CH01_ACCEPTED: &[&str] = &[
    "linear-consumed-by-sink-call-accepted",
    "linear-consumed-by-return-accepted",
    "linear-consumed-by-implicit-receiver-move-accepted",
    "linear-aggregate-destructured-accepted",
    "linear-option-matched-accepted",
    "linear-in-loop-reinit-accepted",
    "linear-spawn-move-accepted",
    "linear-with-block-defer-accepted",
    "defer-consumes-linear-on-all-exits-accepted",
    "errdefer-consumes-on-error-exit-accepted",
    "defer-inout-use-after-defer-accepted",
    "defer-in-loop-per-iteration-accepted",
    "defer-inner-loop-break-accepted",
    "defer-handler-inside-accepted",
    "defer-with-block-allocator-live-accepted",
    "defer-in-closure-body-accepted",
    "defer-nested-body-accepted",
    "errdefer-and-defer-interleaved-reverse-order-accepted",
    // The R19c/R19d `check-ok` rows that were `I8B_NEEDS_STD` while the
    // harness built one file alone (item 47(a): `std` is in every build).
    "scoped-through-generic-sink-consumed-accepted",
    "scoped-through-generic-sink-returned-under-scoped-accepted",
    "scoped-rvalue-extent-is-the-statement-accepted",
    "scoped-rvalue-extent-is-the-for-accepted",
    "zip-two-scoped-sources-local-accepted",
    "zip-scoped-and-owned-accepted",
    "closure-capture-keeps-local-in-chain-accepted",
];

/// design §13's I8b GATE, R19c/R19d group: the `check-error` files whose
/// subject is a call that returns a value keeping a `scoped` argument
/// (`v.iter().zip(..)`, `keep(v.as_str())`, a generic `sink`). These were
/// listed as "needs `std`" while the harness built one file alone, where
/// `Vec`, `String` and `.iter()` were prelude OPAQUE rows. Item 47(a)
/// puts `std` in every build, so that reason is gone and the harness now
/// builds them with it: the `-accepted` rows moved to `I8B_CH01_ACCEPTED`
/// and `closure-capture-in-chain-returned-rejected` to `I8B_CH01_REJECTED`,
/// each now ordinary. What stays here is what is STILL silent with `std` in
/// the build: R19c's rejection of a scoped argument kept by the result of a
/// generic or concrete `sink`, `inout` or `raises` call is not yet reported
/// by the checker (a checker gap, not a missing `std`). Each row is listed,
/// with its file, rather than skipped, and the assertion below is the
/// honest one: the checker must stay silent on it exactly until the gap
/// closes, and a row whose file starts producing a diagnostic must leave
/// this list for `I8B_CH01_REJECTED`.
const I8B_R19C_GAPS: &[&str] = &[
    "scoped-through-generic-sink-result-scoped-rejected",
    "scoped-through-generic-inout-param-rejected",
    "scoped-through-generic-raises-rejected",
    "scoped-into-concrete-sink-rejected",
    "scoped-copy-into-field-via-let-param-rejected",
    "zip-two-scoped-sources-rejected",
    "adaptor-chain-for-mutates-source-rejected",
];

#[test]
fn i8b_round6_ch01_rejected_files_yield_exactly_one_diagnostic() {
    let mut failures = Vec::new();
    for &(name, clause) in I8B_CH01_REJECTED {
        let target = target_named("01-ownership", name);
        let case = parse_directives(&directive_source(&target));
        if case.expect != "check-error" {
            failures.push(format!(
                "{name}: expected a check-error file, found {:?}",
                case.expect
            ));
            continue;
        }
        let got = check_target_messages(&target);
        if got.len() != 1 {
            failures.push(format!(
                "{name} (ch01 {clause}): expected exactly one diagnostic, got {got:?}"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "I8b's round-6 ch01 rejections ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn i8b_round6_ch01_accepted_files_are_silent() {
    let mut failures = Vec::new();
    for &name in I8B_CH01_ACCEPTED {
        let target = target_named("01-ownership", name);
        let case = parse_directives(&directive_source(&target));
        assert_eq!(
            case.expect, "check-ok",
            "{name}: this list is the check-ok half"
        );
        let got = check_target_messages(&target);
        if !got.is_empty() {
            failures.push(format!("{name}: expected silence, got {got:?}"));
        }
    }
    // The seven behaviour tests design §13 assigns to FMIR F4 are NOT in
    // this gate; I8b's obligation on them is only that it emits nothing.
    for name in [
        "defer-reverse-order-run-ok",
        "defer-runs-on-return-run-ok",
        "defer-per-iteration-run-ok",
        "defer-nested-scope-order-run-ok",
        "defer-result-evaluated-first-run-ok",
        "errdefer-skipped-on-return-run-ok",
    ] {
        let got = check_target_messages(&target_named("01-ownership", name));
        if !got.is_empty() {
            failures.push(format!("{name}: F4's behaviour test, got {got:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "I8b's round-6 ch01 acceptances ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The R19c/R19d `check-error` files the checker is still silent on, with
/// `std` in the build (see [`I8B_R19C_GAPS`]): each is a ch01 `check-error`
/// test, and a row whose file starts producing a diagnostic has been fixed
/// and must leave the list.
#[test]
fn i8b_r19c_gap_rows_are_still_silent_with_std() {
    let mut failures = Vec::new();
    for &name in I8B_R19C_GAPS {
        let target = target_named("01-ownership", name);
        let case = parse_directives(&directive_source(&target));
        if case.expect != "check-error" {
            failures.push(format!("{name}: a gap row must be a check-error file"));
        }
        let got = check_target_messages(&target);
        if !got.is_empty() {
            failures.push(format!("{name}: expected silence, got {got:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "I8b's R19c gap rows ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// ch01 Rule 22i's NORMATIVE CONTENT (not wording), asserted as the
/// rendered string on the corpus file whose `detail` enumerates it: "the
/// diagnostic carries the value `r`, its type `Res`, the exit (the `}` of
/// the body) and the consumer `Res.close`".
#[test]
fn r22i_diagnostic_carries_the_value_type_exit_and_consumer() {
    let target = target_named(
        "01-ownership",
        "user-linear-type-diagnostic-names-consumer-rejected",
    );
    let got = check_target_messages(&target);
    assert_eq!(got.len(), 1, "one diagnostic, got {got:?}");
    assert_eq!(got[0].0, "O0022", "ch01 R22's own code");
    let m = &got[0].1;
    for want in [
        "`r`",                    // the value's name
        "`Res`",                  // its type as ch09 R20 displays it
        "of the block opened at", // the exit's kind
        "`Res.close`",            // the consumer, from the head's defining module
        "ch01 R22h",              // the clause
    ] {
        assert!(
            m.contains(want),
            "R22i requires {want:?} in the diagnostic; got {m:?}"
        );
    }
    // The exit's LOCATION, read out of the corpus file rather than pinned.
    let src = fs::read_to_string(&target).unwrap();
    let code = src.find("fn f()").expect("the corpus file still has `f`");
    let brace = code + src[code..].find('{').expect("`f` has a body");
    let (l, c) = fors_diag::line_col(src.as_bytes(), brace as u32);
    assert!(
        m.contains(&format!("{l}:{c}")),
        "R22i requires the exit's location {l}:{c}; got {m:?}"
    );
}

/// design §13's "Interface to FMIR lowering": D7, D8 and D9 exist under
/// exactly those names, and carry the shapes `fmir-interpreter.md` §3.5
/// and §3.8 describe. F4's and F6's lowering halves read these, so the
/// assertion is on the DATA, not on a diagnostic.
#[test]
fn d7_d8_d9_are_published_for_fmir_lowering() {
    use fors_check::facts::{Access, DeferKind, Discharge, ExitEdgeKind};
    let target = target_named(
        "01-ownership",
        "defer-consumes-linear-on-all-exits-accepted",
    );
    let (checker, _, out) = check_target_full(&target);
    assert!(checker.is_empty(), "the file is accepted: {checker:?}");
    let body = out
        .facts
        .iter()
        .find(|(_, f)| !f.defer_regions.rows.is_empty())
        .map(|(_, f)| f)
        .expect("D7: some body has a defer region");
    // D7: one `defer` row, with its scope, kind, body and stmt_order.
    assert_eq!(body.defer_regions.rows.len(), 1);
    assert_eq!(body.defer_regions.rows[0].kind, DeferKind::Defer);
    assert!(body.defer_regions.rows[0].scope > 0);
    // D7: the place -> strongest-access summary (R23d), and `r.close()`
    // is a MOVE.
    assert!(
        body.defer_regions
            .accesses
            .iter()
            .any(|a| a.access == Access::Move),
        "D7: R23d's summary must record the deferred move"
    );
    // D7: every exit edge, with the bodies that run on it in order.
    assert!(
        body.defer_regions
            .exits
            .iter()
            .any(|e| e.kind == ExitEdgeKind::Question && !e.defers.is_empty()),
        "D7: the `?`'s error edge runs the pending `defer`"
    );
    assert!(
        body.defer_regions
            .exits
            .iter()
            .any(|e| e.kind == ExitEdgeKind::BlockEnd && !e.scopes.is_empty()),
        "D7: a block-end edge names the scopes it leaves"
    );
    // D8: the obligation, `lin(T)` per `TyId`, and one `Discharge` per
    // obligation per exit edge.
    assert_eq!(
        body.linear_obligations.obligations.len(),
        1,
        "D8: `r` is the one obligation"
    );
    assert!(
        body.linear_obligations.lin.iter().all(|&(_, v)| v),
        "D8: `lin(T)` per TyId"
    );
    assert!(
        body.linear_obligations
            .discharges
            .iter()
            .any(|d| matches!(d.how, Discharge::DeferredBody { .. })),
        "D8: the deferred body is what consumed it (R22d(iii))"
    );
    // D9: a capturing closure's sources (R19d).
    let (_, _, out) = check_target_full(&target_named(
        "01-ownership",
        "closure-returned-with-local-capture-rejected",
    ));
    assert!(
        out.facts
            .iter()
            .any(|(_, f)| !f.scoped_sources.rows.is_empty()),
        "D9: the capturing closure's source set is published"
    );
}

/// D7 against FMIR F4's own oracle. For every exit edge of every body of
/// the `defer`/`errdefer` corpus files, the multiset D7 publishes — in
/// run order — equals what `fors_fmir::exit::expected_pending` computes
/// from the same rows once they are laid out as F4's `ScopePool` /
/// `DeferPool`. This is the assertion design §13 names ("F4's verifier
/// check is an assertion against D7, not a re-derivation"), run here so
/// the two sides cannot drift.
#[test]
fn d7_exit_multisets_match_fmir_expected_pending() {
    use fors_check::facts::{DeferKind, ExitEdgeKind};
    use fors_fmir::exit::{ExitKind, expected_pending};
    use fors_fmir::ids::{BlockId, BrandId, DeferId, RegionId, ScopeId};
    use fors_fmir::scope::{DeferKind as FKind, DeferPool, DeferRow, ScopePool, ScopeRow};
    let mut edges = 0usize;
    let mut with_bodies = 0usize;
    for name in [
        "errdefer-and-defer-interleaved-reverse-order-accepted",
        "defer-nested-body-accepted",
        "defer-inner-loop-break-accepted",
        "defer-in-loop-per-iteration-accepted",
        "defer-consumes-linear-on-all-exits-accepted",
        "errdefer-consumes-on-error-exit-accepted",
        "defer-with-block-allocator-live-accepted",
        "defer-in-closure-body-accepted",
    ] {
        let (checker, _, out) = check_target_full(&target_named("01-ownership", name));
        assert!(checker.is_empty(), "{name}: {checker:?}");
        for (_, f) in &out.facts {
            let d7 = &f.defer_regions;
            if d7.rows.is_empty() {
                continue;
            }
            // Every scope D7 mentions, each one's rows laid out contiguously.
            let mut scopes: Vec<u32> = Vec::new();
            for r in &d7.rows {
                if !scopes.contains(&r.scope) {
                    scopes.push(r.scope);
                }
            }
            for e in &d7.exits {
                for &s in &e.scopes {
                    if !scopes.contains(&s) {
                        scopes.push(s);
                    }
                }
            }
            for e in &d7.exits {
                // ch01 R23a: a body is pending on an exit only when its
                // statement was executed on that path, i.e. textually
                // precedes the exit (a `}` is after everything). FMIR's
                // `ScopeRow.defers` is one range per scope, so the oracle
                // is fed the rows pending AT THIS EDGE: that cut is what
                // `fors-lower` must reproduce when it lays the pool out.
                let pending_here = |r: &fors_check::facts::DeferRegionRow| {
                    e.kind == ExitEdgeKind::BlockEnd || r.body < e.node
                };
                let mut defers = DeferPool::new();
                let mut pool = ScopePool::new();
                let mut row_id: Vec<Option<DeferId>> = vec![None; d7.rows.len()];
                let mut scope_id: Vec<(u32, ScopeId)> = Vec::new();
                for &s in &scopes {
                    let start = defers.len() as u32;
                    for (i, r) in d7.rows.iter().enumerate() {
                        if r.scope != s || !pending_here(r) {
                            continue;
                        }
                        row_id[i] = Some(defers.push(DeferRow {
                            kind: match r.kind {
                                DeferKind::Defer => FKind::Defer,
                                DeferKind::ErrDefer => FKind::ErrDefer,
                            },
                            body: BlockId(r.body),
                            stmt_order: u16::try_from(r.stmt_order).expect("a u16 statement order"),
                        }));
                    }
                    let end = defers.len() as u32;
                    let id = pool.push(ScopeRow {
                        parent: ScopeId::NONE,
                        brand: BrandId::NONE,
                        defers: start..end,
                        obligations: 0..0,
                        region: RegionId::NONE,
                    });
                    scope_id.push((s, id));
                }
                let sid = |s: u32| {
                    scope_id
                        .iter()
                        .find(|&&(n, _)| n == s)
                        .map(|&(_, i)| i)
                        .unwrap()
                };
                let leaving: Vec<ScopeId> = e.scopes.iter().map(|&s| sid(s)).collect();
                let kind = match e.kind {
                    ExitEdgeKind::Raise | ExitEdgeKind::Question => ExitKind::Error,
                    _ => ExitKind::Normal,
                };
                let want = expected_pending(&pool, &defers, &leaving, kind);
                let got: Vec<DeferId> = e
                    .defers
                    .iter()
                    .map(|&i| row_id[i as usize].expect("a body D7 says runs here is pending here"))
                    .collect();
                assert_eq!(
                    got, want,
                    "{name}: D7's {:?} edge at node {}",
                    e.kind, e.node
                );
                edges += 1;
                if !got.is_empty() {
                    with_bodies += 1;
                }
            }
        }
    }
    assert!(
        edges >= 16 && with_bodies >= 8,
        "the oracle saw {edges} edges, {with_bodies} with bodies"
    );
}

/// D8's contract for F6: on every exit edge, every obligation that is OWED
/// there — its scope is among the scopes the edge leaves, its binding is
/// written before the exit and the exit is not inside its own declaring
/// statement — carries exactly ONE `Discharge`. Over every accepted
/// round-6 file, so a path-insensitive discharge (credited from another
/// branch) or a missing one cannot hide behind a silent checker.
#[test]
fn d8_carries_one_discharge_per_owed_obligation_per_exit_edge() {
    use fors_check::facts::ExitEdgeKind;
    let mut owed = 0usize;
    for &name in I8B_CH01_ACCEPTED {
        let (checker, _, out) = check_target_full(&target_named("01-ownership", name));
        assert!(checker.is_empty(), "{name}: {checker:?}");
        for (_, f) in &out.facts {
            let d7 = &f.defer_regions;
            let d8 = &f.linear_obligations;
            for (i, e) in d7.exits.iter().enumerate() {
                for o in &d8.obligations {
                    if !e.scopes.contains(&o.scope)
                        || (e.node >= o.decl.0 && e.node < o.decl.1)
                        || (e.kind != ExitEdgeKind::BlockEnd && o.root > e.node)
                    {
                        continue;
                    }
                    let n = d8
                        .discharges
                        .iter()
                        .filter(|d| d.exit == i as u32 && d.root == o.root)
                        .count();
                    assert_eq!(
                        n, 1,
                        "{name}: the obligation at node {} on the {:?} edge at node {} has {n} discharges",
                        o.root, e.kind, e.node
                    );
                    owed += 1;
                }
            }
        }
    }
    assert!(
        owed >= 20,
        "D8 covered {owed} owed (obligation, edge) pairs"
    );
}
