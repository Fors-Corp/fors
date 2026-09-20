//! Conformance-corpus tests for `fors-resolve`: ch08 (name resolution)
//! and the subset of ch04 (authority) this crate implements — see
//! `tests/conformance/README.md` for the directive format.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use fors_index::{Interner, Segments, module::is_legal_segment};
use fors_resolve::{Code, Diagnostic, FileInput};
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
    rule_chapter: u8, // 8 or 4
    rule_num: u16,
    expect: String,
}

fn parse_directives(src: &str) -> Case {
    let mut name = String::new();
    let mut rule_chapter = 0u8;
    let mut rule_num = 0u16;
    let mut expect = String::new();
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            break;
        };
        let rest = rest.trim();
        if let Some(v) = rest.strip_prefix("name:") {
            name = v.trim().to_string();
        } else if let Some(v) = rest.strip_prefix("rule:") {
            let v = v.trim();
            // "08.R7" or "07.Grammar" etc; we only care about "NN.Rk".
            // Ch10 numbers its rules "10.S2" (its codes are S00nn), so the
            // prefix letter is per chapter, not always `R`.
            if let Some((ch, r)) = v.split_once('.')
                && let Some(k) = r.strip_prefix('R').or_else(|| r.strip_prefix('S'))
            {
                // "2a" -> "2", "11c" -> "11", "22h" -> "22": a rule
                // number is digits plus an optional letter suffix.
                let k: &str = &k[..k.find(|c: char| !c.is_ascii_digit()).unwrap_or(k.len())];
                if let (Ok(c), Ok(n)) = (ch.parse::<u8>(), k.parse::<u16>()) {
                    rule_chapter = c;
                    rule_num = n;
                }
            }
        } else if let Some(v) = rest.strip_prefix("expect:") {
            expect = v.split("--").next().unwrap_or(v).trim().to_string();
        }
    }
    Case {
        name,
        rule_chapter,
        rule_num,
        expect,
    }
}

/// Builds and resolves one test target (a directory package or a single
/// file), mirroring `fors check`'s package rules (see
/// `tests/conformance/README.md`): a directory's files are named by path
/// under it; a single file is a one-module package, named by its
/// `module` header when present, else its stem.
fn resolve_target(path: &Path) -> Vec<Diagnostic> {
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
    let out = fors_resolve::resolve(&mut interner, &inputs, root);
    out.files.into_iter().flat_map(|f| f.diagnostics).collect()
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

/// Ch08 Rule 9 says outright that a local reference outside its binding's
/// region "is unresolved, Rule 14" — so a corpus test that cites Rule 6,
/// 9 or 26 (the rule that explains *why* a name isn't visible there) for
/// exactly that shape is documented, by the chapter itself, to surface as
/// N0014, not the cited rule's own code.
fn code_matches(code: Code, chapter: u8, num: u16) -> bool {
    match (chapter, code) {
        // Round 3 (D1): Rule 25 itself says a bare pattern name that does
        // not resolve "MUST be the ordinary unresolved-name error, N0014"
        // -- the same citing-vs-firing split as rules 6, 9 and 26. Round 5
        // (D3) adds Rule 17, which likewise says outright that using a std
        // module without importing it "is the ordinary unresolved-name
        // error of Rule 14, N0014, reported at the head segment"; Rule 17
        // keeps its own code for the `use std.<unknown>;` case.
        (8, Code::N(k)) => k == num || (matches!(num, 6 | 9 | 17 | 25 | 26) && k == 14),
        // Ch04 Rule 8 states the `main`-parameter capability requirement
        // as "MUST be declared in the root module's `needs` (Rule 1)", and
        // the corpus cites either rule for that one shape: it is reported
        // once, as A0001.
        (4, Code::A(k)) => k == num || (num == 8 && k == 1),
        _ => false,
    }
}

fn corpus_targets(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(dir) else {
        return out;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        // A target is a directory (a multi-file package) or a single .fors file.
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

/// Ch04 rules this crate does not implement (need types or the
/// manifest): listed here, with why, instead of asserted against.
const PENDING_04: &[(u16, &str)] = &[
    (
        2,
        "needs types (exported requirement over the module graph's edges)",
    ),
    (3, "needs types (sealed-operation site classification)"),
    (7, "needs the manifest (per-target/per-dependency policy)"),
    (
        10,
        "needs types (comptime purity: capability/clock/RNG reachability)",
    ),
    (12, "needs types (root-capability construction sites)"),
    (13, "needs the manifest (lockfile capability pinning)"),
    (
        14,
        "needs types (root-capability construction outside `main`)",
    ),
];

/// Ch08 tests this phase does not decide: Rule 11 explicitly says
/// "because finding the member needs the type, the checker enforces
/// this clause" for cross-module *member* access (as opposed to this
/// rule's syntactic parts — `pub` on a variant field, `pub` on a
/// trait-impl method — which this crate does implement and does assert).
const PENDING_08: &[&str] = &["private_field_cross_module_rejected"];

#[test]
fn ch08_names_corpus() {
    let dir = repo_root().join("tests/conformance/08-names");
    let targets = corpus_targets(&dir);
    assert!(!targets.is_empty(), "corpus not found");
    let mut failures = Vec::new();
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        if case.rule_chapter != 8 {
            continue;
        }
        if PENDING_08.contains(&case.name.as_str()) {
            eprintln!(
                "PENDING 08.R{} ({}): needs a type (Rule 11's own carve-out to the checker)",
                case.rule_num, case.name
            );
            continue;
        }
        let diags = resolve_target(target);
        match case.expect.as_str() {
            "check-ok" => {
                if !diags.is_empty() {
                    failures.push(format!("{}: expected check-ok, got {:?}", case.name, diags.iter().map(|d| d.code.as_string()).collect::<Vec<_>>()));
                }
            }
            "check-error"
                // One root cause, one diagnostic: nothing but the cited
                // rule may fire, and it may fire only once.
                if (diags.len() != 1 || !code_matches(diags[0].code, 8, case.rule_num)) => {
                    failures.push(format!(
                        "{}: expected exactly one diagnostic N{:04} (rule 08.R{}), got {:?}",
                        case.name,
                        case.rule_num,
                        case.rule_num,
                        diags.iter().map(|d| d.code.as_string()).collect::<Vec<_>>()
                    ));
                }
            _ => {}
        }
    }
    assert!(
        failures.is_empty(),
        "ch08 corpus failures:\n{}",
        failures.join("\n")
    );
}

/// Ch09 (types) corpus, round 4: this crate has no type checker, so a
/// `T`-coded test must be resolver-CLEAN (every projection, constraint
/// entry and associated-type item resolves with no N-error: ch08 Rules
/// 16, 26, 27 defer exactly what ch09 decides), and a test whose
/// `detail` names an ch08 code (`N0026`, `N0027`) must produce exactly
/// that one diagnostic. Tests whose code is a ch01 rule are resolver-clean
/// too. The corpus counts 09-types tests by name so a stale spec list is
/// noticed here as well as in the spec's own listing.
#[test]
fn ch09_types_corpus_resolver_view() {
    let dir = repo_root().join("tests/conformance/09-types");
    let targets = corpus_targets(&dir);
    assert!(
        targets.len() >= 150,
        "09-types corpus not found or truncated: {}",
        targets.len()
    );
    let mut failures = Vec::new();
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        assert_eq!(
            case.rule_chapter, 9,
            "{}: every 09-types test cites 09.Rk",
            case.name
        );
        let detail = src
            .lines()
            .find_map(|l| l.strip_prefix("//! detail:"))
            .unwrap_or("")
            .trim()
            .to_string();
        let expected_n: Option<u16> = detail
            .strip_prefix("N")
            .and_then(|r| r.get(..4))
            .and_then(|d| d.parse().ok());
        let diags = resolve_target(target);
        let got: Vec<String> = diags.iter().map(|d| d.code.as_string()).collect();
        match (case.expect.as_str(), expected_n) {
            ("check-error", Some(n)) => {
                if diags.len() != 1 || diags[0].code != Code::N(n) {
                    failures.push(format!(
                        "{}: expected exactly one N{n:04}, got {got:?}",
                        case.name
                    ));
                }
            }
            ("check-ok", _) | ("check-error", None) => {
                if !diags.is_empty() {
                    failures.push(format!("{}: expected the resolver to be clean (the test is ch09's/ch01's), got {got:?}", case.name));
                }
            }
            (other, _) => failures.push(format!("{}: unexpected expectation {other:?}", case.name)),
        }
    }
    assert!(
        failures.is_empty(),
        "ch09 corpus (resolver view) failures:\n{}",
        failures.join("\n")
    );
}

/// Ch10's corpus, resolver view. The std surface is typed, not resolved, so
/// almost every test here is the checker's: the resolver's whole obligation
/// is to be SILENT on them, because the names they use (`Buffer`, `Vec`,
/// `Map`, the `std.*` modules, `mem.Heap` as a `main` parameter) must all
/// resolve. A test whose `detail` names an N/A code is the exception and must
/// produce exactly that one diagnostic. This test is what proves the ch10
/// handoff (prelude additions, the `mem.Heap` root type, package `std`) is
/// actually wired in, so it fails loudly if any of it is reverted.
#[test]
fn ch10_std_corpus_resolver_view() {
    let dir = repo_root().join("tests/conformance/10-std");
    let targets = corpus_targets(&dir);
    assert!(
        targets.len() >= 40,
        "10-std corpus not found or truncated: {}",
        targets.len()
    );
    let mut failures = Vec::new();
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        assert_eq!(
            case.rule_chapter, 10,
            "{}: every 10-std test cites 10.Sk",
            case.name
        );
        let detail = src
            .lines()
            .find_map(|l| l.strip_prefix("//! detail:"))
            .unwrap_or("")
            .trim()
            .to_string();
        let expected: Option<Code> = match detail.as_bytes().first() {
            Some(b'N') => detail.get(1..5).and_then(|d| d.parse().ok()).map(Code::N),
            Some(b'A') => detail.get(1..5).and_then(|d| d.parse().ok()).map(Code::A),
            _ => None,
        };
        let diags = resolve_target(target);
        let got: Vec<String> = diags.iter().map(|d| d.code.as_string()).collect();
        match expected {
            Some(code) => {
                if diags.len() != 1 || diags[0].code != code {
                    failures.push(format!(
                        "{}: expected exactly one {}, got {got:?}",
                        case.name,
                        code.as_string()
                    ));
                }
            }
            None => {
                if !diags.is_empty() {
                    failures.push(format!("{}: expected the resolver to be clean (the test is the checker's), got {got:?}", case.name));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "ch10 corpus (resolver view) failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn ch04_authority_corpus_subset() {
    let dir = repo_root().join("tests/conformance/04-authority");
    let targets = corpus_targets(&dir);
    assert!(!targets.is_empty(), "corpus not found");
    let mut failures = Vec::new();
    let mut pending: HashMap<u16, Vec<String>> = HashMap::new();
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        if case.rule_chapter != 4 {
            continue;
        }
        if PENDING_04.iter().any(|(k, _)| *k == case.rule_num) {
            pending
                .entry(case.rule_num)
                .or_default()
                .push(case.name.clone());
            continue;
        }
        let diags = resolve_target(target);
        match case.expect.as_str() {
            "check-ok" | "run-ok" => {
                if !diags.is_empty() {
                    failures.push(format!(
                        "{}: expected no diagnostics, got {:?}",
                        case.name,
                        diags.iter().map(|d| d.code.as_string()).collect::<Vec<_>>()
                    ));
                }
            }
            "check-error" if !diags.iter().any(|d| code_matches(d.code, 4, case.rule_num)) => {
                failures.push(format!(
                    "{}: expected a diagnostic A{:04} (rule 04.R{}), got {:?}",
                    case.name,
                    case.rule_num,
                    case.rule_num,
                    diags.iter().map(|d| d.code.as_string()).collect::<Vec<_>>()
                ));
            }
            _ => {}
        }
    }
    assert!(
        failures.is_empty(),
        "ch04 subset failures:\n{}",
        failures.join("\n")
    );
    // PENDING table (printed on failure/verbose run; not itself a test
    // assertion): rules 04 needs types or the manifest, out of scope for
    // this phase per the task's own boundary.
    for (rule, reason) in PENDING_04 {
        if let Some(names) = pending.get(rule) {
            eprintln!("PENDING 04.R{rule} ({reason}): {names:?}");
        }
    }
}

/// Every corpus file that is not itself a `parse-error` test must not
/// crash the resolver, whatever chapter it belongs to.
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
                walk(&p, out);
            } else if p.extension().is_some_and(|e| e == "fors") {
                out.push(p);
            }
        }
    }
    let mut files = Vec::new();
    walk(&repo_root().join("tests/conformance"), &mut files);
    for f in files {
        let src = fs::read_to_string(&f).unwrap_or_default();
        let case = parse_directives(&src);
        if case.expect == "parse-error" {
            continue;
        }
        // Resolve each file on its own (a directory-package member has
        // no directives of its own, so it is only reached via its test's
        // directory target below); this sweep is a pure no-crash check.
        let _ = resolve_target(&f);
    }
    // Directory targets too.
    fn walk_dirs(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                if p.join("main.fors").exists() {
                    out.push(p.clone());
                }
                walk_dirs(&p, out);
            }
        }
    }
    let mut dirs = Vec::new();
    walk_dirs(&repo_root().join("tests/conformance"), &mut dirs);
    for d in dirs {
        let _ = resolve_target(&d);
    }
}

/// Ch08's determinism requirement: resolving the corpus twice gives
/// byte-identical diagnostics.
#[test]
fn determinism_resolving_twice() {
    let dir = repo_root().join("tests/conformance/08-names");
    for target in corpus_targets(&dir) {
        let a = resolve_target(&target);
        let b = resolve_target(&target);
        let sa: Vec<String> = a
            .iter()
            .map(|d| format!("{}:{}:{}:{}", d.start, d.end, d.code.as_string(), d.message))
            .collect();
        let sb: Vec<String> = b
            .iter()
            .map(|d| format!("{}:{}:{}:{}", d.start, d.end, d.code.as_string(), d.message))
            .collect();
        assert_eq!(sa, sb, "non-deterministic diagnostics for {target:?}");
    }
}

/// Ch01 (ownership) corpus, resolver view — added in round 6 (owner
/// decision 2026-09-20), which put ~50 new tests in this directory for
/// linearity (Rules 22-22i) and `defer`/`errdefer` (Rules 23-23f). No type
/// checker exists, so this crate's whole obligation on a ch01 test is to be
/// SILENT: every name a `check-ok` or `check-error` test uses must resolve,
/// because ch01's codes are the checker's, not ch08's. `parse-ok`,
/// `parse-error` and `trap` tests are the parser's and the runtime's and are
/// skipped here.
#[test]
fn ch01_ownership_corpus_resolver_view() {
    let dir = repo_root().join("tests/conformance/01-ownership");
    let targets = corpus_targets(&dir);
    assert!(
        targets.len() >= 90,
        "01-ownership corpus not found or truncated: {}",
        targets.len()
    );
    let mut failures = Vec::new();
    let mut checked = 0usize;
    for target in &targets {
        let src = directive_source(target);
        let case = parse_directives(&src);
        if case.rule_chapter != 1 {
            continue;
        }
        if !matches!(case.expect.as_str(), "check-ok" | "check-error") {
            continue;
        }
        // Rounds 1-3 wrote four ch01 tests whose shape IS a name error as
        // well as an ownership one (an undeclared brand argument; an `impl`
        // of a foreign type, outside the defining module). They are ch08's
        // to move or retire, not round 6's, and are listed rather than
        // asserted so this test stays a real gate for everything else.
        const NAME_SHAPED: &[&str] = &[
            "arena_brand_nonescape_rejected",
            "brand_field_requires_param",
            "shared_blanket_impl_rejected",
            "shared_impl_outside_defining_module_rejected",
        ];
        if NAME_SHAPED.contains(&case.name.as_str()) {
            continue;
        }
        let detail = src
            .lines()
            .find_map(|l| l.strip_prefix("//! detail:"))
            .unwrap_or("")
            .trim()
            .to_string();
        // A test whose `detail` names an ch08/ch04 code is that phase's.
        let expected: Option<Code> = match detail.as_bytes().first() {
            Some(b'N') => detail.get(1..5).and_then(|d| d.parse().ok()).map(Code::N),
            Some(b'A') => detail.get(1..5).and_then(|d| d.parse().ok()).map(Code::A),
            _ => None,
        };
        checked += 1;
        let diags = resolve_target(target);
        let got: Vec<String> = diags.iter().map(|d| d.code.as_string()).collect();
        match expected {
            Some(code) => {
                if diags.len() != 1 || diags[0].code != code {
                    failures.push(format!(
                        "{}: expected exactly one {}, got {got:?}",
                        case.name,
                        code.as_string()
                    ));
                }
            }
            None => {
                if !diags.is_empty() {
                    failures.push(format!(
                        "{}: expected the resolver to be clean (the test is ch01's), got {got:?}",
                        case.name
                    ));
                }
            }
        }
    }
    assert!(
        checked >= 60,
        "expected ch01's check-* tests to be found, saw {checked}"
    );
    assert!(
        failures.is_empty(),
        "ch01 corpus (resolver view) failures:\n{}",
        failures.join("\n")
    );
}
