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
        .flat_map(|f| f.diagnostics.iter())
        .map(|d| d.code.as_string())
        .collect();
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
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
            let (got, _) = check_target(target);
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
        let (got, _) = check_target(target);
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
                    let (_, res) = check_target(target);
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
        "ch09 checker view: {on} on, {pending} pending, {} total",
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
/// `std` now writes the destructuring form R22d(ii) prescribes. The list
/// is empty, not deleted, so a regression is caught by the count assertion
/// rather than by this comment going stale.
const STD_CONFLICTS: &[(&str, &str)] = &[];

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
        let (got, _) = check_target(&target);
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
