//! Conformance runner: walks `tests/conformance/`, reads each file's `//!
//! expect:` directive, and asserts:
//!  - `parse-error` files produce at least one diagnostic;
//!  - every other file (`parse-ok`, `check-error`, `trap`, `run-ok`, and
//!    support files without a directive) parses with zero diagnostics;
//!  - the two named error-recovery files produce exactly one diagnostic
//!    and the declaration that follows the recovered point is a proper
//!    node in the tree;
//!  - every corpus file round-trips losslessly (`reconstruct` reproduces
//!    the source byte for byte).
//!
//! Known disagreements between the corpus/spec and this parser (proven
//! from the chapter text, not bent around) are listed explicitly below and
//! skipped rather than silently passed.

use std::fs;
use std::path::{Path, PathBuf};

fn conformance_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance")
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = fs::read_dir(dir) else { return };
    let mut entries: Vec<_> = rd.filter_map(|e| e.ok()).collect();
    entries.sort_by_key(|e| e.path());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            walk(&path, out);
        } else if path.extension().map(|e| e == "fors").unwrap_or(false) {
            out.push(path);
        }
    }
}

fn expect_directive(src: &str) -> Option<String> {
    for line in src.lines().take(10) {
        if let Some(rest) = line.strip_prefix("//! expect:") {
            return Some(rest.trim().to_string());
        }
    }
    None
}

/// Files where this parser's behaviour deliberately differs from a naive
/// reading of the corpus/spec, with the chapter-07 reason. None found so
/// far: every corpus file agrees with ch07 as implemented.
const KNOWN_DISAGREEMENTS: &[&str] = &[];

#[test]
fn corpus_matches_expectations_and_round_trips() {
    let root = conformance_root();
    let mut files = Vec::new();
    walk(&root, &mut files);
    assert!(!files.is_empty(), "no .fors corpus files found under {}", root.display());

    let mut failures = Vec::new();
    let mut checked = 0usize;

    for path in &files {
        let rel = path.strip_prefix(&root).unwrap().to_string_lossy().to_string();
        if KNOWN_DISAGREEMENTS.contains(&rel.as_str()) {
            continue;
        }
        checked += 1;
        let src = fs::read(path).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        let src_str = String::from_utf8_lossy(&src).to_string();
        let expect = expect_directive(&src_str);

        let (tree, diags) = fors_syntax::parse(&src);

        match expect.as_deref() {
            Some("parse-error") => {
                if diags.is_empty() {
                    failures.push(format!("{rel}: expected parse-error, got zero diagnostics"));
                }
            }
            _ => {
                if !diags.is_empty() {
                    failures.push(format!(
                        "{rel}: expected zero diagnostics ({:?}), got {:?}",
                        expect, diags
                    ));
                }
            }
        }

        // Lossless round trip, for every corpus file regardless of
        // expectation (even a rejected file must still reproduce its
        // source: recovery never drops or invents bytes).
        let (tokens, _) = fors_lex::lex(&src);
        let rebuilt = fors_syntax::reconstruct(&tree, &tokens, &src);
        if rebuilt != src {
            failures.push(format!("{rel}: round trip mismatch ({} vs {} bytes)", rebuilt.len(), src.len()));
        }
    }

    assert!(checked >= 200, "expected the ~230-file corpus, only found {checked}");
    assert!(failures.is_empty(), "{} failing file(s):\n{}", failures.len(), failures.join("\n"));
}

#[test]
fn recover_missing_semicolon_is_exactly_one_diagnostic() {
    let path = conformance_root().join("07-grammar/recover-missing-semicolon.fors");
    let src = fs::read(&path).expect("fixture must exist");
    let (_tree, diags) = fors_syntax::parse(&src);
    assert_eq!(diags.len(), 1, "diags: {diags:?}");
    assert_eq!(diags[0].code.as_str(), "P0002");
}

#[test]
fn recover_missing_brace_is_exactly_one_diagnostic_and_resumes() {
    let path = conformance_root().join("07-grammar/recover-missing-brace.fors");
    let src = fs::read(&path).expect("fixture must exist");
    let (tree, diags) = fors_syntax::parse(&src);
    assert_eq!(diags.len(), 1, "diags: {diags:?}");
    assert_eq!(diags[0].code.as_str(), "P0003");

    // The File's direct children must still be 3 proper declarations: the
    // truncated `fn`, then `struct S {}`, then `fn g() {}`.
    let mut dump = String::new();
    let (tokens, _) = fors_lex::lex(&src);
    fors_syntax::dump_tree(&tree, &tokens, &src, &mut dump);
    let top_level_decls = dump
        .lines()
        .filter(|l| l.starts_with("  ") && !l.starts_with("   "))
        .filter(|l| l.trim_start().starts_with("FnDecl") || l.trim_start().starts_with("StructDecl"))
        .count();
    assert_eq!(top_level_decls, 3, "tree:\n{dump}");
}
