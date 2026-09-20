//! T3, THE ARBITER (owner policy R14: a suggested fix is a guess and the
//! compiler is the arbiter).
//!
//! For every fix the compiler offers anywhere in the conformance corpus and
//! in `std`: copy the entry — file names and directory layout intact,
//! because a module's name comes from its file's location — apply the fix,
//! and ask the compiler again.
//!
//! A `machine-applicable` fix must remove its own diagnostic and add no
//! error. A `maybe-incorrect` fix is allowed to be wrong about intent, but
//! never about syntax: it must introduce no parser diagnostic that was not
//! already there. A kind that cannot meet its bar is repaired or demoted in
//! `fors_diag::policy` — never exempted here.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use fors_lsp::json::{Json, parse};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("the repository root is two levels above this crate")
}

fn corpus_entries() -> Vec<String> {
    let root = repo_root();
    let mut out = Vec::new();
    let mut chapters: Vec<PathBuf> = std::fs::read_dir(root.join("tests/conformance"))
        .expect("the conformance corpus is present")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    chapters.sort();
    for ch in chapters {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(&ch)
            .expect("a chapter directory is readable")
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_none_or(|e| e != "md"))
            .collect();
        entries.sort();
        for e in entries {
            out.push(
                e.strip_prefix(&root)
                    .unwrap_or(&e)
                    .to_string_lossy()
                    .into_owned(),
            );
        }
    }
    out.push("std".to_string());
    out
}

fn check_json(args: &[&str]) -> Vec<Rec> {
    let mut full = vec!["check", "--format", "json"];
    full.extend_from_slice(args);
    let out = Command::new(env!("CARGO_BIN_EXE_fors"))
        .current_dir(repo_root())
        .args(&full)
        .output()
        .expect("the `fors` binary runs");
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let mut recs = Vec::new();
    for line in text.lines() {
        let v = parse(line.as_bytes()).unwrap_or_else(|| panic!("not JSON: {line}"));
        if v.get("kind").and_then(Json::as_str) != Some("diagnostic") {
            continue;
        }
        recs.push(Rec::from(&v));
    }
    recs
}

#[derive(Clone, Debug)]
struct Rec {
    path: String,
    code: String,
    start: u32,
    fixes: Vec<FixRec>,
}

#[derive(Clone, Debug)]
struct FixRec {
    kind: String,
    applicability: String,
    edits: Vec<fors_diag::Edit>,
}

fn start_byte(v: &Json) -> u32 {
    v.get("range")
        .and_then(|r| r.get("start"))
        .and_then(|s| s.get("byte"))
        .and_then(Json::as_u32)
        .expect("every range has a start byte")
}

impl Rec {
    fn from(v: &Json) -> Rec {
        let fixes = v
            .get("fixes")
            .and_then(Json::as_arr)
            .unwrap_or(&[])
            .iter()
            .map(|f| FixRec {
                kind: f
                    .get("kind")
                    .and_then(Json::as_str)
                    .expect("a fix has a kind")
                    .to_string(),
                applicability: f
                    .get("applicability")
                    .and_then(Json::as_str)
                    .expect("a fix has an applicability")
                    .to_string(),
                edits: f
                    .get("edits")
                    .and_then(Json::as_arr)
                    .unwrap_or(&[])
                    .iter()
                    .map(|e| {
                        let r = e.get("range").expect("an edit has a range");
                        fors_diag::Edit::new(
                            r.get("start")
                                .and_then(|s| s.get("byte"))
                                .and_then(Json::as_u32)
                                .expect("start byte"),
                            r.get("end")
                                .and_then(|s| s.get("byte"))
                                .and_then(Json::as_u32)
                                .expect("end byte"),
                            e.get("replacement")
                                .and_then(Json::as_str)
                                .expect("replacement")
                                .to_string(),
                        )
                    })
                    .collect(),
            })
            .collect();
        Rec {
            path: v
                .get("path")
                .and_then(Json::as_str)
                .expect("a diagnostic has a path")
                .to_string(),
            code: v
                .get("code")
                .and_then(Json::as_str)
                .expect("a diagnostic has a code")
                .to_string(),
            start: start_byte(v),
            fixes,
        }
    }
}

/// Where `byte` moves to once `edits` have been applied to the same file.
fn shift(byte: u32, edits: &[fors_diag::Edit]) -> u32 {
    let mut delta: i64 = 0;
    for e in edits {
        if byte >= e.end {
            delta += e.replacement.len() as i64 - i64::from(e.end - e.start);
        }
    }
    u32::try_from(i64::from(byte) + delta).unwrap_or(byte)
}

fn copy_tree(from: &Path, to: &Path) {
    if from.is_file() {
        if let Some(p) = to.parent() {
            std::fs::create_dir_all(p).expect("create the copy's parent");
        }
        std::fs::copy(from, to).expect("copy a file");
        return;
    }
    std::fs::create_dir_all(to).expect("create the copy's directory");
    for e in std::fs::read_dir(from).expect("read a directory").flatten() {
        copy_tree(&e.path(), &to.join(e.file_name()));
    }
}

fn p_codes(recs: &[Rec]) -> BTreeMap<String, usize> {
    let mut m = BTreeMap::new();
    for r in recs {
        if r.code.starts_with('P') {
            *m.entry(r.code.clone()).or_insert(0) += 1;
        }
    }
    m
}

#[test]
fn every_fix_survives_the_compiler() {
    let root = repo_root();
    let entries = corpus_entries();

    // One pass over the whole corpus, then one run per fix.
    let mut before: BTreeMap<String, Vec<Rec>> = BTreeMap::new();
    for chunk in entries.chunks(150) {
        let refs: Vec<&str> = chunk.iter().map(String::as_str).collect();
        for r in check_json(&refs) {
            let entry = chunk
                .iter()
                .find(|e| r.path == **e || r.path.starts_with(&format!("{e}/")))
                .unwrap_or_else(|| panic!("`{}` belongs to no entry", r.path))
                .clone();
            before.entry(entry).or_default().push(r);
        }
    }

    let scratch = root.join("target/tmp/fix-arbiter");
    if scratch.exists() {
        std::fs::remove_dir_all(&scratch).expect("clear the previous run's copies");
    }
    std::fs::create_dir_all(&scratch).expect("create the arbiter's scratch directory");

    let mut exercised: BTreeMap<String, usize> = BTreeMap::new();
    let mut case = 0usize;

    for (entry, recs) in &before {
        if recs.iter().all(|r| r.fixes.is_empty()) {
            continue;
        }
        let entry_path = root.join(entry);
        let leaf = Path::new(entry)
            .file_name()
            .expect("an entry has a name")
            .to_owned();

        for rec in recs {
            for fix in &rec.fixes {
                case += 1;
                *exercised.entry(fix.kind.clone()).or_insert(0) += 1;

                let dir = scratch.join(format!("case{case:04}"));
                let target = dir.join(&leaf);
                copy_tree(&entry_path, &target);

                // The file the edit applies to, inside the copy.
                let rel = rec
                    .path
                    .strip_prefix(entry)
                    .map(|s| s.trim_start_matches('/'))
                    .unwrap_or("");
                let edited = if rel.is_empty() {
                    target.clone()
                } else {
                    target.join(rel)
                };
                let source = std::fs::read(&edited).expect("read the copied file");
                let patched = fors_diag::apply_edits(&source, &fix.edits).unwrap_or_else(|| {
                    panic!(
                        "fix `{}` on {} does not apply to its own file",
                        fix.kind, rec.path
                    )
                });
                std::fs::write(&edited, &patched).expect("write the patched file");

                let run_target = target.to_string_lossy().into_owned();
                let after = check_json(&[&run_target]);
                let edited_after = edited.to_string_lossy().into_owned();
                let moved = shift(rec.start, &fix.edits);
                let survived = after
                    .iter()
                    .any(|r| r.path == edited_after && r.code == rec.code && r.start == moved);

                match fix.applicability.as_str() {
                    "machine-applicable" => {
                        assert!(
                            !survived,
                            "machine-applicable `{}` left {} at byte {} of {} in place",
                            fix.kind, rec.code, moved, rec.path
                        );
                        assert!(
                            after.len() < recs.len(),
                            "machine-applicable `{}` on {} did not lower the error count ({} -> {}): \
                             it traded its error for another",
                            fix.kind,
                            rec.path,
                            recs.len(),
                            after.len()
                        );
                    }
                    "maybe-incorrect" | "has-placeholders" => {
                        let (was, now) = (p_codes(recs), p_codes(&after));
                        for (code, n) in &now {
                            assert!(
                                was.get(code).copied().unwrap_or(0) >= *n,
                                "`{}` on {} introduced {code} ({} -> {n})",
                                fix.kind,
                                rec.path,
                                was.get(code).copied().unwrap_or(0)
                            );
                        }
                    }
                    other => panic!("unknown applicability `{other}`"),
                }
            }
        }
    }

    // The report the owner reads: how much evidence each kind actually has.
    let mut report = String::from("fix kinds exercised by the corpus:\n");
    for (kind, n) in &exercised {
        report.push_str(&format!("  {kind:<30} {n}\n"));
    }
    eprintln!("{report}");

    for kind in fors_diag::FixKind::ALL {
        assert!(
            exercised.get(kind.as_str()).copied().unwrap_or(0) > 0,
            "no corpus site exercises `{}` — it is untested, so it may not ship",
            kind.as_str()
        );
    }
    // 28 today. It was 47 while `suggest` still offered one one-letter name
    // for another (`x` -> `f`, 19 sites, none of them right).
    assert!(case >= 25, "only {case} fixes in the whole corpus");
}
