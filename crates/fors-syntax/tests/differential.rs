//! Differential test: for every corpus file, compares this parser's
//! accept/reject verdict against `tools/ref/fors_parse.py`, an independent
//! reference parser (proven to agree with all 230 corpus files) invoked
//! through `tools/ref/diff_driver.py`. Fails on any disagreement.

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

fn repo_root() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn differential_against_reference_parser() {
    let root = repo_root();
    let corpus = root.join("tests/conformance");
    let driver = root.join("tools/ref/diff_driver.py");

    let output = Command::new("python3")
        .arg(&driver)
        .arg(&corpus)
        .output()
        .expect("python3 must be on PATH to run the reference-parser differential test");
    assert!(
        output.status.success(),
        "reference driver failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);

    let mut reference: HashMap<String, bool> = HashMap::new(); // rel -> is_err
    for line in stdout.lines() {
        let Some((rel, verdict)) = line.split_once('\t') else { continue };
        reference.insert(rel.to_string(), verdict == "err");
    }
    assert!(reference.len() >= 200, "expected ~230 reference verdicts, got {}", reference.len());

    let mut disagreements = Vec::new();
    for (rel, ref_is_err) in &reference {
        let path = corpus.join(rel);
        let src = std::fs::read(&path).unwrap_or_else(|e| panic!("reading {rel}: {e}"));
        let (_tree, diags) = fors_syntax::parse(&src);
        let ours_is_err = !diags.is_empty();
        if ours_is_err != *ref_is_err {
            disagreements.push(format!("{rel}: reference={ref_is_err} rust={ours_is_err} diags={diags:?}"));
        }
    }
    disagreements.sort();
    assert!(disagreements.is_empty(), "{} disagreement(s):\n{}", disagreements.len(), disagreements.join("\n"));
}
