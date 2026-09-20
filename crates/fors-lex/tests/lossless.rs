//! Losslessness over the whole conformance corpus (ch07 "The grammar is
//! parseable per file ... to a lossless CST").

use std::fs;
use std::path::{Path, PathBuf};

fn conformance_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance")
}

fn walk_fors_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_fors_files(&path, out);
        } else if path.extension().map(|e| e == "fors").unwrap_or(false) {
            out.push(path);
        }
    }
}

fn check_lossless(src: &[u8], label: &str) {
    let (tokens, _diags) = fors_lex::lex(src);
    let mut rebuilt = Vec::with_capacity(src.len());
    for i in 0..tokens.len() {
        rebuilt.extend_from_slice(tokens.text(i, src));
    }
    assert_eq!(
        rebuilt, src,
        "concatenating token slices did not reproduce the source: {label}"
    );
    // starts must be non-decreasing and end exactly at the source length
    for w in tokens.starts.windows(2) {
        assert!(w[0] <= w[1], "token starts went backwards in {label}");
    }
    assert_eq!(
        tokens.source_len() as usize,
        src.len(),
        "sentinel mismatch in {label}"
    );
}

#[test]
fn lossless_over_conformance_corpus() {
    let dir = conformance_dir();
    let mut files = Vec::new();
    walk_fors_files(&dir, &mut files);
    assert!(
        files.len() >= 200,
        "expected the full conformance corpus under {:?}, found {} files",
        dir,
        files.len()
    );

    for f in &files {
        let src = fs::read(f).expect("read corpus file");
        check_lossless(&src, &f.display().to_string());
    }
    eprintln!("lossless: checked {} corpus files", files.len());
}

#[test]
fn lossless_on_empty_input() {
    check_lossless(b"", "<empty>");
}
