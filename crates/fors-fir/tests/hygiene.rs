//! CI hygiene test (`docs/design/type-checker.md` §4.1, §12, increment
//! I0's gate): `fors-fir` depends on `fors-index` only. Depending on
//! `fors-index` already links `fors-lex`/`fors-syntax` transitively
//! (design §1 point 7), which is a dependency-*direction* concern, not a
//! ch05 Rule 2 violation (R2 forbids re-*parsing* imported source, not
//! linking the parser) — so the guard that actually matters is textual:
//! nothing under `src/` ever spells `fors_syntax` or `fors_lex`, which
//! would mean this crate started reading tokens or trees directly instead
//! of treating `fors-index`'s already-built tables as its only input.

use std::fs;
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
}

fn walk_rs(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            walk_rs(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn fors_fir_src_mentions_neither_fors_syntax_nor_fors_lex() {
    let src_dir = repo_root().join("crates/fors-fir/src");
    let mut files = Vec::new();
    walk_rs(&src_dir, &mut files);
    assert!(!files.is_empty(), "fors-fir/src has no .rs files to check");
    for path in &files {
        let text = fs::read_to_string(path).unwrap();
        assert!(!text.contains("fors_syntax"), "{} mentions fors_syntax", path.display());
        assert!(!text.contains("fors_lex"), "{} mentions fors_lex", path.display());
    }
}
