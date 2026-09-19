//! Never-panic guarantee: 2000 deterministic pseudo-random byte strings (a
//! plain LCG, no external crates) plus every prefix of three corpus files.

use std::fs;
use std::path::{Path, PathBuf};

/// A minimal linear congruential generator: deterministic, no dependency,
/// good enough to hammer the lexer with varied byte content.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed)
    }

    fn next_u64(&mut self) -> u64 {
        // constants from Numerical Recipes
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }

    fn next_byte(&mut self) -> u8 {
        (self.next_u64() >> 33) as u8
    }
}

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

#[test]
fn never_panics_on_random_bytes() {
    let mut rng = Lcg::new(0xF0125_D00D);
    for i in 0..2000u32 {
        // vary length from 0 to ~300 bytes, biased toward the ASCII range
        // that actually exercises lexer states, plus occasional raw bytes
        let len = (rng.next_u64() % 300) as usize;
        let mut buf = Vec::with_capacity(len);
        for _ in 0..len {
            let b = rng.next_byte();
            // ~1 in 8 bytes is fully arbitrary (including non-ASCII); the
            // rest is nudged into the printable ASCII range so we still hit
            // real lexer branches, not just the stray-byte path every time.
            if b % 8 == 0 {
                buf.push(b);
            } else {
                buf.push(0x20 + (b % 95));
            }
        }
        let (tokens, diags) = fors_lex::lex(&buf);
        // basic sanity: never panicked to get here, and the stream is
        // internally consistent
        assert_eq!(tokens.starts.len(), tokens.kinds.len() + 1);
        assert_eq!(tokens.source_len() as usize, buf.len());
        let _ = diags.len();
        if i == 0 {
            // touch the first case so this loop can't be optimized away oddly
            assert!(tokens.len() >= 1);
        }
    }
}

#[test]
fn never_panics_on_corpus_prefixes() {
    let dir = conformance_dir();
    let mut files = Vec::new();
    walk_fors_files(&dir, &mut files);
    files.sort();
    files.truncate(3);
    assert_eq!(files.len(), 3, "expected at least 3 corpus files under {:?}", dir);

    for f in &files {
        let src = fs::read(f).expect("read corpus file");
        for end in 0..=src.len() {
            let (tokens, _diags) = fors_lex::lex(&src[..end]);
            assert_eq!(tokens.source_len() as usize, end);
        }
    }
}
