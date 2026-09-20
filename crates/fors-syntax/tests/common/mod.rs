#![allow(dead_code)]
//! Shared helpers for the integration tests.

use fors_syntax::{NodeKind, Parse, Tree};
use std::path::{Path, PathBuf};

pub fn corpus_files() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<_> = rd.filter_map(|e| e.ok()).collect();
        entries.sort_by_key(|e| e.path());
        for e in entries {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "fors") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    walk(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance"),
        &mut out,
    );
    assert!(out.len() >= 200, "corpus not found");
    out
}

/// Parses, checks every tree invariant and that diagnostics are in range.
pub fn parse_checked(src: &[u8]) -> Parse {
    let p = fors_syntax::parse_file(src);
    if let Err(e) = fors_syntax::validate(&p.tree, &p.tokens, src) {
        panic!(
            "invariant violated: {e}\nsource: {:?}",
            String::from_utf8_lossy(&src[..src.len().min(400)])
        );
    }
    for d in &p.diags {
        assert!(d.start < d.end, "empty diagnostic range {d:?}");
        assert!(
            d.end as usize <= src.len().max(1),
            "diagnostic {d:?} past the end ({} bytes)",
            src.len()
        );
    }
    p
}

fn sexpr(tree: &Tree, i: usize, out: &mut String) {
    out.push_str(&format!("{:?}", tree.kinds[i]));
    if !tree.is_leaf(i) {
        out.push('(');
        for (n, c) in tree.children(i).enumerate() {
            if n > 0 {
                out.push(' ');
            }
            sexpr(tree, c, out);
        }
        out.push(')');
    }
}

pub fn shape_of(tree: &Tree, i: usize) -> String {
    let mut s = String::new();
    sexpr(tree, i, &mut s);
    s
}

/// Shape of the statements of `fn t() { <body> }`, space separated.
pub fn body_shape(body: &str) -> String {
    let src = format!("fn t() {{ {body} }}");
    let p = parse_checked(src.as_bytes());
    assert!(p.diags.is_empty(), "{body:?}: {:?}", p.diags);
    let block = (0..p.tree.len())
        .find(|&i| p.tree.kinds[i] == NodeKind::Block)
        .expect("block");
    p.tree
        .children(block)
        .map(|c| shape_of(&p.tree, c))
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn file_shape(src: &str) -> String {
    let p = parse_checked(src.as_bytes());
    assert!(p.diags.is_empty(), "{src:?}: {:?}", p.diags);
    p.tree
        .children(0)
        .map(|c| shape_of(&p.tree, c))
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn codes(src: &str) -> Vec<&'static str> {
    parse_checked(src.as_bytes())
        .diags
        .iter()
        .map(|d| d.code.as_str())
        .collect()
}

pub fn body_codes(body: &str) -> Vec<&'static str> {
    codes(&format!("fn t() {{ {body} }}"))
}

pub fn accepts(body: &str) {
    assert!(
        body_codes(body).is_empty(),
        "should parse: {body:?} -> {:?}",
        body_codes(body)
    );
}

pub fn rejects(body: &str) {
    assert!(!body_codes(body).is_empty(), "should be rejected: {body:?}");
}

/// Deterministic 64-bit LCG (Knuth's MMIX constants).
pub struct Lcg(pub u64);
impl Lcg {
    pub fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    pub fn below(&mut self, n: usize) -> usize {
        (self.next() as usize) % n.max(1)
    }
}
