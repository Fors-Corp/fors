//! No-panic test: the lexer and parser must never panic, on anything.
//! Covers 2000 deterministic pseudo-random inputs built from real token
//! spellings ("token soup" — syntactically arbitrary, but built from the
//! actual lexical vocabulary so it exercises the parser rather than
//! bottoming out at the lexer), plus every byte-prefix of five corpus
//! files (including mid-token, mid-string and mid-comment cuts, and the
//! empty prefix) and a handful of raw-byte edge cases (invalid UTF-8,
//! deep nesting, an empty file).

use std::path::Path;

/// A small xorshift PRNG: no external crate, fully deterministic across
/// platforms and Rust versions given the same seed.
struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[(self.next_u64() as usize) % xs.len()]
    }
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

const TOKENS: &[&str] = &[
    "module", "use", "pub", "fn", "struct", "enum", "trait", "impl", "const", "extern", "let", "var", "inout",
    "sink", "if", "else", "match", "for", "in", "while", "break", "continue", "return", "raise", "raises",
    "with", "parallel", "simd", "spawn", "comptime", "move", "consume", "discard", "as", "and", "or", "not",
    "true", "false", "iso", "imm", "secret", "dyn", "type", "spmd", "kernel", "import", "recover", "_", "identifier",
    "self", "self)", "self,", "set", "out", "arena", "grain",
    "pre", "post", "invariant", "scoped", "soa", "contracts", "needs", "brand",
    "(", ")", "[", "]", "{", "}", ",", ";", ":", ".", "@", "?", "->", "=>", "=", "==", "!=", "<", ">", "<=",
    ">=", "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", "..<", "..=", "+=", "-=", "*=", "/=", "%=", "&=",
    "|=", "^=", "<<=", ">>=", "1", "1.5", "0xFF", "\"s\"", "\\\\line", "\n", " ", "//c\n", "/*c*/",
];

fn gen_soup(rng: &mut Rng, n_tokens: usize) -> String {
    let mut s = String::new();
    for i in 0..n_tokens {
        if i > 0 {
            s.push(' ');
        }
        s.push_str(rng.pick(TOKENS));
    }
    s
}

fn assert_no_panic(src: &[u8]) {
    let p = fors_syntax::parse_file(src);
    if let Err(e) = fors_syntax::validate(&p.tree, &p.tokens, src) {
        panic!("invariant violated: {e}");
    }
}

#[test]
fn no_panic_token_soup() {
    let mut rng = Rng(0x9E3779B97F4A7C15);
    for _ in 0..2000 {
        let n = rng.range(0, 60);
        let src = gen_soup(&mut rng, n);
        assert_no_panic(src.as_bytes());
    }
}

#[test]
fn no_panic_corpus_prefixes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/conformance");
    let mut picked: Vec<std::path::PathBuf> = Vec::new();
    fn walk(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(rd) = std::fs::read_dir(dir) else { return };
        let mut entries: Vec<_> = rd.filter_map(|e| e.ok()).collect();
        entries.sort_by_key(|e| e.path());
        for e in entries {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().map(|x| x == "fors").unwrap_or(false) {
                out.push(p);
            }
        }
    }
    walk(&root, &mut picked);
    picked.truncate(5);
    assert_eq!(picked.len(), 5, "expected at least 5 corpus files");

    for path in &picked {
        let src = std::fs::read(path).unwrap();
        for len in 0..=src.len() {
            assert_no_panic(&src[..len]);
        }
    }
}

#[test]
fn no_panic_raw_byte_edge_cases() {
    assert_no_panic(b"");
    assert_no_panic(&[0xFF, 0xFE, 0x00, 0x80, 0xC0]); // invalid UTF-8
    assert_no_panic(b"\"unterminated string");
    assert_no_panic(b"/* unterminated comment");
    assert_no_panic(b"/* /* /* nested unterminated");
    assert_no_panic(&b"(".repeat(5000));
    assert_no_panic(&b"[".repeat(5000));
    assert_no_panic(&b"if x {".repeat(2000));
    assert_no_panic(&"a".repeat(200).into_bytes());
    assert_no_panic(b"1..");
    assert_no_panic(b"1__0");
    assert_no_panic(b".5");
    assert_no_panic(b"fn f(");
    assert_no_panic(b"struct");
    assert_no_panic(b"@");
    assert_no_panic(b"&out");
}
