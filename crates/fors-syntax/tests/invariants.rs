//! Tree invariants (`fors_syntax::validate`: every token owned by exactly
//! one node, pre-order ranges nest, `Error` nodes never swallow a
//! declaration start, lossless) over the whole corpus and over mutated
//! corpus files: a deterministic LCG deletes, duplicates, swaps and
//! replaces tokens, and corrupts raw bytes. Nothing may panic, hang or
//! break an invariant; stack use is checked on a deliberately small stack.

mod common;
use common::*;

#[test]
fn corpus_trees_are_valid() {
    for path in corpus_files() {
        let src = std::fs::read(&path).unwrap();
        parse_checked(&src);
    }
}

const VOCAB: &[&str] = &[
    "+", "-", "*", "&", "|", "^", "<<", "..<", "==", "<", "and", "or", "not", "as", "move", "?",
    ".", ",", ";", ":", "(", ")", "[", "]", "{", "}", "=", "+=", "->", "=>", "@", "_", "x", "1",
    "1.5", "\"s\"", ".v", "if", "else", "match", "let", "fn", "struct", "pub", "impl", "use",
    "set", "out", "scoped", "soa", "iso", "dyn", "type", "spmd", "kernel", "self", "trait",
    "\\\\ml\n", "/*", "\"", "0x", "1e", "..", "é", "$",
];

#[test]
fn mutated_corpus_never_breaks_an_invariant() {
    let files: Vec<Vec<u8>> = corpus_files()
        .iter()
        .map(|p| std::fs::read(p).unwrap())
        .collect();
    let mut rng = Lcg(0x5EED_F025);
    let mut cases = 0;
    for round in 0..6000 {
        let src = &files[rng.below(files.len())];
        let (tokens, _) = fors_lex::lex(src);
        let mut pieces: Vec<Vec<u8>> = (0..tokens.len())
            .map(|i| tokens.text(i, src).to_vec())
            .collect();
        for _ in 0..1 + rng.below(3) {
            let (i, j) = (rng.below(pieces.len()), rng.below(pieces.len()));
            match rng.below(4) {
                0 => pieces[i].clear(),
                1 => {
                    let dup = pieces[i].clone();
                    pieces[i].extend_from_slice(b" ");
                    pieces[i].extend_from_slice(&dup);
                }
                2 => pieces.swap(i, j),
                _ => pieces[i] = VOCAB[rng.below(VOCAB.len())].as_bytes().to_vec(),
            }
        }
        let mut mutated = pieces.concat();
        if round % 4 == 0 && !mutated.is_empty() {
            let at = rng.below(mutated.len());
            mutated[at] = rng.next() as u8; // raw byte corruption, often invalid UTF-8
        }
        parse_checked(&mutated);
        cases += 1;
    }
    assert!(cases >= 5000);
}

#[test]
fn every_prefix_of_every_tenth_corpus_file() {
    for path in corpus_files().iter().step_by(10) {
        let src = std::fs::read(path).unwrap();
        for len in 0..=src.len() {
            parse_checked(&src[..len]);
        }
    }
}

/// Every recursive production, nested far past `MAX_DEPTH`, on a 256 KiB
/// stack in a debug build: the depth limit, not the stack, must stop it.
#[test]
fn deep_nesting_is_bounded_on_a_small_stack() {
    let n = 100_000;
    let opens: Vec<(&str, &str)> = vec![
        ("(", ""),
        ("[", ""),
        ("{", ""),
        ("f(", ""),
        ("a[", ""),
        ("P { x: ", ""),
        ("- ", ""),
        ("not ", ""),
        ("& ", ""),
        ("move ", ""),
        ("|a| ", ""),
        ("if x { ", ""),
        ("if x { } else ", ""),
        ("match x { _ => ", ""),
        ("comptime { ", ""),
        ("x.y(|| { ", ""),
        ("a + (", ""),
        ("let x: (", ""),
        ("let x: A[", ""),
        ("let x: fn() -> ", ""),
        ("let x: A[-(", ""),
        ("let (", ""),
        ("match x { (", ""),
        ("match x { .a(", ""),
        ("match x { p { f: ", ""),
        ("while x { for i in y { ", ""),
        ("(", ")"),
        ("f(", ")"),
        ("{", "}"),
        ("[", "]"),
        ("if x { ", " }"),
        ("a.b(", ")?"),
    ];
    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for (open, close) in opens {
        inputs.push(format!("fn t() {{ {}1{} }}", open.repeat(n), close.repeat(n)).into_bytes());
    }
    for decl in [
        "fn f() -> (",
        "fn f(let x: (",
        "struct S[T: A[",
        "impl A[(",
        "const X: A[",
        "enum E { V((",
    ] {
        inputs.push(
            decl.to_string()
                .into_bytes()
                .into_iter()
                .chain("(".repeat(n).into_bytes())
                .collect(),
        );
    }
    inputs.push(format!("fn t() {{ x{}; }}", ".y()".repeat(n)).into_bytes());
    inputs.push(format!("fn t() {{ x{}; }}", "[0]".repeat(n)).into_bytes());
    inputs.push(format!("fn t() {{ x{}; }}", "?".repeat(n)).into_bytes());
    inputs.push(format!("fn t() {{ let v = 1{}; }}", " + 1".repeat(n)).into_bytes());
    inputs.push(format!("fn t() {{ if a {{ }}{} }}", " else if a { }".repeat(n)).into_bytes());
    inputs.push("@a ".repeat(n).into_bytes());
    inputs.push("@a(".repeat(n).into_bytes());
    inputs.push("fn f() { @a ".repeat(n).into_bytes());

    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            for src in &inputs {
                let p = parse_checked(src);
                // later phases recurse over the tree: its depth is bounded too
                let mut depth = 0usize;
                let mut max = 0usize;
                let mut ends: Vec<usize> = Vec::new();
                for i in 0..p.tree.len() {
                    while ends.last().is_some_and(|&e| e <= i) {
                        ends.pop();
                        depth -= 1;
                    }
                    ends.push(p.tree.subtree_end(i));
                    depth += 1;
                    max = max.max(depth);
                }
                assert!(
                    max < 2048,
                    "tree depth {max} for {:?}",
                    String::from_utf8_lossy(&src[..40])
                );
            }
        });
    worker
        .unwrap()
        .join()
        .expect("parser overflowed a 256 KiB stack or broke an invariant");
}

#[test]
fn long_flat_input_is_linear() {
    // 200k statements / a 200k-operand chain: quadratic behaviour would time out
    let src = format!(
        "fn t() {{ {} }}",
        "a.b[c].d = e(1) + f * g;".repeat(200_000)
    );
    assert!(parse_checked(src.as_bytes()).diags.is_empty());
    let src = format!("fn t() {{ f({}); }}", "x, ".repeat(300_000));
    assert!(parse_checked(src.as_bytes()).diags.is_empty());
}

#[test]
fn edge_inputs() {
    for src in [
        &b""[..],
        b"\xEF\xBB\xBF",
        b"\xFF\xFE\x00\x80\xC0",
        b"// \xFF\n",
        b"fn f() { \"\xC3\x28\" }",
        b"\"unterminated",
        b"/* /* nested",
        b"\\\\",
        b"\\",
        b"1..",
        b"1__0",
        b".5",
        b"fn f(",
        b"struct",
        b"@",
        b"&out",
        b"pub",
        b"pub pub",
        b"soa",
        b"soa struct",
        b"extern",
        b"extern \"c\"",
        b"}",
        b")",
        b"fn f() { } }",
        b"impl",
        b"impl {",
        b"trait T { pub",
        b"fn f() { with",
        b"fn f() { parallel for",
        b"fn f() { x = ",
        b"fn f() { match x { a",
        b"fn f() -> scoped(",
        b"module",
        b"contracts",
        b"contracts:",
        b"needs",
        b"needs {",
        b"use",
        b"use a,",
        b"const",
        b"enum E {",
        b"\0\0\0",
    ] {
        parse_checked(src);
    }
    // invalid UTF-8 is diagnosed at the lexer boundary even inside a comment or string
    assert_eq!(codes_of(b"// \xFF\nfn f() { }"), ["P0008"]);
    assert_eq!(codes_of(b"fn f() { let s = \"\xC3\x28\"; }"), ["P0008"]);
    assert_eq!(
        codes_of("fn f() { let s = \"é\"; } // ü".as_bytes()),
        [""; 0]
    );
    assert_eq!(codes_of("fn f() { let x = é 1; }".as_bytes()), ["P0008"]);
}

fn codes_of(src: &[u8]) -> Vec<&'static str> {
    parse_checked(src)
        .diags
        .iter()
        .map(|d| d.code.as_str())
        .collect()
}
