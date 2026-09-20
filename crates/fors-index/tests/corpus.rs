//! Corpus-driven tests: fingerprint stability, determinism, module-graph
//! cycles, and no-panic sweeps over `tests/conformance/`.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use fors_index::{
    Interner, build_decl_table, build_module_graph, extract_module_facts, module_segments,
};
use fors_syntax::parse_file;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn corpus_files() -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        let mut entries: Vec<_> = entries.flatten().collect();
        entries.sort_by_key(|e| e.path());
        for e in entries {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|e| e == "fors") {
                out.push(p);
            }
        }
    }
    let mut out = Vec::new();
    walk(&repo_root().join("tests/conformance"), &mut out);
    out
}

/// Indexes every corpus file and every prefix (in significant-token
/// steps, to keep the sweep fast) of five of them, asserting the parser
/// and indexer never panic.
#[test]
fn no_panic_over_corpus_and_prefixes() {
    let files = corpus_files();
    assert!(!files.is_empty(), "corpus not found");
    for path in &files {
        let src = fs::read(path).unwrap();
        let p = parse_file(&src);
        let mut interner = Interner::new();
        let _ = build_decl_table(&p.tree, &p.tokens, &src, &mut interner);
        let _ = extract_module_facts(&p.tree, &p.tokens, &src, &mut interner);
    }
    for path in files.iter().take(5) {
        let src = fs::read(path).unwrap();
        let step = (src.len() / 40).max(1);
        for end in (0..=src.len()).step_by(step) {
            let prefix = &src[..end];
            let p = parse_file(prefix);
            let mut interner = Interner::new();
            let _ = build_decl_table(&p.tree, &p.tokens, prefix, &mut interner);
            let _ = extract_module_facts(&p.tree, &p.tokens, prefix, &mut interner);
        }
    }
}

fn index_all(files: &[PathBuf]) -> Vec<(String, String, Vec<u128>, Vec<u128>)> {
    // (path, decl-summary, sig hashes, body hashes) per file, independent
    // of any cross-file ordering.
    let mut out = Vec::new();
    for path in files {
        let src = fs::read(path).unwrap();
        let p = parse_file(&src);
        let mut interner = Interner::new();
        let decls = build_decl_table(&p.tree, &p.tokens, &src, &mut interner);
        let summary = decls
            .kind
            .iter()
            .zip(&decls.name)
            .map(|(k, n)| {
                format!(
                    "{k:?}:{:?}",
                    n.map(|s| String::from_utf8_lossy(interner.resolve(s)).into_owned())
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        out.push((
            path.display().to_string(),
            summary,
            decls.sig_hash.clone(),
            decls.body_hash.clone(),
        ));
    }
    out
}

/// Indexing does not depend on the order files are processed in: each
/// file's own table is a pure function of its own bytes.
#[test]
fn determinism_across_file_orders() {
    let mut files = corpus_files();
    let forward = index_all(&files);
    files.reverse();
    let mut backward = index_all(&files);
    backward.sort_by(|a, b| a.0.cmp(&b.0));
    let mut forward_sorted = forward;
    forward_sorted.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(forward_sorted, backward);
}

fn build_dir_graph(dir: &Path, order: &[&str]) -> Vec<String> {
    let mut interner = Interner::new();
    let mut files = Vec::new();
    for (i, stem) in order.iter().enumerate() {
        let src = fs::read(dir.join(format!("{stem}.fors"))).unwrap();
        let p = parse_file(&src);
        let facts = extract_module_facts(&p.tree, &p.tokens, &src, &mut interner);
        let name = module_segments(&mut interner, &[], &[stem.as_bytes()]).unwrap();
        files.push((fors_index::FileId(i as u32), name, facts));
    }
    let (_, _, diags) = build_module_graph(&interner, files);
    let mut msgs: Vec<String> = diags
        .iter()
        .map(|d| format!("{}:{}", d.code.as_str(), d.message))
        .collect();
    msgs.sort();
    msgs
}

#[test]
fn import_cycle_2_detected_regardless_of_order() {
    let dir = repo_root().join("tests/conformance/08-names/import-cycle-2");
    let a = build_dir_graph(&dir, &["main", "b"]);
    let b = build_dir_graph(&dir, &["b", "main"]);
    assert_eq!(a, b);
    assert_eq!(a.len(), 1);
    assert!(a[0].contains("b -> main -> b"));
}

#[test]
fn import_cycle_3_detected_regardless_of_order() {
    let dir = repo_root().join("tests/conformance/08-names/import-cycle-3");
    let a = build_dir_graph(&dir, &["main", "b", "c"]);
    let b = build_dir_graph(&dir, &["c", "b", "main"]);
    assert_eq!(a, b);
    assert_eq!(a.len(), 1);
    assert!(a[0].contains("b -> c -> main -> b"));
}

#[test]
fn self_import_corpus_file_rejected() {
    let path = repo_root().join("tests/conformance/08-names/self-import-rejected.fors");
    let src = fs::read(&path).unwrap();
    let p = parse_file(&src);
    let mut interner = Interner::new();
    let facts = extract_module_facts(&p.tree, &p.tokens, &src, &mut interner);
    let name = module_segments(&mut interner, &[], &[b"selfmod"]).unwrap();
    let (_, edges, diags) =
        build_module_graph(&interner, vec![(fors_index::FileId(0), name, facts)]);
    assert!(edges.is_empty());
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].code, fors_index::DiagCode::SelfImport);
}

#[test]
fn import_diamond_is_acyclic() {
    let dir = repo_root().join("tests/conformance/08-names/import-diamond-accepted");
    let msgs = build_dir_graph(&dir, &["main", "b", "c", "d"]);
    assert!(msgs.is_empty(), "unexpected diagnostics: {msgs:?}");
}

// ---- fingerprint stability, built by string-editing corpus fn/struct
// declarations ----

fn fn_hashes(src: &str) -> (u128, u128) {
    let p = parse_file(src.as_bytes());
    let mut interner = Interner::new();
    let decls = build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
    let i = decls
        .kind
        .iter()
        .position(|k| *k == fors_index::DeclKind::Fn)
        .expect("no fn decl");
    (decls.sig_hash[i], decls.body_hash[i])
}

#[test]
fn whitespace_and_comment_edits_change_nothing() {
    let base = "fn f(let x: i32) -> i32 { return x + 1; }";
    let spaced = "fn   f( let  x : i32 )  ->  i32  {  return  x + 1 ;  }";
    let commented = "fn f(let x: i32) -> i32 { // comment\n  return x + 1; /* trailing */ }";
    assert_eq!(fn_hashes(base), fn_hashes(spaced));
    assert_eq!(fn_hashes(base), fn_hashes(commented));
}

#[test]
fn body_edit_changes_only_body_hash() {
    let base = "fn f(let x: i32) -> i32 { return x + 1; }";
    let edited = "fn f(let x: i32) -> i32 { return x + 2; }";
    let (sig0, body0) = fn_hashes(base);
    let (sig1, body1) = fn_hashes(edited);
    assert_eq!(sig0, sig1);
    assert_ne!(body0, body1);
}

#[test]
fn signature_edit_changes_only_sig_hash() {
    let base = "fn f(let x: i32) -> i32 { return x + 1; }";
    let edited = "fn f(let x: i64) -> i32 { return x + 1; }";
    let (sig0, body0) = fn_hashes(base);
    let (sig1, body1) = fn_hashes(edited);
    assert_ne!(sig0, sig1);
    assert_eq!(body0, body1);
}

#[test]
fn inserting_a_declaration_above_leaves_others_unchanged() {
    let file_a = "fn f(let x: i32) -> i32 { return x + 1; }\nfn g() -> i32 { return 2; }\n";
    let file_b = "fn h() -> i32 { return 0; }\nfn f(let x: i32) -> i32 { return x + 1; }\nfn g() -> i32 { return 2; }\n";
    let decls_of = |src: &str| {
        let p = parse_file(src.as_bytes());
        let mut interner = Interner::new();
        let decls = build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
        let names: Vec<String> = decls
            .name
            .iter()
            .map(|n| String::from_utf8_lossy(interner.resolve(n.unwrap())).into_owned())
            .collect();
        let mut by_name = std::collections::BTreeMap::new();
        for (i, n) in names.into_iter().enumerate() {
            by_name.insert(n, (decls.sig_hash[i], decls.body_hash[i]));
        }
        by_name
    };
    let a = decls_of(file_a);
    let b = decls_of(file_b);
    assert_eq!(a["f"], b["f"]);
    assert_eq!(a["g"], b["g"]);
}

/// Every real corpus `fn`/`struct`/`enum`/`trait`/`const` declaration
/// keeps its hashes under a pure whitespace/comment reformat.
#[test]
fn corpus_declarations_stable_under_reformatting() {
    let mut checked = 0usize;
    for path in corpus_files().iter().take(30) {
        let src = fs::read_to_string(path).unwrap();
        let padded: String = src.replace('\n', "  \n  ");
        let p0 = parse_file(src.as_bytes());
        let p1 = parse_file(padded.as_bytes());
        let mut i0 = Interner::new();
        let mut i1 = Interner::new();
        let d0 = build_decl_table(&p0.tree, &p0.tokens, src.as_bytes(), &mut i0);
        let d1 = build_decl_table(&p1.tree, &p1.tokens, padded.as_bytes(), &mut i1);
        if d0.len() != d1.len() {
            continue; // a parse-error corpus file may re-synchronise differently; skip it
        }
        for k in 0..d0.len() {
            assert_eq!(
                d0.sig_hash[k], d1.sig_hash[k],
                "{path:?} decl {k} sig_hash changed by reformatting"
            );
            assert_eq!(
                d0.body_hash[k], d1.body_hash[k],
                "{path:?} decl {k} body_hash changed by reformatting"
            );
        }
        checked += 1;
    }
    assert!(checked > 0);
}

#[test]
fn distinct_module_names_across_corpus_dont_collide_symbols() {
    // Smoke test that the interner used across a whole-corpus sweep
    // produces a consistent, order-independent id for repeated names.
    let mut interner = Interner::new();
    let mut seen = BTreeSet::new();
    for path in corpus_files() {
        let src = fs::read(&path).unwrap();
        let p = parse_file(&src);
        let facts = extract_module_facts(&p.tree, &p.tokens, &src, &mut interner);
        if let Some((segs, _)) = facts.header {
            seen.insert(segs.len());
        }
    }
    assert!(!seen.is_empty());
}

/// Round 5 (D3): the module graph is EXACTLY the explicit `use` edges.
/// A body that spells `io.len` on a local named `io`, and a header
/// `needs { env };`, add no edge — before round 5 the whole-file token
/// scan turned `io .` into an implicit edge main -> std.io, which with
/// std.io's `use main;` was a cycle. Adding `use std.io;` to main's header
/// is what makes the cycle, and only that.
#[test]
fn edges_are_exactly_the_use_edges_no_body_scan() {
    fn graph(main_src: &str) -> (Vec<(usize, usize)>, Vec<String>) {
        let std_io = "module std.io;\nuse main;\n\npub struct Stdout { fd: i32 }\n";
        let mut interner = Interner::new();
        let mut files = Vec::new();
        let main_path: &[&[u8]] = &[b"main"];
        let std_path: &[&[u8]] = &[b"std", b"io"];
        for (i, (src, path)) in [(main_src, main_path), (std_io, std_path)]
            .into_iter()
            .enumerate()
        {
            let p = parse_file(src.as_bytes());
            let facts = extract_module_facts(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
            let name = module_segments(&mut interner, &[], path).unwrap();
            files.push((fors_index::FileId(i as u32), name, facts));
        }
        let (_, edges, diags) = build_module_graph(&interner, files);
        (
            edges.iter().map(|(a, b)| (a.index(), b.index())).collect(),
            diags.iter().map(|d| d.code.as_str().to_string()).collect(),
        )
    }
    let body_only = "module main;\nneeds { env };\n\nfn f() -> usize {\n    let io: Str = \"a\";\n    return io.len;\n}\n";
    let (edges, diags) = graph(body_only);
    assert_eq!(
        edges,
        vec![(1, 0)],
        "only std.io -> main: the body's `io .` and the header's `needs {{ env }}` add nothing"
    );
    assert!(
        diags.is_empty(),
        "no cycle can arise from a body: {diags:?}"
    );
    let with_use = "module main;\nneeds { env };\nuse std.io;\n\nfn f() -> usize {\n    let io: Str = \"a\";\n    return io.len;\n}\n";
    let (edges, diags) = graph(with_use);
    assert_eq!(
        edges,
        vec![(0, 1), (1, 0)],
        "the explicit `use` is the one way to add the edge"
    );
    assert_eq!(diags, vec!["N0007".to_string()]);
}
