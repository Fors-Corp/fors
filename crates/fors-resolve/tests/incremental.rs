//! Properties the per-declaration query engine will rely on: fingerprint
//! locality, export-table isolation between modules, diagnostic
//! attribution and root-cause counting, and no panic on mutated input.

use std::fs;
use std::path::{Path, PathBuf};

use fors_index::{Interner, Segments, build_decl_table};
use fors_resolve::{Code, Entity, FileInput, ResolveOutput, ResolvedTarget};
use fors_syntax::parse_file;

/// Resolves an in-memory package: `(dotted module name, source)` pairs.
fn resolve_pkg(files: &[(&str, &str)]) -> (ResolveOutput, Interner) {
    let mut interner = Interner::new();
    let names: Vec<Segments> = files
        .iter()
        .map(|(n, _)| {
            n.split('.')
                .map(|s| interner.intern(s.as_bytes()))
                .collect()
        })
        .collect();
    let parsed: Vec<_> = files
        .iter()
        .map(|(_, s)| parse_file(s.as_bytes()))
        .collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(files)
        .zip(&names)
        .map(|((p, (_, s)), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s.as_bytes(),
            name: n.clone(),
        })
        .collect();
    let out = fors_resolve::resolve(&mut interner, &inputs, None);
    (out, interner)
}

fn file_result_text(out: &ResolveOutput, i: usize) -> Vec<String> {
    let f = &out.files[i];
    let mut v: Vec<String> = f
        .diagnostics
        .iter()
        .map(|d| {
            format!(
                "{}..{} {} {}",
                d.start,
                d.end,
                d.code.as_string(),
                d.message
            )
        })
        .collect();
    v.extend(
        f.name_uses
            .node
            .iter()
            .zip(&f.name_uses.target)
            .map(|(n, t)| format!("{n} {t:?}")),
    );
    v
}

fn decl_hashes(src: &str, name: &str) -> (u128, u128) {
    let p = parse_file(src.as_bytes());
    let mut interner = Interner::new();
    let decls = build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
    let want = interner.intern(name.as_bytes());
    let i = decls
        .name
        .iter()
        .position(|n| *n == Some(want))
        .expect("declaration not found");
    (decls.sig_hash[i], decls.body_hash[i])
}

const TARGET: &str =
    "pub fn target[T](let x: T, let n: i32) -> i32 {\n    let y: i32 = n + 1;\n    return y;\n}\n";

#[test]
fn fingerprints_ignore_everything_outside_the_token_range() {
    let alone = decl_hashes(TARGET, "target");
    let surroundings = [
        ("module m;\nuse a.b;\n", "fn after() -> i32 { return 1; }\n"),
        (
            "struct Before { x: i32 }\n\n\n/* c */ const K: i32 = 3;\n",
            "",
        ),
        (
            "fn target2() {}\nenum E { a, b }\n",
            "impl E { fn target(let self: Self) -> i32 { return 0; } }\n",
        ),
        // Broken neighbours must not leak in either.
        ("fn broken( {\n", "struct {{{\n"),
    ];
    for (before, after) in surroundings {
        let src = format!("{before}{TARGET}{after}");
        assert_eq!(
            decl_hashes(&src, "target"),
            alone,
            "neighbours changed the fingerprint: {before:?} .. {after:?}"
        );
    }
}

#[test]
fn whitespace_and_comment_edits_change_no_fingerprint_in_the_file() {
    let base = "module m;\nuse a.b;\npub struct S[T] { pub v: T, w: i32 }\nenum E { one(i32), two { a: i32 } }\ntrait Tr { fn get(let self: Self) -> i32; }\nimpl Tr for S[i32] { fn get(let self: Self) -> i32 { return self.w; } }\nconst K: i32 = 1 + 2;\nfn f(let n: i32) -> i32 { match n { K => 1, other => other } }\n";
    // Re-spell the file token by token with different trivia everywhere.
    let (tokens, _) = fors_lex::lex(base.as_bytes());
    let mut edited = String::from("// leading comment\n\n");
    for i in 0..tokens.len() {
        if tokens.kinds[i].is_trivia() {
            continue;
        }
        edited.push_str(std::str::from_utf8(tokens.text(i, base.as_bytes())).unwrap());
        edited.push_str(if i % 3 == 0 { " /* c */\n\t" } else { "  " });
    }
    let table = |src: &str| {
        let p = parse_file(src.as_bytes());
        assert!(p.diags.is_empty(), "test source must parse: {src}");
        let mut interner = Interner::new();
        let d = build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
        (d.kind.clone(), d.sig_hash.clone(), d.body_hash.clone())
    };
    assert_eq!(table(base), table(&edited));
}

const MOD_B: &str = "module b;\nuse a.Shape, a.area, a;\n\nfn g(let s: Shape) -> i32 {\n    match s {\n        Shape.dot => a.area(s),\n        Shape.line => area(s),\n    }\n}\nfn h() -> i32 { return a.hidden(); }\n";

#[test]
fn body_only_edit_in_a_changes_nothing_for_b() {
    let a1 = "module a;\n\nfn hidden() -> i32 { return 1; }\npub fn area(let s: Shape) -> i32 { return hidden(); }\npub enum Shape { dot, line }\n";
    // Bodies rewritten: more statements, locals, closures, a different
    // node count ahead of `Shape` — signatures and item order untouched.
    let a2 = "module a;\n\nfn hidden() -> i32 {\n    let k: i32 = 41;\n    let g = |q: i32| q + k;\n    return g(1);\n}\npub fn area(let s: Shape) -> i32 {\n    match s {\n        Shape.dot => { return 0; },\n        let other => { return hidden(); },\n    }\n}\npub enum Shape { dot, line }\n";
    let (o1, i1) = resolve_pkg(&[("a", a1), ("b", MOD_B)]);
    let (o2, i2) = resolve_pkg(&[("a", a2), ("b", MOD_B)]);
    assert!(
        o1.files[0].diagnostics.is_empty() && o2.files[0].diagnostics.is_empty(),
        "module a must be clean"
    );
    assert_eq!(
        o1.export_signature(0, &i1),
        o2.export_signature(0, &i2),
        "a body edit changed a's export table"
    );
    assert_eq!(
        file_result_text(&o1, 1),
        file_result_text(&o2, 1),
        "a body edit in a changed b's result"
    );
    // b's one diagnostic is its own: `a.hidden` is private (Rule 10).
    assert_eq!(
        o1.files[1]
            .diagnostics
            .iter()
            .map(|d| d.code)
            .collect::<Vec<_>>(),
        vec![Code::N(10)]
    );
}

#[test]
fn signature_edit_in_a_shows_in_its_export_table() {
    let a1 = "module a;\npub fn area(let s: i32) -> i32 { return s; }\n";
    let a2 = "module a;\npub fn area(let s: i64) -> i32 { return 0; }\n";
    let (o1, i1) = resolve_pkg(&[("a", a1)]);
    let (o2, i2) = resolve_pkg(&[("a", a2)]);
    assert_ne!(o1.export_signature(0, &i1), o2.export_signature(0, &i2));
}

/// Round 3 (D2): the alias of a `pub use` is part of the re-exporting
/// module's export table (a signature-level change for its importers);
/// a private alias, and a body edit beside aliases, are not.
#[test]
fn pub_use_alias_is_signature_level_and_body_edits_stay_local() {
    let inner = "module inner;\npub struct Point { pub x: i32 }\n";
    let api_p = "module api;\npub use inner.Point as P;\n";
    let api_q = "module api;\npub use inner.Point as Q;\n";
    let main = "module main;\nuse api.P as Pt;\nfn f(let p: Pt) -> i32 { return 0; }\n";
    let (o1, i1) = resolve_pkg(&[("inner", inner), ("api", api_p), ("main", main)]);
    assert!(
        o1.files.iter().all(|f| f.diagnostics.is_empty()),
        "aliased re-export chain must be clean"
    );
    // Renaming the re-export alias changes api's export table and breaks
    // the importer -- in the importer's file, with Rule 4's code.
    let (o2, i2) = resolve_pkg(&[("inner", inner), ("api", api_q), ("main", main)]);
    assert_ne!(
        o1.export_signature(1, &i1),
        o2.export_signature(1, &i2),
        "a pub use alias rename must change the export table"
    );
    assert_eq!(
        o1.export_signature(0, &i1),
        o2.export_signature(0, &i2),
        "inner is untouched by api's alias"
    );
    assert!(o2.files[1].diagnostics.is_empty());
    assert_eq!(
        o2.files[2]
            .diagnostics
            .iter()
            .map(|d| d.code)
            .collect::<Vec<_>>(),
        vec![Code::N(4)]
    );
    // A private alias rename in main is invisible outside main.
    let main_b = "module main;\nuse api.P as Other;\nfn f(let p: Other) -> i32 { return 0; }\n";
    let (o3, i3) = resolve_pkg(&[("inner", inner), ("api", api_p), ("main", main_b)]);
    assert!(o3.files.iter().all(|f| f.diagnostics.is_empty()));
    assert_eq!(
        o1.export_signature(2, &i1),
        o3.export_signature(2, &i3),
        "a private alias is not exported"
    );
    // A body-only edit in main (using `let` patterns and a local that
    // shadows a prelude name) changes nothing for inner or api.
    let main_c = "module main;\nuse api.P as Pt;\nfn f(let p: Pt) -> i32 {\n    let io: i32 = 1;\n    match io {\n        let n => { return n; },\n    }\n}\n";
    let (o4, i4) = resolve_pkg(&[("inner", inner), ("api", api_p), ("main", main_c)]);
    assert!(o4.files.iter().all(|f| f.diagnostics.is_empty()));
    for m in 0..3 {
        assert_eq!(
            o1.export_signature(m, &i1),
            o4.export_signature(m, &i4),
            "a body edit changed module {m}'s export table"
        );
    }
    assert_eq!(file_result_text(&o1, 0), file_result_text(&o4, 0));
    assert_eq!(file_result_text(&o1, 1), file_result_text(&o4, 1));
}

#[test]
fn variant_through_reexport_is_an_ordinal_not_a_tree_node() {
    let inner = "module inner;\nfn pad() -> i32 { return 1; }\npub enum Color { red, green }\n";
    let api = "module api;\npub use inner.Color;\n";
    let main = "module main;\nuse api.Color;\nfn f() -> Color { return Color.green; }\n";
    let (out, _) = resolve_pkg(&[("inner", inner), ("api", api), ("main", main)]);
    assert!(out.files.iter().all(|f| f.diagnostics.is_empty()));
    let found = out.files[2].name_uses.target.iter().any(|t| matches!(t, ResolvedTarget::Entity(Entity::Variant { file, index: 1, .. }) if file.0 == 0));
    assert!(
        found,
        "Color.green should resolve to variant #1 of inner's enum: {:?}",
        out.files[2].name_uses.target
    );
}

#[test]
fn diagnostics_land_in_the_file_that_caused_them() {
    // Both `use` paths sit at the same byte range of their files.
    let (out, _) = resolve_pkg(&[
        ("aa", "use bb;\nfn f() {}\n"),
        ("bb", "use aa;\nfn g() {}\n"),
        ("cc", "use cc;\n"),
    ]);
    let codes = |i: usize| {
        out.files[i]
            .diagnostics
            .iter()
            .map(|d| d.code)
            .collect::<Vec<_>>()
    };
    // The cycle is reported on the edge that closes it back to the
    // least module name: bb's `use aa`.
    assert_eq!(codes(0), vec![]);
    assert_eq!(codes(1), vec![Code::N(7)]);
    assert_eq!(codes(2), vec![Code::N(8)]);
}

#[test]
fn one_diagnostic_per_root_cause() {
    // `let io` conflicts with nothing: round 3 (D3) let a function-local
    // binding shadow a prelude name, and round 5 (D3) removed prelude
    // modules altogether, so `io` here is an ordinary free name (this
    // module imports no `std.io`) and only the three `use` root causes
    // are reported.
    let main = "module main;\nuse nowhere.thing, lib.hid, lib.gone;\nfn f() -> i32 { return thing() + hid() + gone() + thing.x; }\nfn g(let t: thing) -> gone { let io: i32 = 1; return io + io; }\n";
    let lib = "module lib;\nfn hid() -> i32 { return 1; }\n";
    let (out, _) = resolve_pkg(&[("main", main), ("lib", lib)]);
    let codes: Vec<Code> = out.files[0].diagnostics.iter().map(|d| d.code).collect();
    assert_eq!(
        codes,
        vec![Code::N(4), Code::N(4), Code::N(4)],
        "{:?}",
        out.files[0].diagnostics
    );
}

#[test]
fn file_order_does_not_change_diagnostics() {
    let files = [
        (
            "main",
            "module main;\nuse lib.Point, lib.nope;\nfn f(let p: Point) -> i32 { let p: i32 = 1; return q; }\n",
        ),
        (
            "lib",
            "module lib;\npub struct Point { pub x: i32, pub x: i32 }\nfn Point() {}\n",
        ),
        ("other", "module other;\nuse main;\nfn i32() {}\n"),
    ];
    let text = |order: &[usize]| {
        let pkg: Vec<(&str, &str)> = order.iter().map(|&i| files[i]).collect();
        let (out, _) = resolve_pkg(&pkg);
        let mut per: Vec<(usize, Vec<String>)> = order
            .iter()
            .enumerate()
            .map(|(pos, &i)| {
                (
                    i,
                    out.files[pos]
                        .diagnostics
                        .iter()
                        .map(|d| {
                            format!(
                                "{}..{} {} {}",
                                d.start,
                                d.end,
                                d.code.as_string(),
                                d.message
                            )
                        })
                        .collect(),
                )
            })
            .collect();
        per.sort();
        per
    };
    let base = text(&[0, 1, 2]);
    assert!(base.iter().all(|(_, d)| !d.is_empty()));
    for order in [[2, 1, 0], [1, 0, 2], [1, 2, 0]] {
        assert_eq!(text(&order), base);
    }
}

// ---- robustness ----

struct Lcg(u64);
impl Lcg {
    fn next(&mut self, bound: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % bound.max(1)
    }
}

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
        let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
        entries.sort();
        for p in entries {
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

/// Deletes, duplicates or swaps whole tokens.
fn mutate(src: &str, rng: &mut Lcg) -> String {
    let (tokens, _) = fors_lex::lex(src.as_bytes());
    let mut parts: Vec<&[u8]> = (0..tokens.len())
        .map(|i| tokens.text(i, src.as_bytes()))
        .collect();
    for _ in 0..1 + rng.next(3) {
        if parts.is_empty() {
            break;
        }
        let i = rng.next(parts.len());
        match rng.next(3) {
            0 => {
                parts.remove(i);
            }
            1 => parts.insert(i, parts[i]),
            _ => {
                let j = rng.next(parts.len());
                parts.swap(i, j);
            }
        }
    }
    String::from_utf8_lossy(&parts.concat()).into_owned()
}

#[test]
fn never_panics_on_parse_error_corpus_or_mutated_files() {
    let files = corpus_files();
    assert!(files.len() > 100);
    let sources: Vec<String> = files
        .iter()
        .map(|f| fs::read_to_string(f).unwrap_or_default())
        .collect();
    // Every corpus file as it is, parse errors included, alone and beside
    // a second module that imports it.
    for s in &sources {
        let _ = resolve_pkg(&[("m", s)]);
        let _ = resolve_pkg(&[
            ("lib", s),
            (
                "main",
                "module main;\nuse lib, lib.f, lib.x;\nfn g() -> i32 { return lib.f() + f(); }\n",
            ),
        ]);
    }
    let mut rng = Lcg(0x5eed);
    let mut cases = 0;
    while cases < 4000 {
        let s = &sources[rng.next(sources.len())];
        let m = mutate(s, &mut rng);
        let other = mutate(&sources[rng.next(sources.len())], &mut rng);
        let _ = resolve_pkg(&[("m", &m), ("lib", &other)]);
        cases += 1;
    }
}

/// Round 5 (D3): a dependency lives in the header or nowhere. A body
/// edit that starts spelling `io.len` on a local named `io` (the token
/// pair the deleted whole-file scan keyed on) changes nothing for any
/// other module and adds no edge; only a header edit adding `use
/// std.io;` does — and it then closes the cycle with std.io's `use main;`.
#[test]
fn use_edges_come_from_headers_only_body_edits_add_none() {
    let std_io = "module std.io;\nuse main;\n\npub struct Stdout { fd: i32 }\n";
    let main_a = "module main;\nneeds { env };\n\nfn f() -> usize { return 1; }\n";
    let main_b = "module main;\nneeds { env };\n\nfn f() -> usize {\n    let io: Str = \"a\";\n    return io.len;\n}\n";
    let main_c = "module main;\nneeds { env };\nuse std.io;\n\nfn f() -> usize { return 1; }\n";
    let (oa, ia) = resolve_pkg(&[("main", main_a), ("std.io", std_io)]);
    let (ob, ib) = resolve_pkg(&[("main", main_b), ("std.io", std_io)]);
    assert!(
        oa.files.iter().all(|f| f.diagnostics.is_empty()),
        "{:?}",
        oa.files
            .iter()
            .map(|f| f
                .diagnostics
                .iter()
                .map(|d| d.code.as_string())
                .collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );
    assert!(
        ob.files.iter().all(|f| f.diagnostics.is_empty()),
        "a body mention of `io.` adds no edge and so no cycle"
    );
    assert_eq!(
        file_result_text(&oa, 1),
        file_result_text(&ob, 1),
        "std.io's result is untouched by main's body edit"
    );
    assert_eq!(oa.export_signature(0, &ia), ob.export_signature(0, &ib));
    let (oc, _) = resolve_pkg(&[("main", main_c), ("std.io", std_io)]);
    let codes: Vec<Code> = oc
        .files
        .iter()
        .flat_map(|f| f.diagnostics.iter().map(|d| d.code))
        .collect();
    assert!(
        codes.contains(&Code::N(7)),
        "the header's `use std.io;` is what closes the cycle: {codes:?}"
    );
}
