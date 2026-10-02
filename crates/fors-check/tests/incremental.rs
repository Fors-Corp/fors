//! M1 exit gate (c): "a single-declaration edit invalidates only its
//! dependents" (`docs/PLAN.md` M1, design §9.2's contract table and §12's
//! "gated on the exact re-run set").
//!
//! Every test here asserts the EXACT set of re-executed queries and, by set
//! equality, the exact set NOT re-executed. A subset assertion would pass a
//! checker that re-ran everything.
//!
//! The suite runs with the query set's oracle on
//! ([`QueryBuild::set_paranoid`]): after each re-check, every value the engine
//! decided not to recompute is compared against what the fresh whole-build
//! signature phase would have produced, so a missing in-edge fails here
//! rather than becoming a stale accept.

use fors_check::queries::{QueryBuild, kind};
use fors_index::Interner;
use fors_index::ids::FileId;

// -------------------------------------------------------------- the corpus

/// `pkg.core`: the module everything else imports. Private and public
/// signatures, an impl of a trait, a trait with an associated type, and
/// bodies that depend on exactly one of them each.
const CORE: &str = r#"module pkg.core;

pub struct Rec { pub a: i32, pub b: i32 }

pub struct Other { pub a: i32 }

struct Priv { p: i32 }

pub trait Tr { fn go(let self) -> i32; }

pub trait Keyed { type Key: Eq + Ord; fn key(let self) -> Self.Key; }

impl Tr for Rec { fn go(let self: Rec) -> i32 { return self.a; } }

impl Keyed for Rec {
    type Key = i64;
    fn key(let self: Rec) -> Self.Key { return 1; }
}

pub fn core_pub(let x: i32) -> i32 { return x + 1; }

fn core_priv(let v: Priv) -> i32 { return v.p; }

pub fn uses_priv(let v: Priv) -> i32 { return core_priv(v); }

pub fn uses_rec(let r: Rec) -> i32 { return r.a; }

pub fn calls_go_on_rec(let r: Rec) -> i32 { return r.go(); }

pub fn uses_key(let r: Rec) -> i32 { let k = r.key(); return 0; }

pub fn independent(let x: i32) -> i32 { return x * 3; }

pub fn generic_fn[T: Eq + Ord](let x: T) -> i32 { return 0; }
"#;

/// `pkg.leaf`: imports `pkg.core`, and has a public signature of its own that
/// `pkg.app` depends on.
const LEAF: &str = r#"module pkg.leaf;
use pkg.core, pkg.core.core_pub;

pub struct LeafRec { pub a: i32 }

pub fn leaf_uses_core_pub(let x: i32) -> i32 { return core_pub(x); }

pub fn leaf_reads_leafrec(let l: LeafRec) -> i32 { return l.a; }

pub fn leaf_independent(let x: i32) -> i32 { return x - 1; }
"#;

/// `pkg.app`: imports `pkg.leaf` only, so an edit in `pkg.core` reaches it
/// only through `pkg.leaf`'s exports.
const APP: &str = r#"module pkg.app;
use pkg.leaf, pkg.leaf.leaf_uses_core_pub, pkg.leaf.LeafRec;

pub fn app_calls_leaf(let x: i32) -> i32 { return leaf_uses_core_pub(x); }

pub fn app_reads_leafrec(let l: LeafRec) -> i32 { return l.a; }

pub fn app_independent(let x: i32) -> i32 { return x; }
"#;

const CORE_F: usize = 0;
const LEAF_F: usize = 1;
const APP_F: usize = 2;

struct H {
    qb: QueryBuild,
    sources: Vec<String>,
    ids: Vec<FileId>,
}

fn harness() -> H {
    build(&[
        ("pkg.core", CORE.to_string()),
        ("pkg.leaf", LEAF.to_string()),
        ("pkg.app", APP.to_string()),
    ])
}

fn build(files: &[(&str, String)]) -> H {
    let mut qb = QueryBuild::new();
    qb.set_paranoid(true);
    let mut ids = Vec::new();
    let mut sources = Vec::new();
    for (name, src) in files {
        let segs: Vec<_> = {
            let interner: &mut Interner = qb.interner_mut();
            name.split('.')
                .map(|s| interner.intern(s.as_bytes()))
                .collect()
        };
        let path = format!("{}.fors", name.replace('.', "/"));
        ids.push(qb.add_file(&path, segs, src.clone().into_bytes()));
        sources.push(src.clone());
    }
    let mut h = H { qb, sources, ids };
    h.recheck();
    h
}

impl H {
    fn recheck(&mut self) {
        self.qb
            .recheck()
            .expect("a re-check that was never cancelled");
        assert!(
            self.qb.oracle_failures().is_empty(),
            "the cold-signature oracle disagrees with the memo:\n{}",
            self.qb.oracle_failures().join("\n")
        );
    }

    /// Replaces `from` with `to` in one file (exactly once) and re-checks with
    /// a fresh counting window.
    fn edit(&mut self, file: usize, from: &str, to: &str) {
        let n = self.sources[file].matches(from).count();
        assert_eq!(n, 1, "the edit anchor {from:?} must be unique, found {n}");
        self.sources[file] = self.sources[file].replace(from, to);
        self.qb
            .edit_file(self.ids[file], self.sources[file].clone().into_bytes());
        self.qb.open_window();
        self.recheck();
    }

    fn signatures(&self) -> Vec<String> {
        self.qb.executed_names(kind::SIGNATURE_OF)
    }

    fn bodies(&self) -> Vec<String> {
        self.qb.executed_names(kind::CHECK_BODY)
    }

    fn ran(&self, k: u16) -> usize {
        self.qb.executed_count(k)
    }

    /// Diagnostics as text, path-based so a permutation of the file order
    /// cannot change them.
    fn rendered(&self) -> Vec<String> {
        let mut v: Vec<String> = self
            .qb
            .diagnostics()
            .iter()
            .map(|d| {
                format!(
                    "{}:{}-{}: {} (site {}) {}",
                    self.qb.file_path(d.file),
                    d.start,
                    d.end,
                    d.code.as_string(),
                    d.site,
                    d.message
                )
            })
            .collect();
        v.sort();
        v
    }
}

fn names(xs: &[&str]) -> Vec<String> {
    let mut v: Vec<String> = xs.iter().map(|s| s.to_string()).collect();
    v.sort();
    v.dedup();
    v
}

// ------------------------------------------------------------- the gate (c)

#[test]
fn the_corpus_checks_clean_cold() {
    let h = harness();
    assert_eq!(h.rendered(), Vec::<String>::new());
}

#[test]
fn single_declaration_edit_rechecks_exactly_its_dependents() {
    // Design §9.2's contract table, one edit class per block. Each block
    // asserts the exact set of re-executed `signature_of`/`check_body` keys,
    // which by set equality is also the exact set NOT re-executed.
    let mut h = harness();

    // (1) comment / whitespace: no row hash changes, so `parse`,
    // `decl_index` and `decl_keys` of the file run and come out green
    // (§9.2's "values unchanged"), and nothing else runs at all.
    h.edit(
        CORE_F,
        "pub fn independent",
        "// a comment\npub fn independent",
    );
    assert_eq!(h.signatures(), Vec::<String>::new(), "comment edit");
    assert_eq!(h.bodies(), Vec::<String>::new(), "comment edit");
    assert_eq!(
        h.ran(kind::DECL_INDEX),
        0,
        "the token hashes did not change"
    );
    assert_eq!(h.ran(kind::DECL_KEYS), 0);

    // (2) body of `f`: `check_body(f)` only. No signature, no other body.
    h.edit(CORE_F, "return x * 3;", "return x * 4;");
    assert_eq!(h.bodies(), names(&["independent"]), "body edit");
    assert_eq!(h.signatures(), Vec::<String>::new(), "body edit");

    // (3) private signature in module `m`: `signature_of` of the edited
    // declaration, then `check_body` of every declaration in `m` whose
    // `DepSet` contains it. Importers are untouched: `module_exports` does
    // not move for a private row.
    h.edit(
        CORE_F,
        "struct Priv { p: i32 }",
        "struct Priv { p: i32, q: i32 }",
    );
    assert_eq!(h.signatures(), names(&["Priv"]), "private signature");
    // `core_priv` is the only body whose `DepSet` contains `Priv`.
    // `uses_priv` reads `core_priv`'s SIGNATURE, which ch09 R2 makes the whole
    // interface — and that signature is unchanged, because a nominal type is
    // encoded by its `DeclKey`, not by its field list. So the cutoff stops at
    // `core_priv`, and that is the point of the gate.
    assert_eq!(
        h.bodies(),
        names(&["core_priv"]),
        "private signature: only the bodies in `m` whose DepSet contains it"
    );

    // (4) public signature of a leaf-module item: `module_exports(leaf)`
    // moves, so the importers that depend on that row follow.
    h.edit(
        LEAF_F,
        "pub struct LeafRec { pub a: i32 }",
        "pub struct LeafRec { pub a: i32, pub b: i32 }",
    );
    assert_eq!(h.signatures(), names(&["LeafRec"]), "public leaf signature");
    assert_eq!(
        h.bodies(),
        names(&["leaf_reads_leafrec", "app_reads_leafrec"]),
        "public leaf signature: the importers that read the row, and no other"
    );

    // (5) public signature in a core module: the transitive dependents by
    // recorded `DepSet`, exactly — and unrelated modules stay green.
    h.edit(
        CORE_F,
        "pub struct Rec { pub a: i32, pub b: i32 }",
        "pub struct Rec { pub a: i32, pub b: i32, pub c: i32 }",
    );
    assert_eq!(h.signatures(), names(&["Rec"]), "public core signature");
    // Every body whose `DepSet` contains `Rec`. `key`'s does not: its
    // signature is `-> Self.Key` and its body `return 1;` never names `Rec`
    // as a type it read. Nothing in `pkg.leaf` or `pkg.app` is woken, which is
    // the half of the contract that a global invalidation would break.
    assert_eq!(
        h.bodies(),
        names(&["go", "uses_rec", "calls_go_on_rec", "uses_key"]),
        "public core signature: every body whose DepSet contains `Rec`"
    );

    // (6) `type A = T;` in an impl: the impl's signature, the bucket merkle,
    // and the bodies that normalised through that bucket. Not the bodies
    // that never looked it up.
    h.edit(CORE_F, "type Key = i64;", "type Key = i32;");
    assert_eq!(
        h.signatures(),
        names(&["impl Keyed for Rec", "key"]),
        "the impl's own signature, and the member whose `-> Self.Key` projects          through it"
    );
    // `key`'s signature moved; `uses_key` normalised through the bucket; and
    // `calls_go_on_rec` is here because R43's candidate scan records EVERY
    // impl of the receiver's head as a signature it read while deciding that
    // `go` is not in the `Keyed` impl. That is a recorded read, not a guess —
    // `methods.rs` is the over-approximation, not the DAG — and the bodies
    // that never touched `Rec` at all stay green.
    assert_eq!(
        h.bodies(),
        names(&["calls_go_on_rec", "key", "uses_key"]),
        "the method whose signature moved, the body that normalised through the bucket, and the one whose candidate scan read the impl"
    );

    // (7) method body inside that impl: `check_body(method)` only. The
    // impl's `sig_hash` is unchanged, so nothing else moves.
    h.edit(
        CORE_F,
        "fn key(let self: Rec) -> Self.Key { return 1; }",
        "fn key(let self: Rec) -> Self.Key { return 2; }",
    );
    assert_eq!(h.bodies(), names(&["key"]), "method body edit");
    assert_eq!(h.signatures(), Vec::<String>::new(), "method body edit");

    // (8) adding an impl: its own queries plus the bucket's, and NOT the
    // bodies that use the same trait on another head. The dedicated test
    // below pins the bucket contract; here the point is that the set is
    // exactly the new declarations plus the bucket's readers.
    h.edit(
        CORE_F,
        "pub fn core_pub(let x: i32) -> i32 { return x + 1; }",
        "impl Tr for Other { fn go(let self: Other) -> i32 { return self.a; } }\n\npub fn core_pub(let x: i32) -> i32 { return x + 1; }",
    );
    assert!(
        !h.bodies().contains(&"calls_go_on_rec".to_string()),
        "adding an impl for `Other` must not wake the body that uses `Tr` on `Rec`: {:?}",
        h.bodies()
    );
    assert!(
        !h.bodies().contains(&"independent".to_string()),
        "adding an impl must not wake an unrelated body: {:?}",
        h.bodies()
    );

    // (9) reordering bounds and renaming a generic parameter: `signature_of`
    // re-lowers, the canonical `sig_hash` is unchanged (§14 Q5, Q6), so the
    // early cutoff stops every dependent.
    h.edit(
        CORE_F,
        "pub fn generic_fn[T: Eq + Ord](let x: T) -> i32",
        "pub fn generic_fn[U: Ord + Eq](let x: U) -> i32",
    );
    assert_eq!(h.signatures(), names(&["generic_fn"]), "bound reorder");
    // Its own body is re-checked, because its own text changed — a
    // declaration is not one of its own dependents. Every DEPENDENT is
    // stopped by the cutoff, which is what §9.2's row asserts.
    assert_eq!(
        h.bodies(),
        names(&["generic_fn"]),
        "the cutoff must stop every DEPENDENT of a re-spelled signature"
    );

    // (10) inserting a declaration above: `decl_keys(file)` changes and the
    // new declaration's queries run; nothing keyed by `DeclKey` moves, so no
    // existing body is re-checked.
    h.edit(
        CORE_F,
        "module pkg.core;\n",
        "module pkg.core;\n\npub fn inserted(let x: i32) -> i32 { return x; }\n",
    );
    assert_eq!(h.signatures(), names(&["inserted"]), "insertion above");
    assert_eq!(h.bodies(), names(&["inserted"]), "insertion above");
    assert_eq!(
        h.ran(kind::DECL_KEYS),
        1,
        "exactly the edited file's key set"
    );
}

#[test]
fn adding_an_impl_invalidates_only_its_head_bucket() {
    // `calls_go_on_other` probes the `(Tr, Other)` bucket and finds it empty,
    // so it has one diagnostic; `calls_go_on_rec` probes `(Tr, Rec)`. Adding
    // the impl for `Other` must wake the first and not the second.
    let core = CORE.replace(
        "pub fn independent",
        "pub fn calls_go_on_other(let o: Other) -> i32 { return o.go(); }\n\npub fn independent",
    );
    let mut h = build(&[
        ("pkg.core", core),
        ("pkg.leaf", LEAF.to_string()),
        ("pkg.app", APP.to_string()),
    ]);
    assert_eq!(
        h.rendered().len(),
        1,
        "exactly one diagnostic before the impl exists: {:?}",
        h.rendered()
    );

    h.edit(
        CORE_F,
        "impl Keyed for Rec {",
        "impl Tr for Other { fn go(let self: Other) -> i32 { return self.a; } }\n\nimpl Keyed for Rec {",
    );
    assert_eq!(h.rendered(), Vec::<String>::new(), "the impl fixes it");
    assert!(
        h.bodies().contains(&"calls_go_on_other".to_string()),
        "the body that asked for the bucket must re-run: {:?}",
        h.bodies()
    );
    assert!(
        !h.bodies().contains(&"calls_go_on_rec".to_string()),
        "a body using the same trait on another head must stay green — this is \
         the assertion that catches a global impl index: {:?}",
        h.bodies()
    );
    assert!(
        !h.bodies().contains(&"uses_rec".to_string()),
        "an unrelated body must stay green: {:?}",
        h.bodies()
    );
    // And the bucket half of the contract, in counts: adding one impl must not
    // re-execute every bucket in the build. `pkg.core` has `Tr` and `Keyed`
    // over `Rec` and `Other` plus the prelude's buckets for those heads; the
    // re-run set is the buckets of the module whose `impl_heads` moved, never
    // all of them.
    let all_buckets = h.qb.stats().nodes as usize;
    assert!(
        h.ran(kind::IMPLS_FOR) < all_buckets,
        "adding one impl re-executed {} impls_for nodes out of {all_buckets} total \
         nodes — a global impl index would be indistinguishable from this",
        h.ran(kind::IMPLS_FOR)
    );
    assert_eq!(
        h.ran(kind::IMPL_HEADS),
        1,
        "exactly one module's impl head list moved"
    );
}

#[test]
fn assoc_type_def_edit_is_signature_level() {
    // The end-to-end twin of `fors-index`'s
    // `assoc_type_def_is_signature_level_and_method_bodies_are_not`: editing
    // `type Key = ...` moves the IMPL's signature, while editing the method's
    // body moves only `check_body`.
    let mut h = harness();

    h.edit(CORE_F, "type Key = i64;", "type Key = i32;");
    let sig_level = h.ran(kind::SIGNATURE_OF);
    assert!(
        sig_level > 0,
        "an associated-type definition is a signature edit"
    );
    assert!(
        h.bodies().contains(&"key".to_string()),
        "the impl's method body is checked against the new projection: {:?}",
        h.bodies()
    );

    h.edit(
        CORE_F,
        "fn key(let self: Rec) -> Self.Key { return 1; }",
        "fn key(let self: Rec) -> Self.Key { return 7; }",
    );
    assert_eq!(
        h.signatures(),
        Vec::<String>::new(),
        "a method body is not signature level"
    );
    assert_eq!(h.bodies(), names(&["key"]));
}

#[test]
fn check_output_identical_cold_vs_incremental() {
    // The deterministic oracle for every edit class at once: apply a script of
    // edits incrementally, then build the same final sources cold, and require
    // byte-identical output. A missing in-edge anywhere above shows up here as
    // a stale diagnostic or a missing one.
    let script: &[(usize, &str, &str)] = &[
        (CORE_F, "return x * 3;", "return x * 4;"),
        (
            CORE_F,
            "struct Priv { p: i32 }",
            "struct Priv { p: i32, q: i32 }",
        ),
        (
            CORE_F,
            "pub struct Rec { pub a: i32, pub b: i32 }",
            "pub struct Rec { pub a: i32, pub b: i32, pub c: i32 }",
        ),
        (CORE_F, "type Key = i64;", "type Key = i32;"),
        (
            LEAF_F,
            "pub struct LeafRec { pub a: i32 }",
            "pub struct LeafRec { pub a: i32, pub b: i32 }",
        ),
        // An edit that BREAKS, so the comparison covers diagnostics too.
        (CORE_F, "return r.a;", "return r.nosuchfield;"),
        (
            CORE_F,
            "impl Keyed for Rec {",
            "impl Tr for Other { fn go(let self: Other) -> i32 { return self.a; } }\n\nimpl Keyed for Rec {",
        ),
        // And the revert, so the final output must equal the cold output of
        // the reverted text.
        (CORE_F, "return r.nosuchfield;", "return r.a;"),
    ];

    let mut h = harness();
    let cold0 = h.rendered();
    for &(f, from, to) in script {
        h.edit(f, from, to);
        let cold = build(&[
            ("pkg.core", h.sources[CORE_F].clone()),
            ("pkg.leaf", h.sources[LEAF_F].clone()),
            ("pkg.app", h.sources[APP_F].clone()),
        ]);
        assert_eq!(
            h.rendered(),
            cold.rendered(),
            "incremental and cold disagree after editing {from:?} -> {to:?}"
        );
    }

    // Revert everything and require the first cold output back, byte for byte
    // (design §9: "output is byte-identical cold or after an edit-and-revert").
    let mut h2 = harness();
    h2.edit(CORE_F, "return x * 3;", "return x * 4;");
    h2.edit(CORE_F, "return x * 4;", "return x * 3;");
    assert_eq!(
        h2.rendered(),
        cold0,
        "edit and revert must restore the output"
    );
}

#[test]
fn an_edit_and_revert_executes_only_the_edited_declaration_twice() {
    let mut h = harness();
    h.edit(CORE_F, "return x * 3;", "return x * 4;");
    assert_eq!(h.bodies(), names(&["independent"]));
    h.edit(CORE_F, "return x * 4;", "return x * 3;");
    assert_eq!(h.bodies(), names(&["independent"]));
}

// ------------------------------------------------- metamorphic determinism

#[test]
fn permuting_file_order_gives_identical_output() {
    let a = build(&[
        ("pkg.core", CORE.to_string()),
        ("pkg.leaf", LEAF.to_string()),
        ("pkg.app", APP.to_string()),
    ]);
    let b = build(&[
        ("pkg.app", APP.to_string()),
        ("pkg.core", CORE.to_string()),
        ("pkg.leaf", LEAF.to_string()),
    ]);
    let c = build(&[
        ("pkg.leaf", LEAF.to_string()),
        ("pkg.app", APP.to_string()),
        ("pkg.core", CORE.to_string()),
    ]);
    assert_eq!(a.rendered(), b.rendered());
    assert_eq!(a.rendered(), c.rendered());
}

#[test]
fn permuting_declaration_order_gives_the_same_diagnostics() {
    // Positions move by construction, so the invariant is the (code, site,
    // message) multiset — and it must be the same whichever order the
    // declarations were written in.
    let broken = CORE.replace("return r.a;", "return r.nosuchfield;");
    let a = build(&[("pkg.core", broken.clone())]);
    // Move `independent` and `generic_fn` to the top.
    let tail = "pub fn independent(let x: i32) -> i32 { return x * 3; }\n\npub fn generic_fn[T: Eq + Ord](let x: T) -> i32 { return 0; }\n";
    let moved = format!(
        "module pkg.core;\n\n{tail}{}",
        broken
            .replacen("module pkg.core;\n", "", 1)
            .replace(tail, "")
    );
    let b = build(&[("pkg.core", moved)]);
    let strip = |h: &H| -> Vec<String> {
        let mut v: Vec<String> =
            h.qb.diagnostics()
                .iter()
                .map(|d| format!("{} (site {}) {}", d.code.as_string(), d.site, d.message))
                .collect();
        v.sort();
        v
    };
    assert_eq!(strip(&a), strip(&b));
}

#[test]
fn the_printing_walk_is_sorted_by_file_then_offset() {
    let broken = CORE.replace("return r.a;", "return r.nosuchfield;");
    let h = build(&[
        ("pkg.core", broken),
        ("pkg.leaf", LEAF.to_string()),
        ("pkg.app", APP.to_string()),
    ]);
    let ds = h.qb.diagnostics();
    assert!(
        ds.windows(2)
            .all(|w| (w[0].file.0, w[0].start) <= (w[1].file.0, w[1].start)),
        "the printing walk must come out sorted"
    );
}

// ------------------------------------------------------- engine integration

#[test]
fn a_cancelled_recheck_writes_nothing_and_the_next_one_recovers() {
    let mut h = harness();
    let before = h.rendered();
    h.sources[CORE_F] = h.sources[CORE_F].replace("return x * 3;", "return x * 4;");
    h.qb.edit_file(h.ids[CORE_F], h.sources[CORE_F].clone().into_bytes());
    let flag = h.qb.cancel_flag();
    flag.cancel();
    assert!(
        h.qb.recheck().is_err(),
        "a cancelled re-check must report it"
    );
    assert_eq!(h.rendered(), before, "a cancelled re-check writes nothing");
    flag.reset();
    h.qb.open_window();
    h.recheck();
    assert_eq!(h.bodies(), names(&["independent"]));
}

#[test]
fn a_second_recheck_with_no_edit_executes_nothing() {
    let mut h = harness();
    h.qb.open_window();
    h.recheck();
    assert_eq!(
        h.qb.executed_keys(),
        &[],
        "no edit means no revision and therefore no execution: {:?}",
        h.qb.executed_keys()
    );
}

#[test]
fn stats_name_every_kind_that_ran() {
    let h = harness();
    let text = h.qb.render_stats();
    for name in ["parse", "decl_index", "signature_of", "check_body"] {
        assert!(text.contains(name), "--stats must mention {name}:\n{text}");
    }
}

// ------------------------------------------------ the oracle over real code

fn repo_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// `fors_check::check_build` is the reference implementation; the query path
/// must agree with it on every file of the ch09 corpus, diagnostic for
/// diagnostic. This is the deterministic oracle design §12 prefers to a model
/// of what "should" be invalidated: if the DAG's attribution, caching or
/// printing walk loses or moves a diagnostic anywhere in 250 real programs,
/// this fails.
#[test]
fn the_query_path_agrees_with_check_build_over_the_ch09_corpus() {
    let dir = repo_root().join("tests/conformance/09-types");
    let mut paths: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
        .expect("the ch09 corpus")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "fors"))
        .collect();
    paths.sort();
    assert!(
        paths.len() > 200,
        "the ch09 corpus is {} files",
        paths.len()
    );

    let mut mismatches: Vec<String> = Vec::new();
    for p in &paths {
        let src = std::fs::read(p).expect("a corpus file");
        // One file is a one-module package (the corpus's convention), named by
        // its `module` header when it has one.
        let mut interner = Interner::new();
        let parsed = fors_syntax::parse_file(&src);
        let name = header_segments(&parsed, &src, &mut interner)
            .unwrap_or_else(|| vec![interner.intern(b"m")]);
        let inputs = [fors_resolve::FileInput {
            tree: &parsed.tree,
            tokens: &parsed.tokens,
            source: &src,
            name: name.clone(),
        }];
        let resolved = fors_resolve::resolve(&mut interner, &inputs, Some(0));
        let reference = fors_check::check_build(&inputs, &resolved, &mut interner);

        let mut qb = QueryBuild::new();
        qb.set_root(Some(0));
        let segs: Vec<_> = name
            .iter()
            .map(|s| qb.interner_mut().intern(interner.resolve(*s)))
            .collect();
        qb.add_file(&p.display().to_string(), segs, src.clone());
        qb.recheck().expect("never cancelled");

        let fmt = |ds: &[fors_check::Diagnostic]| -> Vec<String> {
            let mut v: Vec<String> = ds
                .iter()
                .map(|d| {
                    format!(
                        "{}-{} {} site {} {}",
                        d.start,
                        d.end,
                        d.code.as_string(),
                        d.site,
                        d.message
                    )
                })
                .collect();
            v.sort();
            v
        };
        let a = fmt(&reference.diagnostics);
        let b = fmt(&qb.diagnostics());
        if a != b {
            mismatches.push(format!(
                "{}\n  check_build: {a:?}\n  query DAG:   {b:?}",
                p.file_name().unwrap().to_string_lossy()
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {} ch09 files disagree:\n{}",
        mismatches.len(),
        paths.len(),
        mismatches.join("\n")
    );
}

fn header_segments(
    parsed: &fors_syntax::Parse,
    src: &[u8],
    interner: &mut Interner,
) -> Option<Vec<fors_index::Symbol>> {
    let child = parsed.tree.children(0).next()?;
    if parsed.tree.kinds[child] != fors_syntax::NodeKind::ModuleHdr {
        return None;
    }
    let path_node = parsed.tree.children(child).next()?;
    let (first, end) = parsed.tree.token_range(path_node);
    let mut out = Vec::new();
    for i in first as usize..end as usize {
        if parsed.tokens.kinds[i] == fors_lex::TokenKind::Ident {
            out.push(interner.intern(parsed.tokens.text(i, src)));
        }
    }
    (!out.is_empty()).then_some(out)
}

// ----------------------------------------------------- the counter gate (b)

/// Generated corpus: `modules` modules of `items` declaration groups each,
/// every group a struct, a trait, an impl of it, and two bodies.
fn generated(modules: usize, items: usize) -> Vec<(String, String)> {
    use std::fmt::Write as _;
    (0..modules)
        .map(|m| {
            let mut s = String::new();
            let _ = writeln!(s, "module pkg.m{m};");
            for i in 0..items {
                let _ = writeln!(s, "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i32 }}");
                let _ = writeln!(s, "pub trait Tr{m}_{i} {{ fn go(let self) -> i32; }}");
                let _ = writeln!(
                    s,
                    "impl Tr{m}_{i} for Rec{m}_{i} {{ fn go(let self: Rec{m}_{i}) -> i32 {{ return self.a; }} }}"
                );
                let _ = writeln!(
                    s,
                    "pub fn read{m}_{i}(let r: Rec{m}_{i}) -> i32 {{ return r.b; }}"
                );
                let _ = writeln!(
                    s,
                    "pub fn call{m}_{i}(let r: Rec{m}_{i}) -> i32 {{ return r.go(); }}"
                );
            }
            (format!("pkg.m{m}"), s)
        })
        .collect()
}

/// The M1 gate (b) COUNTER gate: the number of queries an edit re-executes
/// must not grow with the corpus. Doubling the corpus and repeating the same
/// edit must repeat the same counts — otherwise the engine is doing
/// whole-build work per edit and the wall-clock slope would only be hiding
/// it.
///
/// Three kinds are expected to scale with the corpus and are reported rather
/// than bounded, because §3 fork 14 keeps them whole-build in M1:
/// `name_uses` (a slice of the whole-build `resolve`), `resolve_build` and
/// `signature_phase`. Everything else is per-declaration and must be flat.
#[test]
fn the_reexecution_count_per_edit_class_is_independent_of_corpus_size() {
    let classes: [(&str, &str, &str); 4] = [
        (
            "body",
            "pub fn read0_0(let r: Rec0_0) -> i32 { return r.b; }",
            "pub fn read0_0(let r: Rec0_0) -> i32 { return r.b + 1; }",
        ),
        (
            "private signature",
            "pub struct Rec0_0 { pub a: i32, pub b: i32 }",
            "pub struct Rec0_0 { pub a: i32, pub b: i32, pub c: i32 }",
        ),
        ("comment", "pub fn read0_0", "// note\npub fn read0_0"),
        (
            "add an impl",
            "pub fn read0_0",
            "impl Tr0_1 for Rec0_0 { fn go(let self: Rec0_0) -> i32 { return self.b; } }\n\npub fn read0_0",
        ),
    ];
    let sizes = [2usize, 4, 8];
    let mut table: Vec<(String, usize, usize, usize, usize)> = Vec::new();
    for (label, from, to) in classes {
        let mut per_size: Vec<(usize, usize, usize)> = Vec::new();
        for n in sizes {
            let files = generated(n, 3);
            let owned: Vec<(&str, String)> =
                files.iter().map(|(a, b)| (a.as_str(), b.clone())).collect();
            let mut h = build(&owned);
            assert_eq!(
                h.rendered(),
                Vec::<String>::new(),
                "generated corpus must be clean"
            );
            h.edit(0, from, to);
            per_size.push((
                h.ran(kind::CHECK_BODY),
                h.ran(kind::SIGNATURE_OF),
                h.ran(kind::IMPLS_FOR),
            ));
            table.push((
                label.to_string(),
                n * 3 * 5,
                per_size.last().unwrap().0,
                per_size.last().unwrap().1,
                per_size.last().unwrap().2,
            ));
        }
        for (i, counts) in per_size.iter().enumerate().skip(1) {
            assert_eq!(
                *counts,
                per_size[0],
                "edit class {label:?}: at {} declarations the re-execution counts are \
                 {counts:?} but at {} they were {:?} — the cost of an edit must not \
                 grow with the corpus",
                sizes[i] * 3 * 5,
                sizes[0] * 3 * 5,
                per_size[0]
            );
        }
    }
    eprintln!("edit class              decls  check_body  signature_of  impls_for");
    for (label, decls, cb, so, bf) in &table {
        eprintln!("{label:<22} {decls:>6} {cb:>11} {so:>13} {bf:>10}");
    }
}
