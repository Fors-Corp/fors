//! I9's adversarial verification pass: every test here was written to
//! REFUTE the increment's claims, against design §9.2's contract table and
//! §9's "byte-identical cold or after an edit-and-revert".
//!
//! The judge is deterministic: after every edit the incremental output is
//! compared with a fresh cold build of the same sources, so a missing in-edge
//! shows up as a stale or missing diagnostic rather than as an opinion about
//! what "should" have been invalidated.

use fors_check::queries::{QueryBuild, kind};
use fors_index::Interner;
use fors_index::ids::FileId;

struct H {
    qb: QueryBuild,
    names: Vec<String>,
    sources: Vec<String>,
    ids: Vec<FileId>,
    /// False once removed. `QueryBuild::remove_file` keeps the module as an
    /// empty one (its stated M1 semantics), so the cold twin of a removed
    /// file is the same module with empty source.
    live: Vec<bool>,
}

fn build(files: &[(&str, String)]) -> H {
    let mut qb = QueryBuild::new();
    qb.set_paranoid(true);
    let mut ids = Vec::new();
    let mut sources = Vec::new();
    let mut names = Vec::new();
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
        names.push(name.to_string());
    }
    let n = ids.len();
    let mut h = H {
        qb,
        names,
        sources,
        ids,
        live: vec![true; n],
    };
    h.recheck();
    h
}

impl H {
    fn recheck(&mut self) {
        self.qb.recheck().expect("never cancelled");
        assert!(
            self.qb.oracle_failures().is_empty(),
            "the cold-signature oracle disagrees with the memo:\n{}",
            self.qb.oracle_failures().join("\n")
        );
    }

    fn edit(&mut self, file: usize, from: &str, to: &str) {
        let n = self.sources[file].matches(from).count();
        assert_eq!(n, 1, "the edit anchor {from:?} must be unique, found {n}");
        self.sources[file] = self.sources[file].replace(from, to);
        self.qb
            .edit_file(self.ids[file], self.sources[file].clone().into_bytes());
        self.qb.open_window();
        self.recheck();
    }

    fn add(&mut self, name: &str, src: &str) -> usize {
        let segs: Vec<_> = {
            let interner: &mut Interner = self.qb.interner_mut();
            name.split('.')
                .map(|s| interner.intern(s.as_bytes()))
                .collect()
        };
        let path = format!("{}.fors", name.replace('.', "/"));
        self.ids
            .push(self.qb.add_file(&path, segs, src.as_bytes().to_vec()));
        self.sources.push(src.to_string());
        self.names.push(name.to_string());
        self.live.push(true);
        self.qb.open_window();
        self.recheck();
        self.ids.len() - 1
    }

    fn remove(&mut self, file: usize) {
        self.qb.remove_file(self.ids[file]);
        self.live[file] = false;
        self.sources[file] = String::new();
        self.qb.open_window();
        self.recheck();
    }

    fn bodies(&self) -> Vec<String> {
        self.qb.executed_names(kind::CHECK_BODY)
    }

    fn signatures(&self) -> Vec<String> {
        self.qb.executed_names(kind::SIGNATURE_OF)
    }

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

    /// The oracle: a cold build of exactly these sources must render the same
    /// bytes.
    fn assert_matches_cold(&self, what: &str) {
        let files: Vec<(&str, String)> = self
            .names
            .iter()
            .zip(self.sources.iter())
            .map(|(n, s)| (n.as_str(), s.clone()))
            .collect();
        let cold = build(&files);
        assert_eq!(
            self.rendered(),
            cold.rendered(),
            "incremental and cold disagree after {what}"
        );
    }
}

fn names(xs: &[&str]) -> Vec<String> {
    let mut v: Vec<String> = xs.iter().map(|s| s.to_string()).collect();
    v.sort();
    v.dedup();
    v
}

// ------------------------------------------------- §9.2 row 8, cross-module

/// ch08 R21 lets an impl live in the TRAIT's module as well as the head's. A
/// body in a third module that asked whether `Other: Keyed` holds recorded the
/// empty bucket `(Keyed, Other)`; the impl landing in `pkg.core` (the trait's
/// module, which the asking module never imports directly) must still wake
/// that body.
#[test]
fn an_impl_added_in_the_traits_module_wakes_the_cross_module_body_that_probed_the_empty_bucket() {
    let base = "module pkg.base;\n\npub struct Other { pub a: i32 }\n";
    let core = "module pkg.core;\nuse pkg.base, pkg.base.Other;\n\npub trait Keyed { type Key: Eq + Ord; fn key(let self) -> Self.Key; }\n\npub fn core_only(let x: i32) -> i32 { return x; }\n";
    let mid = "module pkg.mid;\nuse pkg.core, pkg.core.Keyed;\n\npub fn needs_keyed[T: Keyed](let x: T) -> i32 { return 0; }\n";
    let app = "module pkg.app;\nuse pkg.base, pkg.base.Other, pkg.mid, pkg.mid.needs_keyed;\n\npub fn g(let o: Other) -> i32 { return needs_keyed(o); }\n\npub fn unrelated(let x: i32) -> i32 { return x; }\n";
    let mut h = build(&[
        ("pkg.base", base.to_string()),
        ("pkg.core", core.to_string()),
        ("pkg.mid", mid.to_string()),
        ("pkg.app", app.to_string()),
    ]);
    assert_eq!(
        h.rendered().len(),
        1,
        "exactly one diagnostic before the impl exists: {:?}",
        h.rendered()
    );

    h.edit(
        1,
        "pub fn core_only",
        "impl Keyed for Other { type Key = i64; fn key(let self: Other) -> Self.Key { return 1; } }\n\npub fn core_only",
    );
    h.assert_matches_cold("adding the impl in the trait's module");
    assert_eq!(
        h.rendered(),
        Vec::<String>::new(),
        "the impl satisfies the bound"
    );
    assert!(
        h.bodies().contains(&"g".to_string()),
        "the body that probed the empty bucket must re-run: {:?}",
        h.bodies()
    );
    assert!(
        !h.bodies().contains(&"unrelated".to_string()),
        "an unrelated body must stay green: {:?}",
        h.bodies()
    );

    // And removing it again: the bucket empties, the body must re-run and the
    // diagnostic come back.
    h.edit(
        1,
        "impl Keyed for Other { type Key = i64; fn key(let self: Other) -> Self.Key { return 1; } }\n\n",
        "",
    );
    h.assert_matches_cold("removing the impl again");
    assert_eq!(h.rendered().len(), 1, "{:?}", h.rendered());
}

/// The mirror case: the impl lands in the HEAD's module.
#[test]
fn an_impl_added_in_the_heads_module_wakes_the_cross_module_body_that_probed_the_empty_bucket() {
    let base = "module pkg.base;\n\npub trait Keyed { type Key: Eq + Ord; fn key(let self) -> Self.Key; }\n\npub fn needs_keyed[T: Keyed](let x: T) -> i32 { return 0; }\n";
    let core = "module pkg.core;\nuse pkg.base, pkg.base.Keyed;\n\npub struct Other { pub a: i32 }\n\npub fn core_only(let x: i32) -> i32 { return x; }\n";
    let app = "module pkg.app;\nuse pkg.core, pkg.core.Other, pkg.base, pkg.base.needs_keyed;\n\npub fn g(let o: Other) -> i32 { return needs_keyed(o); }\n";
    let mut h = build(&[
        ("pkg.base", base.to_string()),
        ("pkg.core", core.to_string()),
        ("pkg.app", app.to_string()),
    ]);
    assert_eq!(h.rendered().len(), 1, "{:?}", h.rendered());
    h.edit(
        1,
        "pub fn core_only",
        "impl Keyed for Other { type Key = i64; fn key(let self: Other) -> Self.Key { return 1; } }\n\npub fn core_only",
    );
    h.assert_matches_cold("adding the impl in the head's module");
    assert_eq!(h.rendered(), Vec::<String>::new());
    assert!(h.bodies().contains(&"g".to_string()), "{:?}", h.bodies());
}

/// `impl Copyable for W` asks whether `W`'s field type `S` is `Copyable`; the
/// answer lives in `S`'s module, which is neither the impl's nor `W`'s trait's.
#[test]
fn a_copyable_impl_follows_its_field_types_impl_in_another_module() {
    let base = "module pkg.base;\n\npub struct S { pub a: i32 }\n\npub fn base_only(let x: i32) -> i32 { return x; }\n";
    let core = "module pkg.core;\nuse pkg.base, pkg.base.S;\n\npub struct W { pub s: S }\n\nimpl Copyable for W { }\n\npub fn unrelated(let x: i32) -> i32 { return x; }\n";
    let mut h = build(&[
        ("pkg.base", base.to_string()),
        ("pkg.core", core.to_string()),
    ]);
    assert_eq!(
        h.rendered().len(),
        1,
        "`S` is not Copyable: {:?}",
        h.rendered()
    );
    h.edit(
        0,
        "pub fn base_only",
        "impl Copyable for S { }\n\npub fn base_only",
    );
    h.assert_matches_cold("adding `impl Copyable for S` in S's module");
    assert_eq!(h.rendered(), Vec::<String>::new());
    assert!(
        h.signatures().contains(&"impl Copyable for W".to_string()),
        "{:?}",
        h.signatures()
    );
    assert!(
        !h.bodies().contains(&"unrelated".to_string()),
        "{:?}",
        h.bodies()
    );
    h.edit(0, "impl Copyable for S { }\n\n", "");
    h.assert_matches_cold("removing it again");
    assert_eq!(h.rendered().len(), 1);
}

// ---------------------------------- signature-phase diagnostics on a green node

const ONE: &str = r#"module pkg.one;

pub struct Rec { pub a: i32, pub b: i32 }

pub trait Tr { fn go(let self) -> i32; }

impl Tr for Rec { fn go(let self: Rec) -> i32 { return self.a; } }

pub fn calls_go(let r: Rec) -> i32 { return r.go(); }

pub fn independent(let x: i32) -> i32 { return x; }
"#;

/// Adding a required method to a trait makes every impl of it incomplete
/// (T0017 at the IMPL). The impl's own tokens did not change; the diagnostic
/// lives on the impl's `signature_of` node, which must therefore depend on the
/// trait's signature and not only on its arity.
#[test]
fn a_trait_gaining_a_required_method_reports_the_impl_incomplete_incrementally() {
    let mut h = build(&[("pkg.one", ONE.to_string())]);
    assert_eq!(h.rendered(), Vec::<String>::new());

    h.edit(
        0,
        "pub trait Tr { fn go(let self) -> i32; }",
        "pub trait Tr { fn go(let self) -> i32; fn go2(let self) -> i32; }",
    );
    h.assert_matches_cold("adding a required method to the trait");
    assert_eq!(h.rendered().len(), 1, "{:?}", h.rendered());
    assert!(
        h.signatures().contains(&"impl Tr for Rec".to_string()),
        "the impl's signature_of must re-execute: {:?}",
        h.signatures()
    );

    h.edit(
        0,
        "pub trait Tr { fn go(let self) -> i32; fn go2(let self) -> i32; }",
        "pub trait Tr { fn go(let self) -> i32; }",
    );
    h.assert_matches_cold("removing it again");
    assert_eq!(h.rendered(), Vec::<String>::new());
}

/// The trait method's RETURN TYPE changes: the impl's method no longer
/// conforms. Same shape: the impl's tokens did not move.
#[test]
fn a_trait_method_signature_change_reports_the_nonconforming_impl_incrementally() {
    let mut h = build(&[("pkg.one", ONE.to_string())]);
    h.edit(
        0,
        "pub trait Tr { fn go(let self) -> i32; }",
        "pub trait Tr { fn go(let self) -> i64; }",
    );
    h.assert_matches_cold("changing the trait method's return type");
    assert!(!h.rendered().is_empty(), "the impl no longer conforms");
    h.edit(
        0,
        "pub trait Tr { fn go(let self) -> i64; }",
        "pub trait Tr { fn go(let self) -> i32; }",
    );
    h.assert_matches_cold("reverting the trait");
    assert_eq!(h.rendered(), Vec::<String>::new());
}

/// R19 overlap: a second impl of the same trait for the same head. The
/// diagnostic is attributed to one impl; whichever one, it must appear and
/// disappear with the edit.
#[test]
fn an_overlapping_impl_is_reported_and_unreported_incrementally() {
    let mut h = build(&[("pkg.one", ONE.to_string())]);
    h.edit(
        0,
        "pub fn calls_go",
        "impl Tr for Rec { fn go(let self: Rec) -> i32 { return self.b; } }\n\npub fn calls_go",
    );
    h.assert_matches_cold("adding an overlapping impl");
    assert!(!h.rendered().is_empty(), "overlap must be reported");
    h.edit(
        0,
        "impl Tr for Rec { fn go(let self: Rec) -> i32 { return self.b; } }\n\npub fn calls_go",
        "pub fn calls_go",
    );
    h.assert_matches_cold("removing the overlapping impl");
    assert_eq!(h.rendered(), Vec::<String>::new());
}

/// R14 infinite size: the verdict is a whole-build node, but its diagnostic is
/// cached on whichever declaration it was emitted at. Fixing the cycle by
/// editing the OTHER declaration must still clear it.
#[test]
fn an_infinite_size_cycle_is_reported_and_cleared_from_either_end() {
    let src = "module pkg.one;\n\npub struct A { pub b: B }\n\npub struct B { pub a: A }\n\npub fn f(let x: i32) -> i32 { return x; }\n";
    let mut h = build(&[("pkg.one", src.to_string())]);
    assert!(!h.rendered().is_empty(), "the cycle must be reported cold");
    let cold_cycle = h.rendered();

    h.edit(
        0,
        "pub struct B { pub a: A }",
        "pub struct B { pub a: i32 }",
    );
    h.assert_matches_cold("breaking the cycle at B");
    assert_eq!(h.rendered(), Vec::<String>::new());

    h.edit(
        0,
        "pub struct B { pub a: i32 }",
        "pub struct B { pub a: A }",
    );
    h.assert_matches_cold("re-introducing the cycle at B");
    assert_eq!(h.rendered(), cold_cycle);

    h.edit(
        0,
        "pub struct A { pub b: B }",
        "pub struct A { pub b: i32 }",
    );
    h.assert_matches_cold("breaking the cycle at A");
    assert_eq!(h.rendered(), Vec::<String>::new());
}

/// A struct that gains a field a body reads, and loses it again: the body's
/// diagnostic must track the signature edit in both directions.
#[test]
fn a_field_removed_from_a_struct_breaks_its_readers_incrementally() {
    let mut h = build(&[("pkg.one", ONE.to_string())]);
    h.edit(
        0,
        "pub struct Rec { pub a: i32, pub b: i32 }",
        "pub struct Rec { pub b: i32 }",
    );
    h.assert_matches_cold("removing the field `a`");
    assert!(!h.rendered().is_empty(), "`go` reads `self.a`");
    h.edit(
        0,
        "pub struct Rec { pub b: i32 }",
        "pub struct Rec { pub a: i32, pub b: i32 }",
    );
    h.assert_matches_cold("restoring it");
    assert_eq!(h.rendered(), Vec::<String>::new());
}

/// A trait's method is renamed: a body calling the OLD name through the trait
/// must be woken (R43's candidate scan reads the impl's signature; the member
/// index of the receiver changes).
#[test]
fn renaming_a_trait_method_breaks_its_callers_incrementally() {
    let mut h = build(&[("pkg.one", ONE.to_string())]);
    h.edit(
        0,
        "pub trait Tr { fn go(let self) -> i32; }\n\nimpl Tr for Rec { fn go(let self: Rec) -> i32 { return self.a; } }",
        "pub trait Tr { fn run(let self) -> i32; }\n\nimpl Tr for Rec { fn run(let self: Rec) -> i32 { return self.a; } }",
    );
    h.assert_matches_cold("renaming the trait method");
    assert!(!h.rendered().is_empty(), "`calls_go` calls `r.go()`");
    assert!(
        h.bodies().contains(&"calls_go".to_string()),
        "{:?}",
        h.bodies()
    );
}

/// §9.2's last row with a body that probes the prelude's builtin buckets
/// (`x + 1` on `i32`, a method call): inserting a declaration above renumbers
/// every `DefId`, including the builtin impl rows declared after the user's,
/// and none of that may reach a bucket's value.
#[test]
fn inserting_a_declaration_above_does_not_wake_bodies_that_probed_builtin_buckets() {
    let src = "module pkg.one;\n\npub struct Rec { pub a: i32 }\n\npub trait Tr { fn go(let self) -> i32; }\n\nimpl Tr for Rec { fn go(let self: Rec) -> i32 { return self.a + 1; } }\n\npub fn arith(let x: i32) -> i32 { return x + 1; }\n\npub fn calls(let r: Rec) -> i32 { return r.go() * 2; }\n";
    let mut h = build(&[("pkg.one", src.to_string())]);
    assert_eq!(h.rendered(), Vec::<String>::new());
    h.edit(
        0,
        "module pkg.one;\n",
        "module pkg.one;\n\npub fn inserted(let x: i32) -> i32 { return x; }\n",
    );
    assert_eq!(h.bodies(), names(&["inserted"]), "insertion above");
    assert_eq!(h.signatures(), names(&["inserted"]), "insertion above");
    // And a second insertion, now that every bucket node exists and has been
    // verified once at the new numbering.
    h.edit(
        0,
        "pub fn inserted(let x: i32) -> i32 { return x; }\n",
        "pub fn inserted(let x: i32) -> i32 { return x; }\n\npub fn inserted2(let x: i32) -> i32 { return x; }\n",
    );
    assert_eq!(h.bodies(), names(&["inserted2"]), "second insertion above");
    h.assert_matches_cold("two insertions above");
}

/// §9.2 row 6 followed by row 8: the `(Keyed, Rec)` bucket's merkle moves
/// with the impl's `type Key` edit — at THAT revision, not at the next one
/// that happens to re-execute the bucket. The sequence is what caught
/// `impls_for` having no in-edge for its rows' signatures.
#[test]
fn an_assoc_type_edit_moves_its_bucket_at_once_not_at_the_next_impl_heads_change() {
    let src = "module pkg.one;\n\npub struct Rec { pub a: i32 }\n\npub struct Other { pub a: i32 }\n\npub trait Tr { fn go(let self) -> i32; }\n\npub trait Keyed { type Key: Eq + Ord; fn key(let self) -> Self.Key; }\n\nimpl Keyed for Rec {\n    type Key = i64;\n    fn key(let self: Rec) -> Self.Key { return 1; }\n}\n\npub fn tail(let x: i32) -> i32 { return x; }\n\npub fn uses_key(let r: Rec) -> i32 { let k = r.key(); return 0; }\n";
    let mut h = build(&[("pkg.one", src.to_string())]);
    h.edit(0, "type Key = i64;", "type Key = i32;");
    assert!(
        h.bodies().contains(&"uses_key".to_string()),
        "the body that normalised through the bucket: {:?}",
        h.bodies()
    );
    let before = h.qb.stats().nodes;
    h.edit(
        0,
        "pub fn tail",
        "impl Tr for Other { fn go(let self: Other) -> i32 { return self.a; } }\n\npub fn tail",
    );
    assert!(
        !h.bodies().contains(&"uses_key".to_string()),
        "an impl for `Other` must not wake a body about `Rec`: {:?}",
        h.bodies()
    );
    assert!(h.qb.stats().nodes >= before);
    h.assert_matches_cold("the two edits");
}

/// Adding a file to the build, importing it, then removing it: `module_graph`
/// and every node keyed by module must see the new file.
#[test]
fn adding_a_file_then_importing_and_removing_it_matches_cold() {
    let core = "module pkg.core;\n\npub struct Rec { pub a: i32 }\n\npub fn mk(let r: Rec) -> i32 { return r.a; }\n";
    let app = "module pkg.app;\nuse pkg.core, pkg.core.Rec, pkg.core.mk;\n\npub fn f(let r: Rec) -> i32 { return mk(r); }\n";
    let mut h = build(&[("pkg.core", core.to_string()), ("pkg.app", app.to_string())]);
    let extra = h.add(
        "pkg.extra",
        "module pkg.extra;\nuse pkg.core, pkg.core.Rec;\n\npub trait Ext { fn ext(let self) -> i32; }\n\nimpl Ext for Rec { fn ext(let self: Rec) -> i32 { return self.a; } }\n",
    );
    h.assert_matches_cold("adding a file");
    h.edit(
        1,
        "use pkg.core, pkg.core.Rec, pkg.core.mk;\n\npub fn f(let r: Rec) -> i32 { return mk(r); }",
        "use pkg.core, pkg.core.Rec, pkg.core.mk, pkg.extra, pkg.extra.Ext;\n\npub fn f(let r: Rec) -> i32 { return mk(r) + r.ext(); }",
    );
    h.assert_matches_cold("importing the new file");
    assert_eq!(h.rendered(), Vec::<String>::new());
    h.remove(extra);
    h.assert_matches_cold("removing the file again");
    assert!(
        !h.rendered().is_empty(),
        "`pkg.app` now imports from an empty module"
    );
}

/// Two mutually recursive structs added in ONE edit: `infinite_size()` had
/// no `size_edges` edge to either, so only the declaration set can wake it.
#[test]
fn two_new_mutually_recursive_structs_are_reported_at_once() {
    let src = "module pkg.one;\n\npub fn f(let x: i32) -> i32 { return x; }\n";
    let mut h = build(&[("pkg.one", src.to_string())]);
    assert_eq!(h.rendered(), Vec::<String>::new());
    h.edit(
        0,
        "pub fn f",
        "pub struct A { pub b: B }\n\npub struct B { pub a: A }\n\npub fn f",
    );
    h.assert_matches_cold("adding a cycle of two new structs");
    assert!(!h.rendered().is_empty(), "the cycle must be reported");
    h.edit(
        0,
        "pub struct A { pub b: B }\n\npub struct B { pub a: A }\n\n",
        "",
    );
    h.assert_matches_cold("removing both");
    assert_eq!(h.rendered(), Vec::<String>::new());
}

// ------------------------------------------------------- early cutoff, exact

/// §9.2's last-but-one row: a signature re-spelled without a change to its
/// canonical hash re-executes `signature_of(f)` and nothing that depends on
/// `f`. Here through a qualified path instead of an imported name.
#[test]
fn a_respelled_signature_reexecutes_only_its_own_nodes() {
    let core = "module pkg.core;\n\npub struct Rec { pub a: i32 }\n\npub fn mk(let r: Rec) -> i32 { return r.a; }\n";
    let app = "module pkg.app;\nuse pkg.core, pkg.core.Rec, pkg.core.mk;\n\npub fn f(let r: Rec) -> i32 { return mk(r); }\n\npub fn g(let r: Rec) -> i32 { return f(r); }\n";
    let mut h = build(&[("pkg.core", core.to_string()), ("pkg.app", app.to_string())]);
    assert_eq!(h.rendered(), Vec::<String>::new());
    h.edit(
        1,
        "use pkg.core, pkg.core.Rec, pkg.core.mk;\n\npub fn f(let r: Rec) -> i32",
        "use pkg.core, pkg.core.Rec, pkg.core.mk, pkg.core.Rec as R;\n\npub fn f(let r: R) -> i32",
    );
    h.assert_matches_cold("re-spelling a parameter type through an alias");
    assert_eq!(h.signatures(), names(&["f"]), "only `f` re-lowers");
    assert_eq!(
        h.bodies(),
        names(&["f"]),
        "`g` depends on `f`'s unchanged canonical hash and must stay green"
    );
}

/// An edit and its revert leave every dependent green both times.
#[test]
fn an_edit_and_revert_of_a_public_signature_wakes_dependents_exactly_twice() {
    let mut h = build(&[("pkg.one", ONE.to_string())]);
    h.edit(
        0,
        "pub struct Rec { pub a: i32, pub b: i32 }",
        "pub struct Rec { pub a: i32, pub b: i32, pub c: i32 }",
    );
    let first = (h.signatures(), h.bodies());
    assert_eq!(first.0, names(&["Rec"]));
    assert!(!first.1.contains(&"independent".to_string()));
    h.edit(
        0,
        "pub struct Rec { pub a: i32, pub b: i32, pub c: i32 }",
        "pub struct Rec { pub a: i32, pub b: i32 }",
    );
    assert_eq!(
        (h.signatures(), h.bodies()),
        first,
        "the revert is the same set"
    );
    h.assert_matches_cold("edit and revert");
    // A third, no-op recheck executes nothing.
    h.qb.open_window();
    h.recheck();
    assert_eq!(h.qb.executed_keys(), &[]);
}

// ------------------------------------------------------------- determinism

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
                // Every third group is broken, so the output has content.
                if i % 3 == 2 {
                    let _ = writeln!(
                        s,
                        "pub fn bad{m}_{i}(let r: Rec{m}_{i}) -> i32 {{ return r.nosuch; }}"
                    );
                }
            }
            (format!("pkg.m{m}"), s)
        })
        .collect()
}

/// A tiny deterministic LCG, so the shuffles are reproducible.
fn shuffle<T>(v: &mut [T], seed: u64) {
    let mut x = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    for i in (1..v.len()).rev() {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let j = (x >> 33) as usize % (i + 1);
        v.swap(i, j);
    }
}

#[test]
fn twenty_file_order_permutations_render_identically() {
    let files = generated(6, 4);
    let base = {
        let owned: Vec<(&str, String)> =
            files.iter().map(|(a, b)| (a.as_str(), b.clone())).collect();
        build(&owned)
    };
    let expected = base.rendered();
    assert!(
        !expected.is_empty(),
        "the corpus has diagnostics to compare"
    );
    for seed in 1..=20u64 {
        let mut perm = files.clone();
        shuffle(&mut perm, seed);
        let owned: Vec<(&str, String)> =
            perm.iter().map(|(a, b)| (a.as_str(), b.clone())).collect();
        let h = build(&owned);
        assert_eq!(h.rendered(), expected, "file-order permutation {seed}");
    }
}

#[test]
fn twenty_declaration_order_permutations_give_the_same_diagnostic_multiset() {
    let (name, src) = &generated(1, 6)[0];
    let header = "module pkg.m0;\n";
    let body = src.strip_prefix(header).unwrap();
    // Split into declarations at blank lines; each group stays intact.
    let groups: Vec<String> = body.split("\n\n").map(|s| s.to_string()).collect();
    let strip = |h: &H| -> Vec<String> {
        let mut v: Vec<String> =
            h.qb.diagnostics()
                .iter()
                .map(|d| format!("{} (site {}) {}", d.code.as_string(), d.site, d.message))
                .collect();
        v.sort();
        v
    };
    let expected = strip(&build(&[(name.as_str(), src.clone())]));
    assert!(!expected.is_empty());
    for seed in 1..=20u64 {
        let mut g = groups.clone();
        shuffle(&mut g, seed);
        let permuted = format!("{header}{}", g.join("\n\n"));
        let h = build(&[(name.as_str(), permuted)]);
        assert_eq!(strip(&h), expected, "declaration-order permutation {seed}");
    }
}

#[test]
fn two_cold_runs_execute_the_same_counters_per_kind() {
    let files = generated(5, 5);
    let owned: Vec<(&str, String)> = files.iter().map(|(a, b)| (a.as_str(), b.clone())).collect();
    let a = build(&owned);
    let b = build(&owned);
    assert_eq!(a.qb.stats().by_kind, b.qb.stats().by_kind);
    assert_eq!(a.qb.stats().nodes, b.qb.stats().nodes);
    assert_eq!(a.qb.stats().dep_edges, b.qb.stats().dep_edges);
    // And the same edit on each executes the same set, key for key.
    let mut a = a;
    let mut b = b;
    let from = "pub fn read2_1(let r: Rec2_1) -> i32 { return r.b; }";
    let to = "pub fn read2_1(let r: Rec2_1) -> i32 { return r.b + 1; }";
    a.edit(2, from, to);
    b.edit(2, from, to);
    let mut ka = a.qb.executed_keys().to_vec();
    let mut kb = b.qb.executed_keys().to_vec();
    ka.sort_unstable();
    kb.sort_unstable();
    assert_eq!(ka, kb);
}

// ---------------------------------------------------- cancellation, mid-flight

/// A cancellation that lands in the MIDDLE of a re-check (from another
/// thread, as an LSP would) must leave the build recoverable: the next
/// re-check agrees with a cold build byte for byte.
#[test]
fn a_mid_flight_cancellation_is_recoverable() {
    let files = generated(8, 12);
    let owned: Vec<(&str, String)> = files.iter().map(|(a, b)| (a.as_str(), b.clone())).collect();
    let mut h = build(&owned);
    let flag = h.qb.cancel_flag();
    let mut saw_cancel = false;
    for round in 0..6u64 {
        let f = (round % 8) as usize;
        let (from, to) = if round % 2 == 0 {
            (
                "return r.b; }\npub fn call",
                "return r.b + 1; }\npub fn call",
            )
        } else {
            (
                "return r.b + 1; }\npub fn call",
                "return r.b; }\npub fn call",
            )
        };
        h.sources[f] = h.sources[f].replacen(from, to, 1);
        h.qb.edit_file(h.ids[f], h.sources[f].clone().into_bytes());
        let canceller = {
            let flag = flag.clone();
            std::thread::spawn(move || {
                std::thread::sleep(std::time::Duration::from_micros(300 * (round + 1)));
                flag.cancel();
            })
        };
        let r = h.qb.recheck();
        canceller.join().unwrap();
        saw_cancel |= r.is_err();
        flag.reset();
        h.recheck();
        h.assert_matches_cold(&format!("round {round} after a mid-flight cancellation"));
    }
    eprintln!("mid-flight cancellation observed at least once: {saw_cancel}");
}

// --------------------------------------------- the oracle over the whole corpus

fn repo_root() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
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

/// The ch09 oracle of `incremental.rs`, over EVERY chapter of the corpus.
#[test]
fn the_query_path_agrees_with_check_build_over_the_whole_conformance_corpus() {
    let root = repo_root().join("tests/conformance");
    let mut paths: Vec<std::path::PathBuf> = Vec::new();
    for ch in std::fs::read_dir(&root).expect("the corpus").flatten() {
        if !ch.path().is_dir() {
            continue;
        }
        for e in std::fs::read_dir(ch.path()).unwrap().flatten() {
            let p = e.path();
            if p.extension().is_some_and(|e| e == "fors") {
                paths.push(p);
            }
        }
    }
    paths.sort();
    assert!(paths.len() > 800, "the corpus is {} files", paths.len());

    let mut mismatches: Vec<String> = Vec::new();
    for p in &paths {
        let src = std::fs::read(p).expect("a corpus file");
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
                p.strip_prefix(&root).unwrap().display()
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "{} of {} corpus files disagree:\n{}",
        mismatches.len(),
        paths.len(),
        mismatches.join("\n")
    );
}
