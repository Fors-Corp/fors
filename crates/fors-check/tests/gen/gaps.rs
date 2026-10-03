//! Checker findings of the generator. Each `GAP` is a program the checker
//! ACCEPTS although it types a node `TY_ERROR` without a diagnostic, or never
//! types a declaration's initialiser at all: the generator does not emit such
//! a form (`body.rs`'s `EMIT_*` switches), and this file pins each with a
//! probe that must keep reproducing. (G1-G4 were such gaps until the I11
//! triage fixed them in the checker; they are `REGRESSIONS` now.) When a probe stops
//! reproducing the checker has been fixed: move it to `REGRESSIONS`, flip the
//! generator's switch and let the soundness run exercise the form.
//!
//! `REGRESSIONS` are the findings I11 fixed in the checker; each probe must
//! keep producing exactly the diagnostics listed.

use crate::run::check;

pub struct Gap {
    pub id: &'static str,
    pub what: &'static str,
    pub src: &'static str,
    /// How many `TY_ERROR` nodes the sweep must still find silent.
    pub silent_nodes_at_least: usize,
}

/// Every gap the generator found has been fixed (I11 triage): G1-G4 are in
/// `REGRESSIONS`. A new one goes here until the checker types its form.
pub const GAPS: &[Gap] = &[];

/// A program the checker accepts although a declaration's initialiser is
/// never typed; `None` since I11 fixed G4.
pub const G4: Option<(&str, &str)> = None;

/// `(id, what, source, the diagnostics the probe must produce)`.
pub const REGRESSIONS: &[(&str, &str, &str, &[&str])] = &[
    (
        "F1",
        "a statement inside a call's argument (a block expression) tripped the debug assertion `a call's Binding outlived the call`: the enclosing call's inference binding is legitimately live there",
        "module m;\n\nfn g(let a: i32) -> i32 {\n    return a;\n}\n\nfn f(let c: bool) -> i32 {\n    return g(if c { let x = 1; x } else { 2 });\n}\n",
        &[],
    ),
    (
        "F2",
        "a tuple variant named by a dot literal, `.vb(1)`, was synthesised and rejected (T0034) in every CHECK position",
        "module m;\n\nenum E0 {\n    va,\n    vb(i32),\n}\n\nfn f() -> E0 {\n    return .vb(1);\n}\n",
        &[],
    ),
    (
        "F3",
        "a parenthesised call with two arguments, `(g(a, 1))`, was typed as a 1-tuple because the comma scan covered the whole span, not just the parenthesis's own commas",
        "module m;\n\nfn g(let a: i32, let b: i32) -> i32 {\n    return a;\n}\n\nfn f(let a: i32) -> i32 {\n    return (g(a, 1));\n}\n",
        &[],
    ),
    (
        "F5",
        "a generic struct literal in a SYNTH position recorded a PLACE field's use after every later field's, so `S { f0: v.a, f2: v.eat() }` was reported as a use of `v.a` after the move that comes after it (O0004, a false rejection found by the clean run of seed 1030179)",
        "module m;\n\nstruct S0[T] {\n    f0: T,\n    f1: i32,\n    f2: T,\n    f3: bool,\n}\n\nimpl[T: Copyable] S0[T] {\n    fn n1(sink self: S0[T]) -> bool {\n        return false;\n    }\n}\n\nfn g0() {\n    var v1: S0[i16] = S0 { f0: 26, f1: 23, f2: 12, f3: true };\n    var v4 = S0 { f0: v1.f3, f1: 3, f2: v1.n1(), f3: false };\n}\n",
        &[],
    ),
    (
        "F6",
        "the same ordering fault in a generic CALL: `g4(v.f2, v.eat())` recorded the first argument's read after the second's move (seed 1139963)",
        "module m;\n\nstruct R {\n    a: i32,\n    b: i32,\n}\n\nimpl R {\n    fn eat(sink self: R) -> i32 {\n        return 1;\n    }\n}\n\nfn g4[T: Copyable](let p0: T, let p1: T) {\n}\n\nfn g5() {\n    var v0: R = R { a: 1, b: 2 };\n    g4(v0.a, v0.eat());\n}\n",
        &[],
    ),
    (
        "G5",
        "an undeclared method on a receiver whose type parameter carries a marker bound next to a user trait (`[T: Copyable + Tr0]`) was silent: the prelude's marker traits made the member table look incomplete, so the call node ended TY_ERROR in an accepted body (found by `call/method-unknown` on seed 9812)",
        "module m;\n\ntrait Tr0 {\n    fn m0_0(let self) -> i32;\n}\n\nfn gb[T: Copyable + Tr0](let p0: T) -> i32 {\n    return p0.zzmethod();\n}\n",
        &["T0043"],
    ),
    (
        "G1",
        "a struct literal with explicit type arguments, `S1[i32] { a: 1 }`, was accepted with its StructLit node typed TY_ERROR and no diagnostic: `struct_head` refused a bracketed head; R38(a) now binds the struct's own parameters from it",
        "module m;\n\nstruct S1[T] {\n    a: T,\n}\n\nfn f1() -> i32 {\n    let s: S1[i32] = S1[i32] { a: 1 };\n    return s.a;\n}\n",
        &[],
    ),
    (
        "G2",
        "a record-variant literal, `E0.vc { a: 1, b: true }`, was accepted with a silent TY_ERROR StructLit node: R34's struct-form variant construction is now typed against the variant's record fields",
        "module m;\n\nenum E0 {\n    va,\n    vc { a: i32, b: bool },\n}\n\nfn f2() -> E0 {\n    return E0.vc { a: 1, b: true };\n}\n",
        &[],
    ),
    (
        "G3",
        "`K0.wrap_as[i64]()` on a `const` receiver was accepted with silent TY_ERROR Bracket/CallExpr/NameExpr nodes: `is_method_path` admitted only a local head",
        "module m;\n\nconst K0: i32 = 5;\n\nfn f3() -> i64 {\n    return K0.wrap_as[i64]();\n}\n",
        &[],
    ),
    (
        "G4",
        "a `const`'s initialiser was never typed (`Wf::bodies_selected` visited `DeclKind::Fn` only, although design 7.1 phase 6 lists `const`), so `const K1: i32 = true;` was accepted",
        "module m;\n\nconst K1: i32 = true;\nconst K2: i32 = 2.5;\nconst K3: f64 = 1;\n",
        &["T0026", "T0027", "T0027"],
    ),
];

#[test]
fn known_gaps_still_reproduce() {
    for g in GAPS {
        let r = check(g.src, true);
        assert!(r.panic.is_none(), "{}: panicked", g.id);
        assert!(
            r.parse.is_empty() && r.resolve.is_empty(),
            "{}: the probe no longer parses/resolves: {:?} {:?}",
            g.id,
            r.parse,
            r.resolve
        );
        assert!(
            r.diags.is_empty() && r.silent.len() >= g.silent_nodes_at_least,
            "{} no longer reproduces (diagnostics {:?}, silent {:?}): the checker was fixed; move it to REGRESSIONS and enable the generator form. Gap: {}",
            g.id,
            r.diags.iter().map(|d| d.code.as_str()).collect::<Vec<_>>(),
            r.silent,
            g.what
        );
    }
    if let Some((id, src)) = G4 {
        let r = check(src, true);
        assert!(
            r.parse.is_empty() && r.resolve.is_empty() && r.diags.is_empty() && r.panic.is_none(),
            "{id} no longer reproduces ({:?}): const initialisers are now typed; mutate them too",
            r.diags.iter().map(|d| d.code.as_str()).collect::<Vec<_>>()
        );
    }
}

#[test]
fn fixed_findings_stay_fixed() {
    for (id, what, src, want) in REGRESSIONS {
        let r = check(src, true);
        assert!(
            r.panic.is_none() && r.parse.is_empty() && r.resolve.is_empty(),
            "{id}: probe is broken"
        );
        let got: Vec<&str> = r.diags.iter().map(|d| d.code.as_str()).collect();
        assert_eq!(&got, want, "{id} regressed: {what}");
        assert!(
            r.silent.is_empty(),
            "{id} regressed: silent TY_ERROR {:?}",
            r.silent
        );
    }
}
