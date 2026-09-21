//! I3.5 (`BodyFacts`) gate tests: the typed side table FMIR lowering
//! reads is complete, exact and deterministic, and recording changes no
//! diagnostic.
//!
//! The pin `TYPED_NODES_SIMPLE` counts every `synth`/`check` return on the
//! fixture program below. It is a change detector by design: a judgement
//! that stops visiting a node, or a wrapper that stops recording, moves
//! the number and fails loudly here instead of starving lowering
//! silently. Re-pin it only alongside a judgement change, never to make
//! red green.

use fors_check::facts::{FactCallee, MemberTarget};
use fors_fir::ty::{PrimKind, TY_ERROR, TyTag};
use fors_index::{Interner, Segments};
use fors_resolve::FileInput;
use fors_syntax::{NodeKind, parse_file};

struct Checked {
    out: fors_check::CheckOutput,
    kinds: Vec<NodeKind>,
    kids: Vec<Vec<usize>>,
}

fn check_source(src: &str) -> Checked {
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(
        parsed.diags.is_empty(),
        "fixture must parse: {:?}\n{}",
        parsed.diags,
        String::from_utf8_lossy(&bytes)
    );
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let kinds = parsed.tree.kinds.to_vec();
    let kids = (0..kinds.len())
        .map(|i| parsed.tree.children(i).collect())
        .collect();
    Checked { out, kinds, kids }
}

/// Nodes of `kind` inside the body's range, in source order.
fn nodes_of(c: &Checked, start: u32, end: u32, kind: NodeKind) -> Vec<u32> {
    (start..end.min(c.kinds.len() as u32))
        .filter(|&n| c.kinds[n as usize] == kind)
        .collect()
}

const SIMPLE: &str = "struct P { x: i32 }\nfn id(let a: i32) -> i32 { return a; }\nfn f(let p: P) -> i32 { let y = id(1); return p.x + y; }";

/// Every `synth`/`check` return on [`SIMPLE`] is recorded, one entry per
/// distinct node (a `check` that falls back to `synth` on the same node
/// records twice; last write wins, so it counts once). Counted against
/// the dispatch: `id`'s body contributes 1 (the `a` operand, checked then
/// synthesised) and `f`'s body contributes 5 (the `id(1)` call, its `1`
/// argument, the `+`, the greedy-path `p.x` operand and the `y` operand).
/// Re-pin with a judgement change only.
const TYPED_NODES_SIMPLE: usize = 6;

#[test]
fn body_facts_cover_every_typed_node() {
    let c = check_source(SIMPLE);
    assert!(
        c.out.diagnostics.is_empty(),
        "fixture must check clean: {:?}",
        c.out.diagnostics
    );
    assert_eq!(c.out.facts.len(), 2);
    let total: usize = c.out.facts.iter().map(|(_, f)| f.typed_nodes()).sum();
    assert_eq!(total, TYPED_NODES_SIMPLE, "recorded node count moved");

    // D2 is total: every call node in either body has a classification, and
    // the one real call resolves to its `fn` item with its argument's
    // convention recorded (D3).
    for (_, facts) in &c.out.facts {
        let (start, end) = facts.range();
        for n in nodes_of(&c, start, end, NodeKind::CallExpr) {
            assert_ne!(
                facts.callee_of(n),
                FactCallee::None,
                "call node {n} has no recorded callee"
            );
        }
    }
    let (_, f) = &c.out.facts[1];
    let (start, end) = f.range();
    let calls = nodes_of(&c, start, end, NodeKind::CallExpr);
    assert_eq!(calls.len(), 1);
    match f.callee_of(calls[0]) {
        FactCallee::Direct(_) => {}
        other => panic!("`id(1)` must resolve Direct, got {other:?}"),
    }
    assert_eq!(f.arg_convs.len(), 1, "one typed call, one conv row");
    assert_eq!(f.arg_convs[0].0, calls[0]);
    assert_eq!(f.arg_convs[0].1.len(), 1, "one argument, one convention");

    // D4: the `p.x` read resolves to (P, field 0). The parser builds it
    // as one greedy-path NameExpr (ch07), so the member lands on that
    // node via `path_value` -> `member_of`, not on a FieldExpr.
    let paths = nodes_of(&c, start, end, NodeKind::NameExpr);
    let resolved: Vec<u32> = paths
        .iter()
        .copied()
        .filter(|&n| f.member_of(n) != MemberTarget::None)
        .collect();
    assert_eq!(resolved.len(), 1, "exactly the `p.x` path resolves");
    match f.member_of(resolved[0]) {
        MemberTarget::Field { index: 0, .. } => {}
        other => panic!("`p.x` must resolve to field 0, got {other:?}"),
    }

    // The tape is retained in the facts table, not dropped with the
    // context: bindings and moves are still there for the flow pass.
    assert!(
        !f.tape.events.is_empty(),
        "retained tape must carry the body's use events"
    );
}

#[test]
fn facts_name_exact_types() {
    let mut c = check_source(SIMPLE);
    assert!(c.out.diagnostics.is_empty());
    let i32 = c.out.fir.tys.prim(PrimKind::I32);
    let (_, f) = &c.out.facts[1];
    let (start, end) = f.range();
    let lits = nodes_of(&c, start, end, NodeKind::Literal);
    assert!(!lits.is_empty());
    for n in lits {
        assert_eq!(f.ty_of(n), i32, "integer literal node {n} must be i32");
    }
    let adds = nodes_of(&c, start, end, NodeKind::AddExpr);
    assert_eq!(adds.len(), 1);
    assert_eq!(f.ty_of(adds[0]), i32, "`p.x + y` must be i32");
    let paths = nodes_of(&c, start, end, NodeKind::NameExpr);
    let read = paths
        .iter()
        .copied()
        .find(|&n| f.member_of(n) != MemberTarget::None)
        .expect("the `p.x` path resolves");
    assert_eq!(f.ty_of(read), i32, "`p.x` must be i32");
    let calls = nodes_of(&c, start, end, NodeKind::CallExpr);
    assert_eq!(f.ty_of(calls[0]), i32, "`id(1)` must be i32");
    // The callee operand itself is never typed (classification reads the
    // resolver, not the judgement): the `id` NameExpr under the call keeps
    // NO_TY, honestly unvisited rather than guessed.
    let calls = nodes_of(&c, start, end, NodeKind::CallExpr);
    for call in calls {
        let operand = c.kids[call as usize]
            .iter()
            .find(|&&k| c.kinds[k] == NodeKind::NameExpr)
            .expect("a direct call's callee is a NameExpr");
        assert_eq!(
            f.ty_of(*operand as u32),
            fors_fir::ty::NO_TY,
            "callee operand must stay unvisited, not guessed"
        );
    }
}

#[test]
fn facts_are_deterministic() {
    let a = check_source(SIMPLE);
    let b = check_source(SIMPLE);
    assert_eq!(a.out.facts.len(), b.out.facts.len());
    for ((_, fa), (_, fb)) in a.out.facts.iter().zip(b.out.facts.iter()) {
        assert_eq!(fa.typed_nodes(), fb.typed_nodes());
        assert_eq!(format!("{fa:?}"), format!("{fb:?}"));
    }
}

#[test]
fn facts_survive_errors() {
    // A mistyped operand poisons the operation, not the table: the `+`
    // node is recorded `TY_ERROR` and the clean call beside it keeps its
    // callee and type.
    let mut c = check_source(
        "fn id(let a: i32) -> i32 { return a; }\nfn f() -> i32 { let y = id(1); return 1 + true; }",
    );
    assert!(!c.out.diagnostics.is_empty(), "fixture must actually err");
    let i32 = c.out.fir.tys.prim(PrimKind::I32);
    let bool_ty = c.out.fir.tys.prim(PrimKind::Bool);
    let (_, f) = &c.out.facts[1];
    let (start, end) = f.range();
    let adds = nodes_of(&c, start, end, NodeKind::AddExpr);
    assert_eq!(adds.len(), 1);
    assert_eq!(
        f.ty_of(adds[0]),
        TY_ERROR,
        "the mistyped `+` must be recorded absorbing"
    );
    assert_ne!(f.ty_of(adds[0]), bool_ty);
    let calls = nodes_of(&c, start, end, NodeKind::CallExpr);
    assert_eq!(calls.len(), 1);
    assert_eq!(f.ty_of(calls[0]), i32);
    assert!(matches!(f.callee_of(calls[0]), FactCallee::Direct(_)));
    // No tag other than the store's own may leak through the table.
    let (s, e) = f.range();
    for n in s..e {
        let t = f.ty_of(n);
        if t != fors_fir::ty::NO_TY {
            let tag = c.out.fir.tys.tag(c.out.fir.tys.unqual(t));
            assert!(
                !matches!(tag, TyTag::Error) || t == TY_ERROR,
                "node {n} carries a qualified error"
            );
        }
    }
}
