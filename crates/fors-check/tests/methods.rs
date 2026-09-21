//! I4a (method-call resolution, R43-R46) probe tests: resolution hits
//! the right tier with the right convention, ambiguity and absence
//! report their codes, and the receiver use lands on the tape with R46's
//! cause. Corpus rows cover the multi-module edge rule; these cover the
//! lookup shape directly.

use fors_check::facts::FactCallee;
use fors_fir::sig::Conv;
use fors_fir::ty::PrimKind;
use fors_index::{Interner, Segments};
use fors_resolve::FileInput;
use fors_syntax::{NodeKind, parse_file};

struct Checked {
    out: fors_check::CheckOutput,
    kinds: Vec<NodeKind>,
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
    Checked { out, kinds }
}

fn codes(c: &Checked) -> Vec<String> {
    c.out
        .diagnostics
        .iter()
        .map(|d| d.code.as_string())
        .collect()
}

fn calls_in(c: &Checked, facts: &fors_check::facts::BodyFacts) -> Vec<u32> {
    let (start, end) = facts.range();
    (start..end.min(c.kinds.len() as u32))
        .filter(|&n| c.kinds[n as usize] == NodeKind::CallExpr)
        .collect()
}

/// The body holding exactly `n` calls (bodies are stored per typed
/// declaration, in no promised order).
fn body_with_calls(c: &Checked, n: usize) -> &fors_check::facts::BodyFacts {
    &c.out
        .facts
        .iter()
        .find(|(_, f)| calls_in(c, f).len() == n)
        .expect("one body holds the calls")
        .1
}

const COUNTER: &str = "struct Counter { n: i64 }\nimpl Counter { fn bump(inout self: Counter) { self.n = self.n + 1; } fn get(let self: Counter) -> i64 { return self.n; } }\nfn f(inout c: Counter) -> i64 { c.bump(); return c.get(); }";

#[test]
fn inherent_method_resolves_with_its_convention() {
    let mut c = check_source(COUNTER);
    assert!(codes(&c).is_empty(), "got {:?}", codes(&c));
    let i64_ty = c.out.fir.tys.prim(PrimKind::I64);
    // Bodies are stored per typed declaration; find `f` by its two calls.
    let f = body_with_calls(&c, 2);
    let calls = calls_in(&c, f);
    assert_eq!(calls.len(), 2);
    for call in &calls {
        assert!(
            matches!(f.callee_of(*call), FactCallee::Method { .. }),
            "call {call} must resolve to a method"
        );
    }
    // `bump` takes `inout self`, `get` takes `let self`: D3 records both.
    let mut convs: Vec<Conv> = calls.iter().map(|&n| f.recv_conv_of(n).unwrap()).collect();
    convs.sort_by_key(|c| *c as u8);
    assert_eq!(convs, vec![Conv::Let, Conv::Inout]);
    // The receiver is not an argument: one conv row per call, and the
    // `bump()` row is empty.
    assert_eq!(f.arg_convs.len(), 2);
    for (node, convs) in &f.arg_convs {
        assert!(calls.contains(node));
        assert!(convs.is_empty(), "receiver takes no argument slot");
    }
    assert_eq!(f.ty_of(calls[1]), i64_ty, "`c.get()` is i64");
}

#[test]
fn sink_receiver_moves_implicitly_on_tape() {
    let c = check_source(
        "struct B { x: i64 }\nimpl B { fn finish(sink self: B) -> i64 { let p = self.x; discard self; return p; } }\nfn f(sink b: B) -> i64 { return b.finish(); }",
    );
    assert!(codes(&c).is_empty(), "got {:?}", codes(&c));
    let f = body_with_calls(&c, 1);
    let calls = calls_in(&c, f);
    assert_eq!(calls.len(), 1);
    assert_eq!(f.recv_conv_of(calls[0]), Some(Conv::Sink));
    let moves = f
        .tape
        .events
        .iter()
        .filter(|e| matches!(e.cause, fors_check::tape::Cause::ImplicitReceiver { .. }))
        .count();
    assert_eq!(moves, 1, "exactly the implicit receiver move");
}

#[test]
fn unknown_method_is_t0043_and_ambiguity_is_t0044() {
    let c = check_source("struct Tag { n: i64 }\nfn f(let t: Tag) -> i64 { return t.id(); }");
    assert_eq!(codes(&c), vec!["T0043"]);
    let c = check_source(
        "trait A { fn id(let self) -> i64; }\ntrait B { fn id(let self) -> i64; }\nfn f[T: A + B](let t: T) -> i64 { return t.id(); }",
    );
    assert_eq!(codes(&c), vec!["T0044"]);
}

#[test]
fn qualified_form_calls_with_receiver_as_arg() {
    let mut c = check_source(
        "struct C { r: f64 }\nimpl C { fn twice(let self: C) -> f64 { return self.r + self.r; } }\nfn total(let c: C) -> f64 { return C.twice(c); }",
    );
    assert!(codes(&c).is_empty(), "got {:?}", codes(&c));
    let f64_ty = c.out.fir.tys.prim(PrimKind::F64);
    let f = body_with_calls(&c, 1);
    let calls = calls_in(&c, f);
    assert_eq!(calls.len(), 1);
    assert!(
        matches!(f.callee_of(calls[0]), FactCallee::Method { .. }),
        "qualified call must resolve to the method"
    );
    assert_eq!(f.ty_of(calls[0]), f64_ty);
    // The receiver is an ordinary first argument here: one arg conv row
    // with the `let` convention of `twice`'s parameter.
    assert_eq!(f.arg_convs.len(), 1);
    assert_eq!(f.arg_convs[0].1, vec![Conv::Let]);
}
