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

/// A multi-module build: `(module name, source)` in the order given. The
/// package root is the first file. Returns `(code, module name)` per
/// diagnostic, so a test can say WHICH module spoke.
fn check_modules(files: &[(&str, &str)]) -> Vec<(String, String)> {
    let mut interner = Interner::new();
    let sources: Vec<Vec<u8>> = files
        .iter()
        .map(|(n, s)| format!("module {n};\nneeds {{ }};\n{s}").into_bytes())
        .collect();
    let names: Vec<Segments> = files
        .iter()
        .map(|(n, _)| vec![interner.intern(n.as_bytes())])
        .collect();
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    for (p, (n, _)) in parsed.iter().zip(files) {
        assert!(p.diags.is_empty(), "module {n} must parse: {:?}", p.diags);
    }
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(sources.iter())
        .zip(names.iter())
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s,
            name: n.clone(),
        })
        .collect();
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"pkg"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    out.diagnostics
        .iter()
        .map(|d| {
            (
                d.code.as_string(),
                files
                    .get(d.file.index())
                    .map(|(n, _)| (*n).to_string())
                    .unwrap_or_default(),
            )
        })
        .collect()
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

/// S1: on a 3+-segment greedy-path callee (`outer.inner.m()`) D4 records
/// the METHOD, not the intermediate field. Path resolution records the
/// field first-wins; the method resolution overwrites it.
#[test]
fn nested_receiver_records_method_not_field() {
    let c = check_source(
        "struct Inner { n: i64 }\nstruct Outer { inner: Inner }\nimpl Inner { fn get(let self: Inner) -> i64 { return self.n; } }\nfn f(let o: Outer) -> i64 { return o.inner.get(); }",
    );
    assert!(codes(&c).is_empty(), "got {:?}", codes(&c));
    let f = body_with_calls(&c, 1);
    let calls = calls_in(&c, f);
    assert_eq!(calls.len(), 1);
    let (def, owner) = match f.callee_of(calls[0]) {
        FactCallee::Method { def, owner } => (def, owner),
        other => panic!("`o.inner.get()` must resolve to a method, got {other:?}"),
    };
    // The callee NameExpr node carries the method resolution in D4: the
    // recorded head is the method's owner, not the intermediate field's
    // struct.
    let (start, end) = f.range();
    let paths: Vec<u32> = (start..end.min(c.kinds.len() as u32))
        .filter(|&n| {
            c.kinds[n as usize] == NodeKind::NameExpr
                && f.member_of(n) != fors_check::facts::MemberTarget::None
        })
        .collect();
    assert_eq!(paths.len(), 1, "exactly the callee records D4");
    match f.member_of(paths[0]) {
        fors_check::facts::MemberTarget::Field { head, .. } => assert_eq!(
            head, owner,
            "D4 must name the method owner, not the intermediate field head"
        ),
        other => panic!("expected a D4 field-shaped method record, got {other:?}"),
    }
    let _ = def;
}

/// S3: `(move x).m()` and `x.m()` with `sink self` produce exactly one
/// Move event with an ImplicitReceiver cause each (R46: they mean exactly
/// the same). Node ids differ between the forms, so the comparison is on
/// (kind, cause shape, place).
#[test]
fn explicit_and_implicit_receiver_moves_match() {
    use fors_check::tape::{Cause, UseKind};
    fn shape(f: &fors_check::facts::BodyFacts) -> Vec<(UseKind, bool, fors_check::tape::PlaceId)> {
        let mut out: Vec<_> = f
            .tape
            .events
            .iter()
            .map(|e| {
                (
                    e.kind,
                    matches!(e.cause, Cause::ImplicitReceiver { .. }),
                    e.place,
                )
            })
            .collect();
        out.sort_by_key(|(k, c, p)| (*k as u8, *c, p.0));
        out
    }
    let plain = check_source(
        "struct B { x: i64 }\nimpl B { fn finish(sink self: B) -> i64 { let p = self.x; discard self; return p; } }\nfn f(sink b: B) -> i64 { return b.finish(); }",
    );
    let moved = check_source(
        "struct B { x: i64 }\nimpl B { fn finish(sink self: B) -> i64 { let p = self.x; discard self; return p; } }\nfn f(sink b: B) -> i64 { return (move b).finish(); }",
    );
    assert!(codes(&plain).is_empty(), "got {:?}", codes(&plain));
    assert!(codes(&moved).is_empty(), "got {:?}", codes(&moved));
    let fp = body_with_calls(&plain, 1);
    let fm = body_with_calls(&moved, 1);
    // Exactly one implicit-receiver move in each form, on the same place.
    let mp = fp
        .tape
        .events
        .iter()
        .filter(|e| matches!(e.cause, Cause::ImplicitReceiver { .. }))
        .count();
    let mm = fm
        .tape
        .events
        .iter()
        .filter(|e| matches!(e.cause, Cause::ImplicitReceiver { .. }))
        .count();
    assert_eq!((mp, mm), (1, 1), "one implicit move per form");
    assert_eq!(
        shape(fp),
        shape(fm),
        "tapes must match between `x.m()` and `(move x).m()`"
    );
}

// ------------------------------------------- increment I4's gate (design §11)

/// design §11, "Fidelity's risk 2": R43's candidate traits come from the
/// MODULE GRAPH (ch08 R7), so the same `(receiver, method name)` resolves
/// differently in different modules of one build. The lookup memo is
/// therefore keyed by the requesting module, and this is the assertion
/// from outside: a three-module build in which `b` lacks the edge `a` has
/// must report in `b` and only in `b`, checked twice in one process and
/// with the modules presented in both orders.
#[test]
fn method_lookup_memo_is_module_keyed() {
    const LIB: &str = "pub struct W { pub n: i64 }";
    const T: &str = "use lib.W;\n\
         pub trait Tagged { fn tag(let self) -> i64; }\n\
         impl Tagged for W { fn tag(let self: W) -> i64 { return self.n; } }";
    // `a` has a direct edge to `t`, so `t`'s impl is a candidate there.
    const A: &str = "use lib.W;\nuse t.Tagged;\n\
         pub fn f(let w: W) -> i64 { return w.tag(); }";
    // `b` does not, so for `b` the table is complete without it: T0043.
    const B: &str = "use lib.W;\npub fn g(let w: W) -> i64 { return w.tag(); }";

    let forward = [("lib", LIB), ("t", T), ("a", A), ("b", B)];
    let reverse = [("lib", LIB), ("b", B), ("a", A), ("t", T)];
    let want = vec![("T0043".to_string(), "b".to_string())];
    for (label, files) in [("forward", &forward), ("reverse", &reverse)] {
        // Twice in one process: the second check must not inherit the
        // first's answer either.
        for pass in 1..=2 {
            let got = check_modules(files);
            assert_eq!(
                got, want,
                "{label} order, pass {pass}: the module without the edge must be \
                 the only one that reports (ch08 R7)"
            );
        }
    }
}
