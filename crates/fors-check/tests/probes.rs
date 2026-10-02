//! Fresh violation programs from the I2/I3 verification (2026-09-20): each
//! one violates a rule in a way the conformance corpus does not, so that a
//! rule marked `Implemented` is enforced for its OWN reason. A program is a
//! single module `m`; the expectation is the exact list of checker codes
//! (resolver codes are not this harness's business).
//!
//! MARC: these live beside the corpus rather than in it because
//! `tests/conformance/**` is the spec's and is not this increment's to
//! extend; a case that the corpus later covers may be deleted here.

use fors_index::{Interner, Segments};
use fors_resolve::FileInput;
use fors_syntax::parse_file;

fn check_source(src: &str) -> Vec<String> {
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(
        parsed.diags.is_empty(),
        "probe must parse: {:?}\n{}",
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
    out.diagnostics.iter().map(|d| d.code.as_string()).collect()
}

/// `check_source` with the messages, for a probe that must tell two
/// diagnostics of the same code apart by WHAT they name.
fn check_messages(src: &str) -> Vec<String> {
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(
        parsed.diags.is_empty(),
        "probe must parse: {:?}",
        parsed.diags
    );
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    out.diagnostics
        .iter()
        .map(|d| format!("{}: {}", d.code.as_string(), d.message))
        .collect()
}

/// `check_source` with each diagnostic's 1-based LINE in the source as
/// `check_source` builds it (its two header lines included), for a test
/// whose expectation is WHICH arm a diagnostic lands on.
fn check_source_lines(src: &str) -> Vec<(String, u32)> {
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(
        parsed.diags.is_empty(),
        "probe must parse: {:?}\n{}",
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
    out.diagnostics
        .iter()
        .map(|d| {
            let line = bytes[..d.start as usize]
                .iter()
                .filter(|&&b| b == b'\n')
                .count() as u32
                + 1;
            (d.code.as_string(), line)
        })
        .collect()
}

/// A multi-module build, `(module name, source)` in the order given, the
/// first being the package root; `(code, module name)` per diagnostic.
fn check_modules(files: &[(&str, &str)]) -> Vec<(String, String)> {
    let mut interner = Interner::new();
    let sources: Vec<Vec<u8>> = files
        .iter()
        .map(|(n, s)| format!("module {n};\n{s}").into_bytes())
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

struct Probe {
    name: &'static str,
    want: &'static [&'static str],
    src: &'static str,
}

const PROBES: &[Probe] = &[
    // ---------------------------------------------------------------- I2
    Probe {
        name: "r11_type_in_const_slot",
        want: &["T0011"],
        src: "fn f(let a: Array[i32, i32]) { }",
    },
    Probe {
        name: "r13_bool_in_usize_slot",
        want: &["T0013"],
        src: "fn f(let a: Array[i32, true]) { }",
    },
    Probe {
        name: "r13_negative_in_usize_slot",
        want: &["T0013"],
        src: "fn f(let a: Array[i32, -1]) { }",
    },
    Probe {
        name: "r13_fit_is_declaration_order_independent_fn_first",
        want: &["T0013"],
        src: "fn f(let x: S[300]) { }\nstruct S[N: u8] { a: Array[i32, 2] }",
    },
    Probe {
        name: "r13_fit_is_declaration_order_independent_struct_first",
        want: &["T0013"],
        src: "struct S[N: u8] { a: Array[i32, 2] }\nfn f(let x: S[300]) { }",
    },
    Probe {
        name: "r13_fit_ok",
        want: &[],
        src: "fn f(let x: S[200]) { }\nstruct S[N: u8] { a: Array[i32, 2] }",
    },
    Probe {
        name: "r17_parameter_name_differs",
        want: &["T0017"],
        src: "trait Tr { fn m(let self, let a: i32); }\nstruct S { x: i32 }\nimpl Tr for S { fn m(let self, let b: i32) { } }",
    },
    Probe {
        name: "r17_raises_differs",
        want: &["T0017"],
        src: "enum E { boom }\ntrait Tr { fn m(let self) raises E; }\nstruct S { x: i32 }\nimpl Tr for S { fn m(let self) { } }",
    },
    Probe {
        name: "r17_generic_parameter_count_differs",
        want: &["T0017"],
        src: "trait Tr { fn m(let self); }\nstruct S { x: i32 }\nimpl Tr for S { fn m[T](let self) { } }",
    },
    Probe {
        name: "r17_index_impl_with_scoped_self_accepted",
        want: &[],
        src: "struct P { x: i32 }\nimpl Index[usize] for P { type Output = i32; fn at(let self, let i: usize) -> scoped(self) i32 { return self.x; } }",
    },
    Probe {
        name: "r14_cycle_through_associated_type",
        want: &["T0014"],
        src: "struct Foo { n: i32 }\nstruct S[I: Iterator] { x: I.Item }\nimpl Iterator for Foo { type Item = S[Foo]; fn next(inout self) -> Option[S[Foo]] { return none; } }",
    },
    Probe {
        name: "r19_overlap_reported_whichever_impl_is_first",
        want: &["T0019"],
        src: "struct W[T] { t: T }\nimpl Tr for W[i32] { fn m(let self) { } }\nimpl[T] Tr for W[T] { fn m(let self) { } }\ntrait Tr { fn m(let self); }",
    },
    // ---------------------------------------------------------------- I3
    Probe {
        name: "r29_unary_minus_needs_neg",
        want: &["T0029"],
        src: "fn f(let n: u32) { let x = -n; }",
    },
    Probe {
        name: "r29_negated_literal_against_unsigned",
        want: &["T0029"],
        src: "fn f() { let x: u8 = -1; }",
    },
    Probe {
        name: "r29_index_on_scalar",
        want: &["T0029"],
        src: "fn f(let n: i32) { let x = n[0]; }",
    },
    Probe {
        name: "r29_index_on_struct_without_impl",
        want: &["T0029"],
        src: "struct P { x: i32 }\nfn f(let p: P) { let c = p[0]; }",
    },
    Probe {
        name: "r47_bracket_after_non_generic_fn_item_indexes",
        want: &["T0029"],
        src: "fn g(let x: i32) -> i32 { return x; }\nfn f() { let y = g[0]; }",
    },
    Probe {
        name: "r30_range_operands_differ",
        want: &["T0030"],
        src: "fn f(let a: u8, let b: u16) { let r = a ..< b; }",
    },
    Probe {
        name: "r31_tuple_binding_against_non_tuple",
        want: &["T0031"],
        src: "fn f() { let (a, b) = 1; }",
    },
    Probe {
        name: "r31_one_element_binding_is_the_value",
        want: &[],
        src: "fn f() { let (a) = 1; }",
    },
    Probe {
        name: "r35_return_in_synth_closure",
        want: &["T0035"],
        src: "fn f() { let g = |let a: i32| { return a; }; }",
    },
    Probe {
        name: "r35_return_in_check_closure_uses_fn_result",
        want: &["T0026"],
        src: "fn f() { let g: fn(let i32) -> i32 = |a| { return true; }; }",
    },
    Probe {
        name: "r33_break_inside_closure_is_outside_loop",
        want: &["T0033"],
        src: "fn f() { for i in 0 ..< 3 { let g = || { break; }; } }",
    },
    Probe {
        name: "r36_question_on_non_raising_call",
        want: &["T0036"],
        src: "fn g() -> i32 { return 1; }\nfn f() -> i32 { return g()?; }",
    },
    Probe {
        name: "r36_handler_on_non_raising_call",
        want: &["T0036"],
        src: "fn g() -> i32 { return 1; }\nfn f() -> i32 { return g() else |e| { 0 }; }",
    },
    Probe {
        name: "r36_question_in_non_raising_fn",
        want: &["T0036"],
        src: "enum E { a }\nfn g() -> i32 raises E { return 1; }\nfn f() -> i32 { return g()?; }",
    },
    Probe {
        name: "r36_raise_in_non_raising_fn",
        want: &["T0036"],
        src: "enum E { a }\nfn f() { raise E.a; }",
    },
    Probe {
        name: "r36_question_on_a_local",
        want: &["T0036"],
        src: "fn f(let x: i32) -> i32 { return x?; }",
    },
    Probe {
        name: "r36_check_closure_raises_from_its_fn_type",
        want: &[],
        src: "enum E { a }\nfn g() -> i32 raises E { return 1; }\nfn f() { let h: fn(let i32) -> i32 raises E = |a| { return g()?; }; }",
    },
    Probe {
        name: "r37_spawn_needs_a_call",
        want: &["T0037"],
        src: "fn f() { spawn 1; }",
    },
    Probe {
        name: "r42_field_on_primitive",
        want: &["T0042"],
        src: "fn f(let n: i32) { let x = n.len; }",
    },
    // ---------------------------------------------------------- `never`
    Probe {
        name: "never_right_operand_under_literal_exception",
        want: &[],
        src: "fn die() -> never { while true { } }\nfn f() -> i32 { return 1 + die(); }",
    },
    Probe {
        name: "never_left_operand_absorbs",
        want: &[],
        src: "fn die() -> never { while true { } }\nfn f() -> i32 { return die() + 1; }",
    },
    Probe {
        name: "never_cast_source",
        want: &[],
        src: "fn die() -> never { while true { } }\nfn f() -> i32 { return die() as i32; }",
    },
    Probe {
        name: "never_range_bound",
        want: &[],
        src: "fn die() -> never { while true { } }\nfn f() { for i in 0 ..< die() { } }",
    },
    Probe {
        name: "never_first_array_element",
        want: &[],
        src: "fn die() -> never { while true { } }\nfn f() -> Array[i32, 2] { return [die(), 1]; }",
    },
    // ---------------------------------------------------------------- I7
    Probe {
        name: "r50_tuple_pattern_arity_mismatch_rejected",
        want: &["T0050"],
        src: "fn f(let p: (i32, i32)) -> i32 { match p { (let a, let b, let c) => a, } }",
    },
    Probe {
        name: "r50_variant_tuple_payload_arity_mismatch_rejected",
        want: &["T0050"],
        src: "enum E70 { V(i32, i32) }\nfn f(let e: E70) -> i32 { match e { E70.V(let a) => a, } }",
    },
    Probe {
        name: "r50_bool_literal_against_non_bool_rejected",
        want: &["T0050"],
        src: "fn f(let n: i32) -> i32 { match n { true => 1, _ => 0, } }",
    },
    Probe {
        name: "r51_let_binding_type_is_the_variants_own_substituted_argument",
        want: &["T0026"],
        src: "enum Box70[T] { Full(T) }\nfn f(let b: Box70[i64]) -> bool { match b { Box70.Full(let v) => { return v; } } }",
    },
    Probe {
        name: "r53_missing_payload_variant_names_the_gap_rejected",
        want: &["T0053"],
        src: "enum Shape70 { circle(f64), square(f64) }\nfn f(let s: Shape70) -> f64 { match s { .circle(let r) => r, } }",
    },
    Probe {
        name: "r53_struct_pattern_itself_is_always_exhaustive_accepted",
        want: &[],
        src: "struct P70 { x: i32, y: i32 }\nfn f(let p: P70) -> i32 { match p { P70 { x: let x, y: let y } => x + y, } }",
    },
    Probe {
        name: "r54_fully_wildcard_tuple_makes_a_later_concrete_arm_unreachable",
        want: &["T0054"],
        src: "fn f(let p: (bool, bool)) -> i32 { match p { (_, _) => 0, (true, true) => 1, } }",
    },
    Probe {
        name: "nested_explicit_generic_argument_is_checked",
        want: &["T0026"],
        src: "fn id70[T](let x: T) -> T { return x; }\nfn f() -> bool { return id70[Option[i64]](true); }",
    },
    Probe {
        name: "explicit_generic_argument_of_a_user_generic_struct_is_checked",
        want: &["T0026"],
        src: "struct Box71[T] { v: T }\nfn id71[T](let x: T) -> T { return x; }\nfn f(let b: Box71[i64]) -> bool { return id71[Box71[i64]](b); }",
    },
];

#[test]
fn fresh_violations_are_enforced_for_their_own_reason() {
    let mut failures = Vec::new();
    for p in PROBES {
        let got: Vec<String> = check_source(p.src)
            .into_iter()
            .filter(|c| c.starts_with('T'))
            .collect();
        if got != p.want {
            failures.push(format!("{}: want {:?}, got {:?}", p.name, p.want, got));
        }
    }
    assert!(
        failures.is_empty(),
        "probe failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The FIR pools' `u8`/`u16` length columns: a 256-parameter function, a
/// 256-parameter closure and a 65 536-element tuple each panicked before
/// the verification; now each is one diagnostic and no panic.
#[test]
fn implementation_limits_are_diagnostics_not_panics() {
    let params: Vec<String> = (0..300).map(|i| format!("let p{i}: i32")).collect();
    let src = format!("fn f({}) {{ }}", params.join(", "));
    assert_eq!(check_source(&src), vec!["T0007"]);

    let cparams: Vec<String> = (0..300).map(|i| format!("let p{i}: i32")).collect();
    let src = format!("fn f() {{ let g = |{}| 1; }}", cparams.join(", "));
    assert_eq!(check_source(&src), vec!["T0035"]);

    let elems = vec!["1"; 70_000].join(", ");
    let src = format!("fn f() {{ let t = ({elems}); }}");
    assert_eq!(check_source(&src), vec!["T0004"]);
}

// ------------------------------------------------ increment I4b's probes

/// R12's use side, metamorphically: the ONLY thing that decides the call
/// is whether an impl of the bound's trait exists for the argument's type.
/// Four variants of one program differing in exactly that, plus the
/// control that the generic's own body never speaks (R59: nothing inside
/// `show` depends on who calls it).
#[test]
fn bound_at_a_call_is_metamorphic_in_the_impl() {
    const DECLS: &str = "trait Named { fn id(let self) -> i32; }\n\
         struct Sq { s: i32 }\n\
         fn show[T: Named](let x: T) -> i32 { return 1; }\n";
    // (a) no impl of `Named` for `Sq`: the bound fails at the call.
    assert_eq!(
        check_source(&format!(
            "{DECLS}fn f() -> i32 {{ let q = Sq {{ s: 1 }}; return show(q); }}"
        )),
        vec!["T0012"],
        "an argument whose type has no impl of the bound's trait is T0012"
    );
    // (b) the SAME program with the impl added: silent. Nothing else moved.
    assert!(
        check_source(&format!(
            "{DECLS}impl Named for Sq {{ fn id(let self: Sq) -> i32 {{ return self.s; }} }}\n\
             fn f() -> i32 {{ let q = Sq {{ s: 1 }}; return show(q); }}"
        ))
        .is_empty(),
        "adding the impl must remove the diagnostic and add none"
    );
    // (c) the impl exists but for ANOTHER type: back to T0012, so (b) was
    // not an accident of the impl merely being present in the build.
    assert_eq!(
        check_source(&format!(
            "{DECLS}struct Tri {{ t: i32 }}\n\
             impl Named for Tri {{ fn id(let self: Tri) -> i32 {{ return self.t; }} }}\n\
             fn f() -> i32 {{ let q = Sq {{ s: 1 }}; return show(q); }}"
        )),
        vec!["T0012"],
        "an impl for a different head must not satisfy the bound"
    );
    // (d) the bounded parameter is not determined by any argument
    // position nor by the result: R39 (I5) reports it as undetermined, ONCE,
    // and the bound is not also checked on a slot that has no value — one
    // root cause, never a T0012 guessed from nothing.
    assert_eq!(
        check_source(&format!(
            "{DECLS}fn g[T: Named]() -> i32 {{ return 1; }}\nfn f() -> i32 {{ return g(); }}"
        )),
        vec!["T0039"],
        "an undetermined parameter is R39's T0039, not a bound violation"
    );
    // ...and given explicitly, the bound is checked with that value.
    assert_eq!(
        check_source(&format!(
            "{DECLS}fn g[T: Named]() -> i32 {{ return 1; }}\nfn f() -> i32 {{ return g[Sq](); }}"
        )),
        vec!["T0012"]
    );
    // (e) the generic itself never speaks, however many callers it has.
    let one = check_source(&format!(
        "{DECLS}fn f() -> i32 {{ let q = Sq {{ s: 1 }}; return show(q); }}"
    ));
    let two = check_source(&format!(
        "{DECLS}fn f() -> i32 {{ let q = Sq {{ s: 1 }}; return show(q); }}\n\
         fn h() -> i32 {{ let r = Sq {{ s: 2 }}; return show(r); }}"
    ));
    assert_eq!(one.len(), 1);
    assert_eq!(
        two.len(),
        2,
        "one diagnostic per CALLING declaration and none inside `show`: {two:?}"
    );
    assert!(two.iter().all(|c| c == "T0012"));
}

/// R43 on a PRIMITIVE head. The tiers are the whole method table for a
/// numeric primitive, so a name no surface can declare is T0043 — but the
/// two surfaces this increment does not model stay silent, and the
/// carve-out is by SURFACE, not by "primitives are exempt".
#[test]
fn a_primitive_receiver_reports_only_what_no_surface_can_declare() {
    // Nothing in the language or in `std` declares `count` on `usize`.
    assert_eq!(
        check_source("fn f(let n: usize) -> usize { return n.count(); }"),
        vec!["T0043"]
    );
    // ch03 R4's family is language-known and declared by no file (I10).
    for name in [
        "wrap_add",
        "sat_add",
        "unchecked_add",
        "wrap_rem",
        "sat_shr",
    ] {
        assert!(
            check_source(&format!(
                "fn f(let n: i32) -> i32 {{ return n.{name}(1); }}"
            ))
            .is_empty(),
            "ch03 R4's `{name}` must stay silent in a build with no ch03 surface"
        );
    }
    // The family is FINITE (ch03 R2's operators), not a name prefix: a
    // `wrap_` spelling of no trapping operator is an ordinary R43 miss.
    // (I4b verification: the first cut matched by prefix, so `wrap_foo`
    // was silently accepted.)
    for name in ["wrap_foo", "sat_", "unchecked_pow"] {
        assert_eq!(
            check_source(&format!(
                "fn f(let n: i32) -> i32 {{ return n.{name}(1); }}"
            )),
            vec!["T0043"],
            "`{name}` is not in ch03's family and must report"
        );
    }
    // `impl Str` is `std`'s (ch10 R26) and absent from this build.
    assert!(
        check_source("fn f(let s: Str) -> usize { return s.len(); }").is_empty(),
        "Str's inherent surface is std's; its absence proves nothing"
    );
    // The carve-out is per surface, not per receiver: a name that is
    // neither ch03 R4's shape nor on `Str` still reports on `i32`.
    assert_eq!(
        check_source("fn f(let n: i32) -> i32 { return n.wrapping_add(1); }"),
        vec!["T0043"],
        "`wrapping_add` is not ch03 R4's `wrap_<op>` spelling"
    );
    // A trait the primitive DOES implement still answers in tier (2), so
    // the primitive path is a real lookup and not a blanket rejection.
    assert!(
        check_source("fn f(let a: i32, let b: i32) -> bool { return a.eq(b); }").is_empty(),
        "`Eq.eq` is a prelude-trait method of every scalar"
    );
}

/// ch10 R34 / R43's inherent-before-trait precedence, shown by mutation:
/// the inherent `take` re-routes the call, and the only visible effect is
/// the type the next stage sees. Removing the inherent method removes the
/// diagnostic; renaming it removes it too.
#[test]
fn an_inherent_method_shadows_a_trait_one_and_only_the_name_decides() {
    const BASE: &str = "struct Src { n: usize }\n\
         impl Iterator for Src { type Item = i32; fn next(inout self: Src) -> Option[i32] { return none; } }\n";
    // The inherent `take` answers tier (1), so `.count()` runs on `usize`:
    // the fault is reported one stage LATER than the shadowing.
    assert_eq!(
        check_messages(&format!(
            "{BASE}impl Src {{ pub fn take(sink self: Src, let n: usize) -> usize {{ return n; }} }}\n\
             fn f(sink s: Src) -> usize {{ return s.take(3).count(); }}"
        )),
        vec!["T0043: `usize` has no method `count`"]
    );
    // Rename the inherent method and the SAME code is reported about a
    // different stage — `take` itself. Same code, different subject: the
    // probe above really was the re-routing and not the chain's tail.
    assert_eq!(
        check_messages(&format!(
            "{BASE}impl Src {{ pub fn grab(sink self: Src, let n: usize) -> usize {{ return n; }} }}\n\
             fn f(sink s: Src) -> usize {{ return s.take(3).count(); }}"
        )),
        vec!["T0043: `Src` has no method `take`"]
    );
    // Give the inherent method the receiver's own type back and the SAME
    // code again names a third subject: the diagnostic follows the
    // re-routed RESULT type, which is the whole content of ch10 R34's
    // warning. (`Src` has no `count` either: the `Iterator` row of a build
    // with no `std` declares `next` and nothing else.)
    assert_eq!(
        check_messages(&format!(
            "{BASE}impl Src {{ pub fn take(sink self: Src, let n: usize) -> Src {{ return Src {{ n: n }}; }} }}\n\
             fn f(sink s: Src) -> usize {{ return s.take(3).count(); }}"
        )),
        vec!["T0043: `Src` has no method `count`"]
    );
}

/// R29's "Several" clause, metamorphically in the NUMBER of impls: with
/// one `Index` impl `g[0]` checks the literal against that impl's `I`;
/// adding a second makes the index synthesised, so the same `g[0]` is
/// T0029 and `g[0usize]` is not. The point of the rule is that adding an
/// impl can BREAK `a[0]` but can never silently change what it meant.
#[test]
fn a_second_index_impl_breaks_a_bare_literal_index_and_nothing_else() {
    const G: &str = "struct Grid { cells: Array[i64, 16], names: Array[Str, 4] }\n";
    const ONE: &str = "impl Index[usize] for Grid {\n\
         type Output = i64;\n\
         fn at(let self: Grid, let i: usize) -> scoped(self) i64 { return self.cells[i]; }\n}\n";
    const TWO: &str = "impl Index[u8] for Grid {\n\
         type Output = Str;\n\
         fn at(let self: Grid, let i: u8) -> scoped(self) Str { return self.names[0]; }\n}\n";
    const BARE: &str = "fn f(let g: Grid) -> i64 { return g[0]; }";
    const SUFFIXED: &str = "fn f(let g: Grid) -> i64 { return g[0usize]; }";

    // One impl: the literal is CHECKED against `usize`, so `g[0]` is fine.
    assert!(
        check_source(&format!("{G}{ONE}{BARE}")).is_empty(),
        "one impl checks the index against its own `I`"
    );
    // Two impls: the index is synthesised and an unsuffixed literal names
    // no impl.
    assert_eq!(
        check_source(&format!("{G}{ONE}{TWO}{BARE}")),
        vec!["T0029"],
        "a second impl must break the bare literal"
    );
    // The same two impls with a suffix: silent, and the result is the
    // `Output` of the impl the suffix names (`i64`, which `f` returns).
    assert!(
        check_source(&format!("{G}{ONE}{TWO}{SUFFIXED}")).is_empty(),
        "the suffix names one impl by one R12 lookup"
    );
    // Order is not a tie-break: the impls swapped give the same answers.
    assert_eq!(check_source(&format!("{G}{TWO}{ONE}{BARE}")), vec!["T0029"]);
    assert!(check_source(&format!("{G}{TWO}{ONE}{SUFFIXED}")).is_empty());
    // An index type NO impl takes is the other half of the clause.
    assert_eq!(
        check_source(&format!(
            "{G}{ONE}{TWO}fn f(let g: Grid, let k: i64) -> i64 {{ return g[k]; }}"
        )),
        vec!["T0029"],
        "`Index[i64]` is not among the impls"
    );
}

/// Two checks of the same build in one process give byte-identical output.
#[test]
fn checking_twice_is_deterministic() {
    let src = "struct P { x: i32 }\nfn f(let p: P) -> i32 { let q = p.y; return p.x + true; }\nfn g() { let (a, b) = 1; }";
    let a = check_source(src);
    let b = check_source(src);
    assert_eq!(a, b);
    // `PER_DECL_BUDGET` is 1: one diagnostic per declaration, two declarations speak.
    assert_eq!(a.len(), 2);
}

// ------------------------------------------------------------------- I5
//
// One mutation probe per mechanism R38-R41 introduces: each pair is the
// same program with ONE thing changed, so a probe that passes for the
// wrong reason shows up as the pair agreeing when it must not.

/// R38(c): the expected type binds a slot before any argument is visited,
/// and taking the expected type away is the whole difference between a
/// clean call and T0039.
#[test]
fn r38c_expected_type_is_what_binds_the_result_only_parameter() {
    const MAKE: &str = "fn make[T]() -> Option[T] { return none; }\n";
    assert!(
        check_source(&format!("{MAKE}fn f() -> Option[u8] {{ return make(); }}")).is_empty(),
        "the expected type determines `T`"
    );
    assert_eq!(
        check_source(&format!("{MAKE}fn f() {{ let v = make(); }}")),
        vec!["T0039"],
        "without one, `T` occurs nowhere else"
    );
    // ...and writing it explicitly is the fix the message names.
    assert!(
        check_source(&format!("{MAKE}fn f() {{ let v = make[u8](); }}")).is_empty(),
        "R38(a): the explicit argument supplies what (c) would have"
    );
}

/// R38(d): a binding is never revised — the SECOND argument is the one
/// that disagrees, and moving the disagreement moves the diagnostic.
#[test]
fn r38d_a_binding_is_never_revised_and_the_later_argument_is_blamed() {
    const PICK: &str = "fn pick[T: Copyable](let a: T, let b: T) -> T { return a; }\n";
    assert!(check_source(&format!("{PICK}fn f() -> i32 {{ return pick(1, 2); }}")).is_empty());
    assert_eq!(
        check_source(&format!("{PICK}fn f() -> i32 {{ return pick(1, true); }}")),
        vec!["T0026"]
    );
    // The same disagreement with the expected type absent is still one
    // T0026, now from the first argument's binding rather than (c)'s.
    assert_eq!(
        check_source(&format!("{PICK}fn f() {{ let x = pick(1i32, true); }}")),
        vec!["T0026"]
    );
}

/// R33 at a call: an argument of type `never` binds nothing, so the slot
/// stays undetermined. Give the same call a non-`never` argument and it
/// types.
#[test]
fn r33_never_binds_nothing_at_an_argument() {
    const BASE: &str =
        "fn id[T](sink x: T) -> T { return x; }\nfn die() -> never { return die(); }\n";
    assert_eq!(
        check_source(&format!("{BASE}fn f() {{ id(die()); }}")),
        vec!["T0039"]
    );
    assert!(check_source(&format!("{BASE}fn f() {{ id(1i32); }}")).is_empty());
    // And with the expected type present, `never` is harmless: (c) bound
    // the slot before the argument was ever visited.
    assert!(check_source(&format!("{BASE}fn f() -> i32 {{ return id(die()); }}")).is_empty());
}

/// R39: the explicit-argument count and the argument count, both at the
/// call, both T0039.
#[test]
fn r39_counts_are_checked_at_the_call() {
    // I8: `return a;` on a `let` parameter of unbounded rigid type is a
    // move out of a `let` parameter (ch01 R3, the clause
    // `copy-without-copyable-rejected` asserts), so the fixture carries
    // a `Copyable` bound. Nothing this probe measures changes.
    const G: &str = "fn g[T: Copyable](let a: T) -> T { return a; }\n";
    assert!(check_source(&format!("{G}fn f() -> i32 {{ return g[i32](1); }}")).is_empty());
    assert_eq!(
        check_source(&format!("{G}fn f() -> i32 {{ return g[i32, u8](1); }}")),
        vec!["T0039"],
        "one declared parameter, two written"
    );
    assert_eq!(
        check_source(&format!("{G}fn f() -> i32 {{ return g(1, 2); }}")),
        vec!["T0039"],
        "one declared argument, two passed"
    );
    assert_eq!(
        check_source("fn h(let a: i32) { }\nfn f() { h(); }"),
        vec!["T0039"],
        "and a non-generic callee counts its arguments too"
    );
}

/// R41: the closure pre-test. The ONLY difference between the two
/// programs is the order of the parameters, which is what decides whether
/// the closure's parameter type is complete when it is visited.
#[test]
fn r41_closure_is_checked_only_when_its_parameter_types_are_complete() {
    const FWD: &str =
        "fn apply[T, U, F: fn(let T) -> U](let x: T, let f: F) -> U { return f(x); }\n";
    const REV: &str =
        "fn apply[T, U, F: fn(let T) -> U](let f: F, let x: T) -> U { return f(x); }\n";
    assert!(
        check_source(&format!(
            "{FWD}fn demo() -> i32 {{ return apply(2, |let n| n * 2); }}"
        ))
        .is_empty(),
        "`2` binds T, so the closure is CHECKed and its body gives U"
    );
    assert_eq!(
        check_source(&format!(
            "{REV}fn demo() -> i32 {{ return apply(|let n| n * 2, 2); }}"
        )),
        vec!["T0035"],
        "the closure precedes what binds T, so it is SYNTHed and R35 rejects it"
    );
    // Annotating the parameter is the fix: nothing is inferred from a
    // closure body in SYNTH mode, but an annotated closure has a type.
    assert!(
        check_source(&format!(
            "{REV}fn demo() -> i32 {{ return apply(|let n: i32| n * 2, 2); }}"
        ))
        .is_empty()
    );
}

/// R40: brands are compared by identity and a `with` block introduces a
/// FRESH one. Two sibling blocks must not share a brand either.
#[test]
fn r40_fresh_with_brands_are_distinct_and_bind_by_identity() {
    const N: &str = "struct Node[A: brand] { val: i64 }\n\
                     fn touch[A: brand](inout a: Arena[Node[A], A], let r: Ref[Node[A], A]) -> i64 { return 0; }\n";
    // One block: the argument types agree, so `A` binds once.
    assert!(
        check_source(&format!(
            "{N}fn f() {{ with arena one: Arena[Node[one]] {{\n\
               let x: Ref[Node[one], one] = one.alloc(Node {{ val: 1 }});\n\
               let v: i64 = touch(&one, x);\n}} }}"
        ))
        .is_empty()
    );
    // Two blocks: the brands differ, so the second argument disagrees
    // with what the first bound.
    assert_eq!(
        check_source(&format!(
            "{N}fn f() {{ with arena one: Arena[Node[one]] {{\n\
               let x: Ref[Node[one], one] = one.alloc(Node {{ val: 1 }});\n\
               with arena two: Arena[Node[two]] {{\n\
                 let v: i64 = touch(&two, x);\n\
               }}\n}} }}"
        )),
        vec!["T0026"]
    );
    // SIBLING blocks each get their OWN brand (the ordinal only ever
    // rises), so both type cleanly and neither reuses the other's. R40's
    // "a type mentioning a fresh brand can never reach a binding outside
    // its `with` block" is the SCOPE: the name is simply not writable
    // there, which is why this half is an acceptance, not a rejection.
    assert!(
        check_source(&format!(
            "{N}fn f() {{\n\
               with arena one: Arena[Node[one]] {{\n\
                 let x: Ref[Node[one], one] = one.alloc(Node {{ val: 1 }});\n\
                 let v: i64 = touch(&one, x);\n\
               }}\n\
               with arena two: Arena[Node[two]] {{\n\
                 let y: Ref[Node[two], two] = two.alloc(Node {{ val: 2 }});\n\
                 let w: i64 = touch(&two, y);\n\
               }}\n}}"
        ))
        .is_empty(),
        "each block binds its own brand"
    );
}

/// R7/R28: a generic `fn` item and `none` are the two values with no type
/// of their own. Each is T0039 in SYNTH and fine in CHECK.
#[test]
fn r7_and_r28_values_without_a_type_of_their_own() {
    const ID: &str = "fn id[T](sink x: T) -> T { return x; }\n";
    assert_eq!(
        check_source(&format!("{ID}fn f() {{ let g = id; }}")),
        vec!["T0039"]
    );
    assert!(
        check_source("fn id(sink x: i32) -> i32 { return x; }\nfn f() { let g = id; }").is_empty(),
        "a NON-generic `fn` item is a value"
    );
    assert_eq!(check_source("fn f() { let c = none; }"), vec!["T0039"]);
    assert!(check_source("fn f() { let c: Option[u8] = none; }").is_empty());
}

/// R34/R38: a generic struct literal takes its arguments from the
/// expected type, and the fields are then CHECKED against the
/// substituted field types.
#[test]
fn r34_struct_literal_arguments_come_from_the_expected_type() {
    const P: &str = "struct Pair[T] { a: T, b: T }\n";
    assert!(
        check_source(&format!(
            "{P}fn f() -> Pair[u8] {{ let p: Pair[u8] = Pair {{ a: 1, b: 2 }}; return p; }}"
        ))
        .is_empty()
    );
    assert_eq!(
        check_source(&format!(
            "{P}fn f() -> Pair[u8] {{ let p: Pair[u8] = Pair {{ a: 1, b: true }}; return p; }}"
        )),
        vec!["T0026"],
        "the field is checked as `u8`, not merely synthesised"
    );
}

/// R12 at a generic call, folded into R38(e): the bound is checked with
/// the binding R38 determined, not with a guess.
#[test]
fn r12_bounds_are_checked_with_the_binding_r38_determined() {
    const S: &str = "struct Plain { n: i64 }\n\
                     fn want[T: Copyable](let x: T) -> i64 { return 0; }\n";
    assert!(check_source(&format!("{S}fn f() -> i64 {{ return want(1i64); }}")).is_empty());
    assert_eq!(
        check_source(&format!(
            "{S}fn f(let p: Plain) -> i64 {{ return want(p); }}"
        )),
        vec!["T0012"],
        "`Plain` is not `Copyable`"
    );
    // The same bound, reached through the EXPECTED type rather than an
    // argument, must fail the same way.
    assert_eq!(
        check_source(
            "struct Plain { n: i64 }\n\
             fn make[T: Copyable]() -> Option[T] { return none; }\n\
             fn f() -> Option[Plain] { return make(); }"
        ),
        vec!["T0012"]
    );
}

/// A generic `Index` impl: the impl's own parameters are determined with
/// the same machinery, so the index type and `Output` are read with them
/// substituted rather than left open.
#[test]
fn a_generic_index_impl_is_instantiated_not_read_open() {
    // I8: `return self.v;` on a non-`Copyable` rigid field is a partial
    // move out of a `let self` (ch01 R4a(c)), so the impl carries a
    // `Copyable` bound; `i64` satisfies it and the probe's subject (the
    // container slot the receiver binds) is unchanged.
    const B: &str = "struct Box[T] { v: T }\n\
         impl[T: Copyable] Index[usize] for Box[T] {\n\
             type Output = T;\n\
             fn at(let self: Box[T], let i: usize) -> scoped(self) T { return self.v; }\n}\n";
    assert!(
        check_source(&format!(
            "{B}fn f(let b: Box[i64]) -> i64 {{ return b[0]; }}"
        ))
        .is_empty(),
        "`Output` is `T`, which is `i64` here"
    );
    assert_eq!(
        check_source(&format!(
            "{B}fn f(let b: Box[i64]) -> Str {{ return b[0]; }}"
        )),
        vec!["T0026"],
        "and it really is `i64`, not an unread `T`"
    );
}

/// A RECURSIVE generic call: the callee's slots and the caller's rigid
/// parameters are the same `Param` rows, so the match must not take
/// equality as "nothing to do".
#[test]
fn a_recursive_generic_call_infers_its_own_parameters() {
    assert!(
        check_source("fn id[T](sink x: T) -> T { return id(move x); }").is_empty(),
        "the expected type and the declared result are the same row"
    );
    assert!(
        check_source(
            "struct SIter[T] { n: usize }\n\
             fn iter[T: Copyable](let s: Slice[T]) -> SIter[T] { return iter(s); }"
        )
        .is_empty()
    );
}

/// R59, the metamorphic pair: a generic body is checked ONCE, at its
/// definition, with rigid parameters and its declared bounds only. Adding
/// instantiations — and changing which ones — must not change one
/// diagnostic of it.
#[test]
fn no_error_depends_on_instantiation() {
    // (a) A body that is ill-typed at its definition stays ill-typed, and
    // identically so, however many ways it is instantiated.
    const BAD: &str = "fn sum2[T: Copyable](let a: T, let b: T) -> T { return a + b; }\n";
    let alone = check_source(BAD);
    assert_eq!(alone, vec!["T0057"], "R57 at the definition");
    let once = check_source(&format!("{BAD}fn u1() -> i32 {{ return sum2(1, 2); }}"));
    let twice = check_source(&format!(
        "{BAD}fn u1() -> i32 {{ return sum2(1, 2); }}\n\
         fn u2() -> i64 {{ return sum2(1i64, 2i64); }}"
    ));
    let three = check_source(&format!(
        "{BAD}fn u1() -> i32 {{ return sum2(1, 2); }}\n\
         fn u2() -> i64 {{ return sum2(1i64, 2i64); }}\n\
         fn u3() -> u8 {{ return sum2(1u8, 2u8); }}"
    ));
    assert_eq!(alone, once);
    assert_eq!(once, twice);
    assert_eq!(twice, three);

    // (b) A body that is WELL-typed at its definition stays silent under
    // every instantiation, including one whose argument would make the
    // body's own operations illegal if it were re-checked per
    // instantiation.
    const GOOD: &str = "fn dup[T: Copyable](let x: T) -> T { return x; }\n";
    assert!(check_source(GOOD).is_empty());
    assert!(check_source(&format!("{GOOD}fn u1() -> i32 {{ return dup(1); }}")).is_empty());
    assert!(
        check_source(&format!(
            "{GOOD}fn u1() -> i32 {{ return dup(1); }}\n\
             fn u2() -> Str {{ return dup(\"x\"); }}"
        ))
        .is_empty()
    );

    // (c) The INSTANTIATION may be rejected (R12 at the call), and that
    // rejection is the caller's, never the callee's: the generic body's
    // own diagnostics are unchanged.
    let with_bad_use = check_source(&format!(
        "struct Plain {{ n: i64 }}\n{GOOD}fn u(let p: Plain) -> Plain {{ return dup(p); }}"
    ));
    assert_eq!(with_bad_use, vec!["T0012"], "one diagnostic, at the caller");
}

/// R38(f)/§7.4: "nothing survives the call". The `debug_assert` in
/// `body::stmt` checks it at every statement boundary; this probe is the
/// shape that would trip it — nested generic calls in arguments, each
/// running the procedure to completion before the outer one continues.
#[test]
fn nested_generic_calls_leave_no_binding_behind() {
    assert!(
        check_source(
            "fn id[T](sink x: T) -> T { return x; }\n\
             fn pair[A: Copyable, B: Copyable](let a: A, let b: B) -> A { return a; }\n\
             fn f() -> i32 { return pair(id(1i32), pair(2i64, 3u8)); }"
        )
        .is_empty()
    );
}

// -------------------------------------------- I5, verification round
//
// Each probe below is an over-acceptance the producer's R38 let through,
// written as the pair it failed: the program that MUST be rejected next
// to the one-token change that makes it clean.

/// R41/R15: a callable parameter "accepts a closure type, `fn` item or `fn`
/// value OF THAT SIGNATURE". R38(d) binds `F` to whatever the argument
/// synthesised, so the signature is a bound like any other and is checked
/// at (e) — a `fn` item of another signature, or a plain `i32`, is not
/// silently accepted.
#[test]
fn a_callable_parameter_checks_the_signature_of_a_non_closure_argument() {
    const APPLY: &str =
        "fn apply[U, F: fn (sink i32) -> U](sink x: i32, let f: F) -> U { return f(move x); }\n";
    assert!(
        check_source(&format!(
            "{APPLY}fn double(sink x: i32) -> i32 {{ return x * 2; }}\n\
             fn go() -> i32 {{ return apply(2, double); }}"
        ))
        .is_empty(),
        "the right signature, with `U` from the expected type"
    );
    assert_eq!(
        check_source(&format!(
            "{APPLY}fn wrong(sink x: Str) -> Str {{ return x; }}\n\
             fn go() -> i32 {{ return apply(2, wrong); }}"
        )),
        vec!["T0041"],
        "a `fn` item of another signature"
    );
    assert_eq!(
        check_source(&format!(
            "{APPLY}fn tostr(sink x: i32) -> Str {{ return \"a\"; }}\n\
             fn go() -> i32 {{ return apply(2, tostr); }}"
        )),
        vec!["T0041"],
        "the parameters agree and the result does not"
    );
    assert_eq!(
        check_source(&format!("{APPLY}fn go() -> i32 {{ return apply(2, 5); }}")),
        vec!["T0041"],
        "not a function at all"
    );
    // In SYNTH position nothing binds `U` (R38 never binds through a
    // bound): R39, before any signature is compared.
    assert_eq!(
        check_source(&format!(
            "{APPLY}fn double(sink x: i32) -> i32 {{ return x * 2; }}\n\
             fn go() {{ let d = apply(2, double); }}"
        )),
        vec!["T0039"]
    );
}

/// R39 is about EVERY parameter of the callee: one that occurs in no
/// argument type and not in the result is undetermined after (d) even
/// though no substitution ever needed it.
#[test]
fn a_parameter_in_no_position_is_undetermined_not_silently_dropped() {
    const MAKE: &str = "fn make[T]() -> i32 { return 0; }\n";
    assert_eq!(
        check_source(&format!("{MAKE}fn f() -> i32 {{ return make(); }}")),
        vec!["T0039"]
    );
    assert!(check_source(&format!("{MAKE}fn f() -> i32 {{ return make[u8](); }}")).is_empty());
}

/// R34/R38 for a literal in SYNTH position: the fields are the arguments,
/// so the first binds `T` and the second is compared against it at (e).
#[test]
fn a_generic_struct_literal_in_synth_binds_from_its_fields() {
    const P: &str = "struct Pair[T] { a: T, b: T }\n";
    assert!(
        check_source(&format!(
            "{P}fn f() {{ let p = Pair {{ a: 1u8, b: 2u8 }}; }}"
        ))
        .is_empty()
    );
    assert_eq!(
        check_source(&format!(
            "{P}fn f() {{ let p = Pair {{ a: 1u8, b: true }}; }}"
        )),
        vec!["T0026"]
    );
    // A struct whose parameter occurs in no field cannot be determined
    // from the literal alone...
    const E: &str = "struct Empty[T] { n: i64 }\n";
    assert_eq!(
        check_source(&format!("{E}fn f() {{ let e = Empty {{ n: 1 }}; }}")),
        vec!["T0039"]
    );
    // ...and is, from the expected type (R38(c)).
    assert!(
        check_source(&format!(
            "{E}fn f() {{ let e: Empty[u8] = Empty {{ n: 1 }}; }}"
        ))
        .is_empty()
    );
    // R12 on the struct's own bound, with the binding the fields gave.
    const B: &str = "struct Plain { n: i64 }\nstruct Box[T: Copyable] { v: T }\n";
    assert_eq!(
        check_source(&format!(
            "{B}fn f(let p: Plain) {{ let b = Box {{ v: p }}; }}"
        )),
        vec!["T0012"]
    );
}

/// R38(a)/R11: an explicit argument is read by the slot's declared kind,
/// and a VALUE in a type slot is reported, not lowered to a silent error
/// that would make the whole call absorbing.
#[test]
fn a_value_in_an_explicit_type_slot_is_t0011() {
    // I8: `return a;` on a `let` parameter of unbounded rigid type is a
    // move out of a `let` parameter (ch01 R3, the clause
    // `copy-without-copyable-rejected` asserts), so the fixture carries
    // a `Copyable` bound. Nothing this probe measures changes.
    const G: &str = "fn g[T: Copyable](let a: T) -> T { return a; }\n";
    assert_eq!(
        check_source(&format!("{G}fn f() -> i32 {{ return g[1](1); }}")),
        vec!["T0011"]
    );
    assert!(
        check_source(&format!(
            "{G}fn f() -> Option[i32] {{ return g[Option[i32]](some(1)); }}"
        ))
        .is_empty(),
        "a compound type argument lowers"
    );
}

/// An argument that already failed makes the call absorbing: the slot it
/// alone would have bound is not a second diagnostic.
#[test]
fn a_failed_argument_does_not_cascade_into_t0039() {
    assert_eq!(
        check_messages("fn id[T](sink x: T) -> T { return x; }\nfn f() { let v = id(1 + true); }")
            .len(),
        1
    );
}

// ------------------------------------------------------------- I6 probes
//
// One mutation probe per mechanism I6 adds: `normalise.rs`'s
// `normalise_proj` (the exact impl index, the structural descent, the memo
// key, the `NoImpl` outcome, the per-query work budget), R20's neutrality,
// R62's constraint entries at a call, R12 for a projection subject, R43 on
// a neutral projection, and §7.4's container slots for a generic METHOD
// call. Each probe pairs an accepted program with the ONE-TOKEN mutation
// that must flip it, so a mechanism that silently stops working fails here
// rather than passing by silence.

/// An `Iterator` whose `Item` is `i64`, and a one-parameter adaptor over it.
const CHAIN: &str = "struct Counter { n: i64, end: i64 }\n\
     impl Iterator for Counter {\n\
         type Item = i64;\n\
         fn next(inout self: Counter) -> Option[i64] { return none; }\n\
     }\n\
     struct Skip[I] { inner: I, n: usize }\n\
     impl[I: Iterator] Iterator for Skip[I] {\n\
         type Item = I.Item;\n\
         fn next(inout self: Skip[I]) -> Option[I.Item] { return self.inner.next(); }\n\
     }\n\
     fn seed[I: Iterator](inout it: I, let x: I.Item) -> i64 { return 0; }\n";

/// R20 through the real checker: `Skip[Skip[Counter]].Item` collapses to
/// `i64` by structural descent, and the collapsed type is what the argument
/// is CHECKED against — so a `u8` there is T0026 and not silence.
#[test]
fn i6_normalisation_collapses_a_chain_and_the_result_is_checked() {
    assert!(
        check_source(&format!(
            "{CHAIN}fn f(inout s: Skip[Skip[Counter]]) -> i64 {{ return seed(&s, 7i64); }}"
        ))
        .is_empty(),
        "the chain normalises to i64 and 7i64 fits"
    );
    assert_eq!(
        check_source(&format!(
            "{CHAIN}fn f(inout s: Skip[Skip[Counter]]) -> i64 {{ return seed(&s, 7u8); }}"
        )),
        vec!["T0026"],
        "the SAME chain rejects a u8: the projection really collapsed"
    );
}

/// §17 amendment 1, re-asserted against the real checker: the
/// normalisation memo is keyed by the substituted HEAD, not by the trait
/// reference. `Holder[i64].Item` and `Holder[u8].Item` share one
/// `TraitRefId` and one right-hand side row (`Param(impl, 0)`); if the key
/// were the trait reference the second query would read the first's answer
/// and accept the wrong literal.
#[test]
fn i6_the_normalisation_memo_key_is_the_head_not_the_trait_ref() {
    const H: &str = "struct Holder[T] { v: T }\n\
         impl[T: Droppable] Iterator for Holder[T] {\n\
             type Item = T;\n\
             fn next(inout self: Holder[T]) -> Option[T] { return none; }\n\
         }\n\
         fn seed[I: Iterator](inout it: I, let x: I.Item) -> i64 { return 0; }\n";
    assert!(
        check_source(&format!(
            "{H}fn a(inout h: Holder[i64]) -> i64 {{ return seed(&h, 1i64); }}\n\
             fn b(inout h: Holder[u8]) -> i64 {{ return seed(&h, 2u8); }}"
        ))
        .is_empty(),
        "each head gets its own answer"
    );
    assert_eq!(
        check_source(&format!(
            "{H}fn a(inout h: Holder[i64]) -> i64 {{ return seed(&h, 1i64); }}\n\
             fn b(inout h: Holder[u8]) -> i64 {{ return seed(&h, 2i64); }}"
        )),
        vec!["T0026"],
        "`Holder[u8].Item` is u8 even after `Holder[i64].Item` was asked first"
    );
}

/// R20's neutrality: a projection on a rigid parameter equals only itself.
/// Nothing is learnt from what the parameter might become (R59), so a
/// concrete impl for a sibling instantiation does not answer — and the
/// member lookup that would have found it reports R43 rather than staying
/// silent.
#[test]
fn i6_a_neutral_projection_matches_only_itself() {
    const T: &str = "trait Tagged { fn tag(let self) -> i64; }\n\
         struct Bx[T] { v: T }\n\
         impl Tagged for Bx[i64] { fn tag(let self: Bx[i64]) -> i64 { return 1; } }\n";
    assert!(
        check_source(&format!(
            "{T}fn g(let b: Bx[i64]) -> i64 {{ return b.tag(); }}"
        ))
        .is_empty(),
        "the concrete head resolves"
    );
    assert_eq!(
        check_source(&format!(
            "{T}fn g[I: Iterator](let b: Bx[I.Item]) -> i64 {{ return b.tag(); }}"
        )),
        vec!["T0043"],
        "`Bx[I.Item]` is not `Bx[i64]`, and the miss is reported, not swallowed"
    );
}

/// R20's `NoImpl`: a projection whose head has no impl of the trait has no
/// type, and design §8's R20 row says the site reports T0012.
#[test]
fn i6_a_projection_on_a_head_without_an_impl_is_t0012() {
    assert_eq!(
        check_source(
            "struct Plain { n: i64 }\n\
             fn seed[I: Iterator](sink it: I, let x: I.Item) -> i64 { return 0; }\n\
             fn f(sink p: Plain) -> i64 { return seed(move p, 1i64); }"
        ),
        vec!["T0012"],
        "`Plain` implements no `Iterator`, so `Plain.Item` does not exist"
    );
}

/// R62's USE side (design §7.4(e)): a constraint entry's subject is
/// substituted AND normalised at the call, and then every bound of the
/// entry must hold for the result.
#[test]
fn i6_constraint_entries_are_checked_at_the_call() {
    const S: &str = "struct Circle { r: f64 }\n\
         struct Ints { n: i64 }\n\
         impl Iterator for Ints {\n\
             type Item = i64;\n\
             fn next(inout self: Ints) -> Option[i64] { return none; }\n\
         }\n\
         struct Circles { n: i64 }\n\
         impl Iterator for Circles {\n\
             type Item = Circle;\n\
             fn next(inout self: Circles) -> Option[Circle] { return none; }\n\
         }\n\
         fn drain[I: Iterator, I.Item: Add](sink it: I) -> i64 { return 0; }\n";
    assert!(
        check_source(&format!(
            "{S}fn f(sink c: Ints) -> i64 {{ return drain(move c); }}"
        ))
        .is_empty(),
        "`Ints.Item` is `i64`, which has `Add`"
    );
    assert_eq!(
        check_source(&format!(
            "{S}fn f(sink c: Circles) -> i64 {{ return drain(move c); }}"
        )),
        vec!["T0012"],
        "`Circles.Item` is `Circle`, which has no `Add`"
    );
}

/// R12 for a PROJECTION subject plus R43 on it (design §7.6, §7.7): the
/// bounds a trait declares for its associated type are the operations of
/// the neutral projection, and nothing else is.
#[test]
fn i6_a_neutral_projection_carries_exactly_its_declared_bounds() {
    assert!(
        check_source(
            "trait Keyed2 { type Key: Eq + Ord; fn key(let self) -> Self.Key; }\n\
             fn less[T: Keyed2](let a: T, let b: T) -> bool { return a.key() < b.key(); }"
        )
        .is_empty(),
        "`Ord` is declared for `Key`, so `<` on `T.Key` is R57-legal"
    );
    assert_eq!(
        check_source(
            "trait Keyed3 { type Key: Eq; fn key(let self) -> Self.Key; }\n\
             fn less[T: Keyed3](let a: T, let b: T) -> bool { return a.key() < b.key(); }"
        ),
        vec!["T0057"],
        "drop `Ord` from the declaration and the SAME body loses the operation"
    );
}

/// Design §7.4's container slots for a generic METHOD call: the receiver
/// binds the owner's parameters in step (b), which is what makes a method
/// whose result is `Self.A` — or the impl's own parameter — typable at all.
/// I5 left every such method `Candidate::Generic` and the call untyped.
#[test]
fn i6_a_generic_method_binds_its_container_from_the_receiver() {
    // I8: `return self.v;` on a non-`Copyable` rigid field is a partial
    // move out of a `let self` (ch01 R4a(c)), so the impl carries a
    // `Copyable` bound; `i64` satisfies it and the probe's subject (the
    // container slot the receiver binds) is unchanged.
    const B: &str = "struct Bag[T] { v: T }\n\
         impl[T: Copyable] Bag[T] { pub fn get(let self: Bag[T]) -> T { return self.v; } }\n";
    assert!(
        check_source(&format!(
            "{B}fn f(let b: Bag[i64]) -> i64 {{ return b.get(); }}"
        ))
        .is_empty(),
        "`T := i64` comes from the receiver, so `get` returns `i64`"
    );
    assert_eq!(
        check_source(&format!(
            "{B}fn f(let b: Bag[i64]) -> u8 {{ return b.get(); }}"
        )),
        vec!["T0026"],
        "and the call really has that type: a `u8` result is rejected"
    );
}

/// The same, through a TRAIT container, whose `Self` is ordinal 0 of its
/// generics: `h.get()` on a rigid `H: Has` has type `H.A`, a neutral
/// projection, and R10 then refuses to coerce it to `dyn Tr`.
#[test]
fn i6_a_trait_method_result_is_a_neutral_projection() {
    const H: &str = "trait Tr2 { fn go(let self); }\n\
         trait Has2 { type A: Tr2; fn get(let self) -> Self.A; }\n";
    assert!(
        check_source(&format!(
            "{H}fn f[H: Has2](let h: H) -> H.A {{ return h.get(); }}"
        ))
        .is_empty(),
        "`get` on `H` has type `H.A`"
    );
    assert_eq!(
        check_source(&format!(
            "{H}fn f[H: Has2](let h: H) -> dyn Tr2 {{ return h.get() as dyn Tr2; }}"
        )),
        vec!["T0010"],
        "a neutral projection is not a concrete type and does not coerce to `dyn`"
    );
}

/// §17 amendment 3 through the real checker: `k` impls in one
/// `(trait, HeadKey)` bucket are each one exact probe, and the answer is
/// the right one — the bucket's size changes neither the answer nor,
/// per `scale.rs`'s measurement, the match-step count.
#[test]
fn i6_the_exact_impl_index_picks_the_right_impl_out_of_a_crowded_bucket() {
    let mut s = String::new();
    s.push_str("struct Cell[T] { t: T }\n");
    for j in 0..16 {
        s.push_str(&format!("struct Mk{j} {{ z: i64 }}\n"));
        let item = if j == 7 { "u8" } else { "i64" };
        s.push_str(&format!(
            "impl Iterator for Cell[Mk{j}] {{\n\
                 type Item = {item};\n\
                 fn next(inout self: Cell[Mk{j}]) -> Option[{item}] {{ return none; }}\n\
             }}\n"
        ));
    }
    s.push_str("fn seed[I: Iterator](inout it: I, let x: I.Item) -> i64 { return 0; }\n");
    let ok = format!("{s}fn f(inout c: Cell[Mk7]) -> i64 {{ return seed(&c, 1u8); }}");
    let bad = format!("{s}fn f(inout c: Cell[Mk7]) -> i64 {{ return seed(&c, 1i64); }}");
    assert!(
        check_source(&ok).is_empty(),
        "row 7 of the bucket says `u8`, and that is the one that answers"
    );
    assert_eq!(
        check_source(&bad),
        vec!["T0026"],
        "a neighbouring row's `i64` must not answer for `Cell[Mk7]`"
    );
}

/// R59 extended to projections (design §13 I6's "the metamorphic
/// `no_error_depends_on_instantiation` extended to projections"): a generic
/// body that mentions a projection is checked ONCE, at its definition, with
/// the projection neutral. Adding instantiations — and changing which ones
/// — must not change one diagnostic of it, and a rejection at an
/// instantiation is the CALLER's.
#[test]
fn no_error_depends_on_instantiation_projections() {
    // (a) A body whose neutral projection lacks the operation is ill-typed
    // at its definition, identically under every instantiation.
    const BAD: &str = "trait Keyed4 { type Key: Eq; fn key(let self) -> Self.Key; }\n\
         struct Rec { k: i64 }\n\
         impl Keyed4 for Rec { type Key = i64; fn key(let self: Rec) -> i64 { return self.k; } }\n\
         fn less[T: Keyed4](let a: T, let b: T) -> bool { return a.key() < b.key(); }\n";
    let alone = check_source(BAD);
    assert_eq!(
        alone,
        vec!["T0057"],
        "R57 at the definition, `Key` has no `Ord`"
    );
    let once = check_source(&format!(
        "{BAD}fn u1(let a: Rec, let b: Rec) -> bool {{ return less(a, b); }}"
    ));
    let twice = check_source(&format!(
        "{BAD}fn u1(let a: Rec, let b: Rec) -> bool {{ return less(a, b); }}\n\
         fn u2(let a: Rec, let b: Rec) -> bool {{ return less(b, a); }}"
    ));
    assert_eq!(alone, once, "an instantiation adds nothing");
    assert_eq!(once, twice, "nor does a second one");

    // (b) A body that is well-typed at its definition stays silent under
    // instantiations whose `Item` differs — the projection is normalised at
    // the CALL, never inside the callee.
    assert!(check_source(CHAIN).is_empty(), "the generic body alone");
    assert!(
        check_source(&format!(
            "{CHAIN}fn u1(inout c: Counter) -> i64 {{ return seed(&c, 1i64); }}"
        ))
        .is_empty()
    );
    assert!(
        check_source(&format!(
            "{CHAIN}fn u1(inout c: Counter) -> i64 {{ return seed(&c, 1i64); }}\n\
             fn u2(inout s: Skip[Counter]) -> i64 {{ return seed(&s, 2i64); }}\n\
             fn u3(inout s: Skip[Skip[Counter]]) -> i64 {{ return seed(&s, 3i64); }}"
        ))
        .is_empty(),
        "three depths of the same chain, all silent"
    );

    // (c) A rejection at an instantiation is the caller's one diagnostic;
    // the callee's own body is unchanged.
    assert_eq!(
        check_source(&format!(
            "{CHAIN}fn u1(inout c: Counter) -> i64 {{ return seed(&c, 1i64); }}\n\
             fn u2(inout s: Skip[Counter]) -> i64 {{ return seed(&s, 2u8); }}"
        )),
        vec!["T0026"],
        "one diagnostic, at the caller that got the element type wrong"
    );
}

/// R31's element type through R20 (design §13 I6's "R31 for-element type
/// from `Item`"): `body::assoc_item` used to answer only from the EXACT
/// impl index, so a chain whose outermost impl is generic — the ordinary
/// adaptor shape — left the element `TY_ERROR` and the loop body unchecked.
#[test]
fn i6_the_for_element_type_comes_from_item_through_the_chain() {
    assert!(
        check_source(&format!(
            "{CHAIN}fn f(sink s: Skip[Skip[Counter]]) -> i64 {{\n\
                 var t: i64 = 0;\n\
                 for x in s {{ t = t + x; }}\n\
                 return t;\n\
             }}"
        ))
        .is_empty(),
        "`Skip[Skip[Counter]].Item` is `i64`, so `t + x` is legal"
    );
    assert_eq!(
        check_source(&format!(
            "{CHAIN}fn f(sink s: Skip[Skip[Counter]]) -> u8 {{\n\
                 var t: u8 = 0;\n\
                 for x in s {{ t = t + x; }}\n\
                 return t;\n\
             }}"
        )),
        vec!["T0026"],
        "and the element really is typed: a `u8` accumulator is rejected"
    );
}

/// The member-lookup memo must separate SCOPES for a projection receiver.
/// `I.Item` is one `TyId` for every method of one impl, but R62's
/// constraint entries live on each method's OWN generics — so `other` and
/// `show` below ask the same `(module, receiver, name)` question and must
/// get different answers. `other` is declared first on purpose: a memo
/// keyed by module alone would cache its silence and leave `show`'s call
/// untyped, which absorbs the T0026 this asserts.
#[test]
fn i6_the_method_memo_separates_scopes_for_a_projection_receiver() {
    const S: &str = "trait Shw { fn shw(let self) -> i64; }\n\
         struct Sm[I] { it: I }\n\
         impl[I: Iterator] Sm[I] {\n\
             pub fn other(let self: Sm[I], let z: I.Item) -> i64 { return z.shw(); }\n\
             pub fn show[I.Item: Shw](let self: Sm[I], let z: I.Item) -> u8 { return z.shw(); }\n\
         }\n";
    assert_eq!(
        check_source(S),
        vec!["T0026"],
        "`show` resolves `shw` through its own constraint entry and gets `i64`, \
         which is not the declared `u8`; `other` has no such entry and stays silent"
    );
}

// ------------------------------------------------- I6 verifier probes
//
// Three over-acceptances the I6 verifier found by mutation and repaired.
// Each pairs the rejecting program with the one-token change that must be
// accepted, so the repair cannot regress into silence unnoticed.

/// A parameter-less trait and a one-parameter struct to put impls on.
const BOX2: &str = "trait Tagged { fn tag(let self) -> i64; }\n\
     trait Named { fn id(let self) -> i64; }\n\
     struct Box2[T] { v: T }\n";

/// R43 via R12: an impl that UNIFIES with the receiver but is refused by its
/// own bounds is no candidate. Before the repair `methods::scope_declares`
/// read the unifying impl as a trait-argument artifact and kept the lookup
/// silent — on a neutral-projection subterm, on a bare parameter and on a
/// concrete type alike. For a trait WITHOUT parameters the `holds` question
/// was complete, so R12's `No` is the answer; a trait WITH parameters keeps
/// the silence, because `holds` was asked without its arguments.
#[test]
fn i6v_an_impl_refused_by_its_own_bounds_is_no_candidate() {
    const IMPL: &str =
        "impl[T: Named] Tagged for Box2[T] { fn tag(let self: Box2[T]) -> i64 { return 1; } }\n";
    for recv in [
        "fn g[I: Iterator](let b: Box2[I.Item]) -> i64 { return b.tag(); }",
        "fn g[T](let b: Box2[T]) -> i64 { return b.tag(); }",
        "fn g(let b: Box2[i64]) -> i64 { return b.tag(); }",
    ] {
        assert_eq!(
            check_source(&format!("{BOX2}{IMPL}{recv}")),
            vec!["T0043"],
            "{recv}: the only impl is refused by `T: Named`, so there is no candidate"
        );
    }
    // The bound holds, three ways: no bound; a constraint entry on the
    // neutral projection; a concrete type that implements it.
    assert!(
        check_source(&format!(
            "{BOX2}impl[T] Tagged for Box2[T] {{ fn tag(let self: Box2[T]) -> i64 {{ return 1; }} }}\n\
             fn g[I: Iterator](let b: Box2[I.Item]) -> i64 {{ return b.tag(); }}"
        ))
        .is_empty()
    );
    assert!(
        check_source(&format!(
            "{BOX2}{IMPL}fn g[I: Iterator, I.Item: Named](let b: Box2[I.Item]) -> i64 {{ return b.tag(); }}"
        ))
        .is_empty()
    );
    assert!(
        check_source(&format!(
            "{BOX2}{IMPL}struct C {{ r: i64 }}\n\
             impl Named for C {{ fn id(let self: C) -> i64 {{ return 2; }} }}\n\
             fn g(let b: Box2[C]) -> i64 {{ return b.tag(); }}"
        ))
        .is_empty()
    );
    // A trait WITH parameters: `holds(Foo, Conv[])` misses for want of the
    // argument, and the impl in scope keeps R43 silent as before.
    assert!(
        check_source(
            "trait Conv[T] { fn conv(let self, let t: T) -> i64; }\n\
             struct Foo { x: i64 }\n\
             impl Conv[u8] for Foo { fn conv(let self: Foo, let t: u8) -> i64 { return 1; } }\n\
             fn g(let f: Foo) -> i64 { return f.conv(1u8); }"
        )
        .is_empty()
    );
}

/// R43 on a rigid receiver: the candidate traits are EXACTLY its bounds, and
/// when every one of them is a `trait` declared in this build its member
/// table is complete, so a missing method is T0043 and not silence. Silence
/// survives only where absence proves nothing: a prelude trait among the
/// bounds (its opaque rows need not list every method), or a bound that did
/// not resolve (ch10 R2's std names in a build without `std`).
#[test]
fn i6v_a_rigid_receiver_with_complete_bounds_reports_a_missing_method() {
    const T: &str = "trait Named { fn id(let self) -> i64; }\n\
         trait Other { fn other(let self) -> i64; }\n\
         trait Source { type Item: Named; fn pull(inout self) -> Option[Self.Item]; }\n";
    assert_eq!(
        check_source(&format!(
            "{T}fn f[S: Source](let x: S.Item) -> i64 {{ return x.other(); }}"
        )),
        vec!["T0043"],
        "a neutral projection's only bound is `Named`, which has no `other`"
    );
    assert_eq!(
        check_source(&format!(
            "{T}fn f[N: Named](let x: N) -> i64 {{ return x.other(); }}"
        )),
        vec!["T0043"],
        "a parameter's only bound is `Named`, which has no `other`"
    );
    assert!(
        check_source(&format!(
            "{T}fn f[S: Source](let x: S.Item) -> i64 {{ return x.id(); }}"
        ))
        .is_empty()
    );
    assert!(
        check_source(&format!(
            "{T}fn f[S: Source, S.Item: Other](let x: S.Item) -> i64 {{ return x.other(); }}"
        ))
        .is_empty(),
        "R62: the constraint entry adds `Other` to the candidates"
    );
    assert!(
        check_source("fn f[A: brand, L: Allocator[A]](inout a: L) { a.deinit(); }").is_empty(),
        "`Allocator` is opaque without `std`: the bound did not lower, so nothing is known"
    );
}

/// R12 at a call for a subject that merely CONTAINS a neutral projection
/// (`Box2[I.Item]`): the question is decidable — a generic impl binds its
/// parameter to the projection, a concrete impl cannot match it (R59), and
/// the impl's own bounds on what it bound are answered by `holds`'s `Proj`
/// arm. Before the repair `call::check_bounds` skipped such a subject
/// altogether, so `h(b)` with `b: Box2[I.Item]` never had `T: Tagged`
/// checked.
#[test]
fn i6v_a_bound_on_a_subject_that_contains_a_neutral_projection_is_decided() {
    const H: &str = "fn h[T: Tagged](let t: T) -> i64 { return 0; }\n\
         fn g[I: Iterator](let b: Box2[I.Item]) -> i64 { return h(b); }\n";
    assert_eq!(
        check_source(&format!(
            "{BOX2}impl Tagged for Box2[i64] {{ fn tag(let self: Box2[i64]) -> i64 {{ return 1; }} }}\n{H}"
        )),
        vec!["T0012"],
        "a concrete impl for `Box2[i64]` does not match `Box2[I.Item]`"
    );
    assert_eq!(
        check_source(&format!(
            "{BOX2}impl[T: Copyable] Tagged for Box2[T] {{ fn tag(let self: Box2[T]) -> i64 {{ return 1; }} }}\n{H}"
        )),
        vec!["T0012"],
        "the generic impl matches but `I.Item: Copyable` has no witness"
    );
    assert!(
        check_source(&format!(
            "{BOX2}impl[T] Tagged for Box2[T] {{ fn tag(let self: Box2[T]) -> i64 {{ return 1; }} }}\n{H}"
        ))
        .is_empty(),
        "the generic impl binds `T := I.Item`"
    );
    assert!(
        check_source(
            "struct Box2[T] { v: T }\n\
             fn h[T: Droppable](sink t: T) { }\n\
             fn g[I: Iterator](sink b: Box2[I.Item]) { h(move b); }"
        )
        .is_empty(),
        "the structural `Droppable` bound still holds on such a subject"
    );
}

// ---------------------------------------------------------------- I7

/// A corpus FILE's own text (already its own `module ...;`, unlike
/// [`check_source`]'s snippets) plus the build's `exhaust_steps` counter
/// (design §12; `exhaust.rs`'s own budget), for a test that must read the
/// plain algorithm's own step count rather than just its diagnostics.
fn check_file_steps(source: &[u8]) -> (Vec<String>, u64) {
    let mut interner = Interner::new();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(source);
    assert!(
        parsed.diags.is_empty(),
        "corpus file must parse: {:?}",
        parsed.diags
    );
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    (
        out.diagnostics.iter().map(|d| d.code.as_string()).collect(),
        out.counters.exhaust_steps,
    )
}

/// R55's own paragraph: "the computation is charged one step per row ...
/// with no memoisation and no early exit other than an empty matrix or an
/// exhausted column list ... the count is that of the PLAIN algorithm, so
/// that it is the same in every implementation". This re-derives that
/// count a SECOND way — over a flat `Vec<Option<bool>>` row shape instead
/// of `exhaust.rs`'s `PatStore`/`Ctor` — so a counting mistake in either
/// coding is caught by the other, on the design's own two R55 corpus
/// files. The 36-arm file's `node_count` is `arms * (columns + 1)` (one
/// `PatStore` node per tuple pattern, plus one per leaf — `exhaust.rs`'s
/// `pat::PatStore::pattern_node_count`), matching `exhaust.rs` exactly
/// because both charge the TOP-level 1-column tuple matrix once before
/// the N-column one its sole constructor specialises to, every time a
/// query starts (see `ref_query` below).
#[test]
fn plain_step_count_matches_reference() {
    type Row = Vec<Option<bool>>;

    fn ref_usefulness(
        rows: &[Row],
        v: &[Option<bool>],
        steps: &mut u64,
        limit: u64,
    ) -> Option<bool> {
        *steps += rows.len() as u64;
        if *steps > limit {
            return None;
        }
        if v.is_empty() {
            return Some(rows.is_empty());
        }
        match v[0] {
            Some(b) => {
                let spec: Vec<Row> = rows
                    .iter()
                    .filter_map(|r| match r[0] {
                        Some(x) if x == b => Some(r[1..].to_vec()),
                        None => Some(r[1..].to_vec()),
                        _ => None,
                    })
                    .collect();
                ref_usefulness(&spec, &v[1..], steps, limit)
            }
            None => {
                let has_t = rows.iter().any(|r| r[0] == Some(true));
                let has_f = rows.iter().any(|r| r[0] == Some(false));
                if has_t && has_f {
                    // Complete signature: both constructors, neither
                    // early-exit (R55: every matrix the loop forms is
                    // charged, win or lose).
                    let mut any = false;
                    for b in [false, true] {
                        let spec: Vec<Row> = rows
                            .iter()
                            .filter_map(|r| match r[0] {
                                Some(x) if x == b => Some(r[1..].to_vec()),
                                None => Some(r[1..].to_vec()),
                                _ => None,
                            })
                            .collect();
                        let u = ref_usefulness(&spec, &v[1..], steps, limit)?;
                        any = any || u;
                    }
                    Some(any)
                } else {
                    let def_rows: Vec<Row> = rows
                        .iter()
                        .filter(|r| r[0].is_none())
                        .map(|r| r[1..].to_vec())
                        .collect();
                    ref_usefulness(&def_rows, &v[1..], steps, limit)
                }
            }
        }
    }

    /// One usefulness query over the WHOLE match: the written column is
    /// the tuple pattern itself (one column, the sole constructor of a
    /// tuple type always matches), charged once before `ref_usefulness`
    /// charges its own first call on the N-column matrix it specialises
    /// to — the same two charges `exhaust.rs`'s "Some(c)" dispatch makes
    /// for its caller's and callee's matrices.
    fn ref_query(rows: &[Row], v: &[Option<bool>], steps: &mut u64, limit: u64) -> Option<bool> {
        *steps += rows.len() as u64;
        if *steps > limit {
            return None;
        }
        ref_usefulness(rows, v, steps, limit)
    }

    fn ref_steps(arms: &[Row]) -> (u64, bool) {
        let n = arms[0].len();
        let node_count = arms.len() as u64 * (n as u64 + 1);
        let limit = 256 * node_count;
        let mut steps = 0u64;
        for i in 0..arms.len() {
            let rows: Vec<Row> = arms[..i].to_vec();
            if ref_query(&rows, &arms[i], &mut steps, limit).is_none() {
                return (steps, true);
            }
        }
        let wildcard_row = vec![None; n];
        if ref_query(arms, &wildcard_row, &mut steps, limit).is_none() {
            return (steps, true);
        }
        (steps, false)
    }

    /// Each arm row `(true, _, false, ...) => N,` to `Vec<Option<bool>>`.
    fn parse_arms(src: &str) -> Vec<Row> {
        src.lines()
            .map(str::trim)
            .filter(|l| l.starts_with('('))
            .map(|l| {
                let close = l.find(')').expect("a closing paren");
                l[1..close]
                    .split(',')
                    .map(|t| match t.trim() {
                        "true" => Some(true),
                        "false" => Some(false),
                        "_" => None,
                        other => panic!("unexpected pattern token {other:?}"),
                    })
                    .collect()
            })
            .collect()
    }

    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/conformance/09-types");
    for (name, want_exceeded) in [
        ("match-budget-exceeded-rejected", true),
        ("match-budget-within-accepted", false),
    ] {
        let src = std::fs::read_to_string(root.join(format!("{name}.fors"))).unwrap();
        let (diags, steps) = check_file_steps(src.as_bytes());
        let arms = parse_arms(&src);
        let (expected_steps, exceeded) = ref_steps(&arms);
        assert_eq!(
            exceeded, want_exceeded,
            "{name}: reference exceeded mismatch"
        );
        assert_eq!(
            steps, expected_steps,
            "{name}: exhaust.rs's own step count ({steps}) disagrees with the independent reference ({expected_steps})"
        );
        if want_exceeded {
            assert_eq!(diags, vec!["T0055".to_string()], "{name}");
        } else {
            assert!(diags.is_empty(), "{name}: expected check-ok, got {diags:?}");
        }
    }

    // The design's "20 hand-built matrices": seeded random bool-tuple arm
    // sets (3-6 columns, 2-8 arms, a third wildcards) written out the way
    // the corpus files are, the plain count re-derived by the reference
    // above and compared EXACTLY — along with whether the budget was
    // exceeded, which `exhaust.rs` reports as T0055 and nothing else.
    let mut seed = 0x1e57_ab1e_u64;
    for k in 0..20 {
        seed = fors_index::splitmix64(seed);
        let n = 3 + (seed % 4) as usize;
        let narms = 2 + ((seed >> 8) % 7) as usize;
        let mut s = seed;
        let arms: Vec<Row> = (0..narms)
            .map(|_| {
                (0..n)
                    .map(|_| {
                        s = fors_index::splitmix64(s);
                        match s % 3 {
                            0 => None,
                            1 => Some(false),
                            _ => Some(true),
                        }
                    })
                    .collect()
            })
            .collect();
        let params: Vec<String> = (0..n).map(|i| format!("let b{i}: bool")).collect();
        let scrut: Vec<String> = (0..n).map(|i| format!("b{i}")).collect();
        let body: String = arms
            .iter()
            .enumerate()
            .map(|(i, r)| {
                let cells: Vec<&str> = r
                    .iter()
                    .map(|c| match c {
                        None => "_",
                        Some(true) => "true",
                        Some(false) => "false",
                    })
                    .collect();
                format!("        ({}) => {i},\n", cells.join(", "))
            })
            .collect();
        let src = format!(
            "module m;\n\nfn f({}) -> i32 {{\n    match ({}) {{\n{body}    }}\n}}\n",
            params.join(", "),
            scrut.join(", ")
        );
        let (diags, steps) = check_file_steps(src.as_bytes());
        let (expected_steps, exceeded) = ref_steps(&arms);
        assert_eq!(
            steps, expected_steps,
            "hand-built matrix {k}: exhaust.rs's own step count ({steps}) disagrees with the independent reference ({expected_steps})\n{src}"
        );
        assert_eq!(
            diags.contains(&"T0055".to_string()),
            exceeded,
            "hand-built matrix {k}: budget verdict\n{src}"
        );
    }
}

/// R53/R54's usefulness algorithm against brute-force enumeration of EVERY
/// value of a random small finite domain (design §13's I7 GATE row: "≤3
/// columns over enums ≤4 variants and bools, 10k random matrices"), seeded
/// deterministically so a failure reproduces. Domains nest — `bool`, unit
/// enums, tuples, structs matched by `{ }` payloads that omit fields, and
/// `Option` — up to three levels deep (`Option[Option[bool]]`,
/// `(Option[E3], bool)`), capped at 256 values so the enumeration stays
/// cheap. Each case asserts the exact diagnostic list AND its line:
/// `diag.rs`'s `PER_DECL_BUDGET` (design §10) caps a declaration at ONE
/// diagnostic and `exhaust::check_match` charges it in the order it
/// decides things — every unreachable arm in arm order, then the
/// missing-value witness — so the expectation is the FIRST thing that
/// order finds, at that arm's own line (T0054) or the `match`'s (T0053).
#[test]
fn usefulness_vs_brute_force_oracle() {
    #[derive(Clone)]
    enum Dom {
        Bool,
        /// `enum E<n> { V0, .. }`, `n` unit variants.
        Enum(u32),
        Tuple(Vec<Dom>),
        /// `struct P<k> { pub f0: bool, .. }`, matched by a `{ }` payload
        /// that may omit any field.
        Struct(u32),
        Opt(Box<Dom>),
    }

    #[derive(Clone)]
    enum Pat {
        Wild,
        Bool(bool),
        Variant(u32),
        Tuple(Vec<Pat>),
        /// One entry per field; `None` is an omitted field.
        Struct(Vec<Option<Pat>>),
        Some(Box<Pat>),
        NoneV,
    }

    /// Values are numbered `0..size`: tuples mixed-radix (first component
    /// least significant), structs bitwise, `Option` with `none` at 0 and
    /// `some(x)` at `1 + x`.
    fn size(d: &Dom) -> u64 {
        match d {
            Dom::Bool => 2,
            Dom::Enum(n) => *n as u64,
            Dom::Tuple(ds) => ds.iter().map(size).product(),
            Dom::Struct(k) => 1u64 << k,
            Dom::Opt(inner) => 1 + size(inner),
        }
    }

    fn covers(pat: &Pat, dom: &Dom, v: u64) -> bool {
        match (pat, dom) {
            (Pat::Wild, _) => true,
            (Pat::Bool(b), Dom::Bool) => (v == 1) == *b,
            (Pat::Variant(i), Dom::Enum(_)) => v == *i as u64,
            (Pat::Tuple(ps), Dom::Tuple(ds)) => {
                let mut rest = v;
                ps.iter().zip(ds).all(|(p, d)| {
                    let s = size(d);
                    let comp = rest % s;
                    rest /= s;
                    covers(p, d, comp)
                })
            }
            (Pat::Struct(fs), Dom::Struct(_)) => fs.iter().enumerate().all(|(i, f)| match f {
                None => true,
                Some(p) => covers(p, &Dom::Bool, (v >> i) & 1),
            }),
            (Pat::Some(p), Dom::Opt(inner)) => v >= 1 && covers(p, inner, v - 1),
            (Pat::NoneV, Dom::Opt(_)) => v == 0,
            _ => panic!("pattern/domain shape mismatch"),
        }
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = fors_index::splitmix64(self.0);
            self.0
        }
        fn range(&mut self, n: u32) -> u32 {
            (self.next() % n as u64) as u32
        }
        fn bool(&mut self) -> bool {
            self.next() & 1 == 1
        }
    }

    fn gen_dom(rng: &mut Rng, depth: u32) -> Dom {
        match rng.range(if depth == 0 { 3 } else { 6 }) {
            0 => Dom::Bool,
            1 => Dom::Enum(2 + rng.range(3)),
            2 => Dom::Struct(2 + rng.range(2)),
            3 => Dom::Tuple(
                (0..2 + rng.range(2))
                    .map(|_| gen_dom(rng, depth - 1))
                    .collect(),
            ),
            4 => Dom::Opt(Box::new(gen_dom(rng, depth - 1))),
            // The design's "enums-in-tuples", at any depth.
            _ => Dom::Tuple(vec![Dom::Enum(2 + rng.range(3)), Dom::Bool]),
        }
    }

    fn gen_pat(rng: &mut Rng, dom: &Dom) -> Pat {
        if rng.range(100) < 30 {
            return Pat::Wild;
        }
        match dom {
            Dom::Bool => Pat::Bool(rng.bool()),
            Dom::Enum(n) => Pat::Variant(rng.range(*n)),
            Dom::Tuple(ds) => Pat::Tuple(ds.iter().map(|d| gen_pat(rng, d)).collect()),
            Dom::Struct(k) => {
                let mut fs: Vec<Option<Pat>> = (0..*k)
                    .map(|_| (rng.range(100) < 60).then(|| gen_pat(rng, &Dom::Bool)))
                    .collect();
                // ch07 has no empty `{ }` payload and a bare struct name
                // is T0050 (R50), so at least one field is written.
                if fs.iter().all(Option::is_none) {
                    fs[0] = Some(Pat::Wild);
                }
                Pat::Struct(fs)
            }
            Dom::Opt(inner) => {
                if rng.range(3) == 0 {
                    Pat::NoneV
                } else {
                    Pat::Some(Box::new(gen_pat(rng, inner)))
                }
            }
        }
    }

    fn ty_src(d: &Dom) -> String {
        match d {
            Dom::Bool => "bool".to_string(),
            Dom::Enum(n) => format!("E{n}"),
            Dom::Tuple(ds) => {
                let parts: Vec<String> = ds.iter().map(ty_src).collect();
                format!("({})", parts.join(", "))
            }
            Dom::Struct(k) => format!("P{k}"),
            Dom::Opt(inner) => format!("Option[{}]", ty_src(inner)),
        }
    }

    /// Every declaration `d` needs, deduplicated, one per line.
    fn decls(d: &Dom, out: &mut Vec<String>) {
        let line = match d {
            Dom::Enum(n) => {
                let vs: Vec<String> = (0..*n).map(|i| format!("V{i}")).collect();
                Some(format!("enum E{n} {{ {} }}", vs.join(", ")))
            }
            Dom::Struct(k) => {
                let fs: Vec<String> = (0..*k).map(|i| format!("pub f{i}: bool")).collect();
                Some(format!("struct P{k} {{ {} }}", fs.join(", ")))
            }
            _ => None,
        };
        if let Some(l) = line
            && !out.contains(&l)
        {
            out.push(l);
        }
        match d {
            Dom::Tuple(ds) => ds.iter().for_each(|x| decls(x, out)),
            Dom::Opt(inner) => decls(inner, out),
            _ => {}
        }
    }

    /// `names` numbers the `let` bindings so each is distinct; a wildcard
    /// alternates between its two irrefutable spellings (design §7.8
    /// treats `_` and `let n` alike).
    fn pat_src(p: &Pat, dom: &Dom, names: &mut u32) -> String {
        match (p, dom) {
            (Pat::Wild, _) => {
                *names += 1;
                if names.is_multiple_of(2) {
                    "_".to_string()
                } else {
                    format!("let w{names}")
                }
            }
            (Pat::Bool(b), _) => b.to_string(),
            (Pat::Variant(i), _) => format!(".V{i}"),
            (Pat::Tuple(ps), Dom::Tuple(ds)) => {
                let parts: Vec<String> = ps
                    .iter()
                    .zip(ds)
                    .map(|(p, d)| pat_src(p, d, names))
                    .collect();
                format!("({})", parts.join(", "))
            }
            (Pat::Struct(fs), Dom::Struct(k)) => {
                let parts: Vec<String> = fs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, f)| {
                        f.as_ref()
                            .map(|p| format!("f{i}: {}", pat_src(p, &Dom::Bool, names)))
                    })
                    .collect();
                format!("P{k} {{ {} }}", parts.join(", "))
            }
            (Pat::Some(p), Dom::Opt(inner)) => format!("some({})", pat_src(p, inner, names)),
            (Pat::NoneV, _) => "none".to_string(),
            _ => panic!("pattern/domain shape mismatch"),
        }
    }

    struct Case {
        src: String,
        dom: Dom,
        arms: Vec<Pat>,
        match_line: u32,
        arm_lines: Vec<u32>,
    }

    /// The source, the domain and the arm patterns a random case decided,
    /// plus the line each arm and the `match` land on once `check_source`
    /// has prepended its two header lines.
    fn gen_case(rng: &mut Rng) -> Case {
        let dom = loop {
            let d = gen_dom(rng, 2);
            if size(&d) <= 256 {
                break d;
            }
        };
        let narms = 2 + rng.range(5) as usize;
        let arms: Vec<Pat> = (0..narms).map(|_| gen_pat(rng, &dom)).collect();
        let mut header = Vec::new();
        decls(&dom, &mut header);
        let mut line = 2 + header.len() as u32;
        let mut src = header.join("\n");
        if !header.is_empty() {
            src.push('\n');
        }
        src.push_str(&format!("fn f(let x: {}) -> i32 {{\n", ty_src(&dom)));
        line += 1;
        src.push_str("    match x {\n");
        line += 1;
        let match_line = line;
        let mut names = 0u32;
        let mut arm_lines = Vec::with_capacity(narms);
        for (i, p) in arms.iter().enumerate() {
            line += 1;
            arm_lines.push(line);
            src.push_str(&format!(
                "        {} => {i},\n",
                pat_src(p, &dom, &mut names)
            ));
        }
        src.push_str("    }\n}\n");
        Case {
            src,
            dom,
            arms,
            match_line,
            arm_lines,
        }
    }

    /// Exhaustiveness and per-arm usefulness by enumerating every value of
    /// the domain directly — the oracle `exhaust.rs`'s matrix algorithm is
    /// checked against. Returns the exhaustiveness bit and, in arm order,
    /// whether each arm is useful.
    fn ground_truth(dom: &Dom, arms: &[Pat]) -> (bool, Vec<bool>) {
        let n = size(dom);
        let mut covered = vec![false; n as usize];
        let mut useful = Vec::with_capacity(arms.len());
        for pat in arms {
            let mut arm_useful = false;
            for v in 0..n {
                if covers(pat, dom, v) && !covered[v as usize] {
                    arm_useful = true;
                    covered[v as usize] = true;
                }
            }
            useful.push(arm_useful);
        }
        (covered.iter().all(|&c| c), useful)
    }

    const CASES: usize = 10_000;
    let mut rng = Rng(0x5eed_c0de_1234_5678);
    let mut failures = Vec::new();
    let mut deepest = 0u32;
    let mut saw_struct = false;
    let mut saw_enum_in_tuple = false;
    for case in 0..CASES {
        let c = gen_case(&mut rng);
        fn depth(d: &Dom) -> u32 {
            match d {
                Dom::Tuple(ds) => 1 + ds.iter().map(depth).max().unwrap_or(0),
                Dom::Opt(inner) => 1 + depth(inner),
                _ => 1,
            }
        }
        deepest = deepest.max(depth(&c.dom));
        saw_struct |= matches!(c.dom, Dom::Struct(_));
        saw_enum_in_tuple |=
            matches!(&c.dom, Dom::Tuple(ds) if ds.iter().any(|d| matches!(d, Dom::Enum(_))));
        let (exhaustive, useful) = ground_truth(&c.dom, &c.arms);
        let want: Vec<(String, u32)> = match useful.iter().position(|&u| !u) {
            Some(i) => vec![("T0054".to_string(), c.arm_lines[i])],
            None if !exhaustive => vec![("T0053".to_string(), c.match_line)],
            None => Vec::new(),
        };
        let got = check_source_lines(&c.src);
        if got != want {
            failures.push(format!(
                "case {case}: want {want:?}, got {got:?}\n{}",
                c.src
            ));
        }
        if failures.len() >= 5 {
            break;
        }
    }
    assert!(
        failures.is_empty(),
        "oracle failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(deepest >= 3, "the generator never nested three levels deep");
    assert!(
        saw_struct && saw_enum_in_tuple,
        "the generator skipped a required shape"
    );
}

// ------------------------------------------------- I7 verification (2026-10-02)

/// R53: "a `const` pattern is the literal constructor of the constant's
/// comptime value ... covers exactly that one value". Before the repair
/// `lower::lower_const` gave a `Str` or negated-integer constant no value
/// at all, so `pat::check_pat_const` lowered it to a WILDCARD: `S => 1`
/// alone was accepted as exhaustive, and a `_` after it drew T0054.
#[test]
fn i7v_str_and_negative_const_patterns_are_one_value_constructors() {
    const S: &str = "const S: Str = \"x\";\n";
    assert_eq!(
        check_source(&format!(
            "{S}fn f(let s: Str) -> i32 {{ match s {{ S => 1 }} }}"
        )),
        vec!["T0053"]
    );
    assert_eq!(
        check_source(&format!(
            "{S}fn f(let s: Str) -> i32 {{ match s {{ \"x\" => 1, S => 2, _ => 0 }} }}"
        )),
        vec!["T0054"],
        "a constant and an equal literal are the same constructor"
    );
    assert!(
        check_source(&format!(
            "{S}fn f(let s: Str) -> i32 {{ match s {{ \"y\" => 1, S => 2, _ => 0 }} }}"
        ))
        .is_empty(),
        "two different strings are two constructors and the `_` is still useful"
    );
    const N: &str = "const N: i32 = -1;\n";
    assert_eq!(
        check_source(&format!(
            "{N}fn f(let n: i32) -> i32 {{ match n {{ N => 1 }} }}"
        )),
        vec!["T0053"]
    );
    assert_eq!(
        check_source(&format!(
            "{N}fn f(let n: i32) -> i32 {{ match n {{ N => 1, -1 => 2, _ => 0 }} }}"
        )),
        vec!["T0054"]
    );
    assert!(
        check_source(&format!(
            "{N}fn f(let n: i32) -> i32 {{ match n {{ N => 1, 1 => 2, _ => 0 }} }}"
        ))
        .is_empty()
    );
}

/// R50's `const` clause compares the constant's type with the scrutinee's
/// BARE type: an `imm i32` scrutinee matches an `i32` constant (before the
/// repair the qualified `TyId` differed and drew a spurious T0050), while
/// an `i64` constant against an `i32` scrutinee is still T0050.
#[test]
fn i7v_const_pattern_checks_against_the_bare_scrutinee_type() {
    assert!(
        check_source(
            "const LIMIT: i32 = 10;\nfn f(let n: imm i32) -> i32 { match n { LIMIT => 1, _ => 0 } }"
        )
        .is_empty()
    );
    assert_eq!(
        check_source(
            "const LIMIT: i64 = 10;\nfn f(let n: i32) -> i32 { match n { LIMIT => 1, _ => 0 } }"
        ),
        vec!["T0050"]
    );
}

/// R50: "a `{ }` payload names visible fields at most once each". A name
/// that is no field, and a field named twice, are each T0050 at the
/// `fpat` (before the repair both were silent — the unknown field even
/// made the arm a wildcard, so a later arm drew T0054 instead).
#[test]
fn i7v_field_payload_names_visible_fields_at_most_once() {
    const P: &str = "struct P { pub x: bool, pub y: bool }\n";
    assert_eq!(
        check_messages(&format!(
            "{P}fn f(let p: P) -> i32 {{ match p {{ P {{ x: true, x: false }} => 1, _ => 0 }} }}"
        )),
        vec!["T0050: the field `x` is named twice in this pattern"]
    );
    assert_eq!(
        check_messages(&format!(
            "{P}fn f(let p: P) -> i32 {{ match p {{ P {{ z: let q }} => 1, _ => 0 }} }}"
        )),
        vec!["T0050: there is no field `z` to match here"]
    );
    assert_eq!(
        check_messages(
            "enum S { rect { w: i32, h: i32 }, e }\nfn f(let s: S) -> i32 { match s { .rect { q: let q } => 1, _ => 0 } }"
        ),
        vec!["T0050: there is no field `q` to match here"]
    );
    assert!(
        check_source(&format!(
            "{P}fn f(let p: P) -> i32 {{ match p {{ P {{ y: true }} => 1, P {{ x: _ }} => 0 }} }}"
        ))
        .is_empty(),
        "omitted fields match anything; naming each once is fine"
    );
}

/// R50's "VISIBLE fields": a struct field without `pub` named by a `{ }`
/// pattern in another module is ch08 R11's N0011 — the same code and
/// wording `member::member_of` gives `p.hid` (row 49: member visibility
/// is ch08's code). In its own module the field is visible; a variant's
/// record fields have no `pub` of their own and are as visible as the
/// variant.
#[test]
fn i7v_private_field_pattern_across_modules_is_ch08_r11() {
    const LIB: &str = "pub struct P { pub x: i32, hid: i32 }\npub enum E { r { w: i32 }, u }\n";
    assert_eq!(
        check_modules(&[
            ("lib", LIB),
            (
                "main",
                "use lib.P;\nfn f(let p: P) -> i32 { match p { P { hid: let s } => s } }"
            ),
        ]),
        vec![("N0011".to_string(), "main".to_string())]
    );
    assert!(
        check_modules(&[
            ("lib", LIB),
            (
                "main",
                "use lib.P;\nuse lib.E;\nfn f(let p: P) -> i32 { match p { P { x: let s } => s } }\n\
                 fn g(let e: E) -> i32 { match e { .r { w: let w } => w, .u => 0 } }"
            ),
        ])
        .is_empty()
    );
    assert!(
        check_source(
            "struct P { pub x: i32, hid: i32 }\nfn f(let p: P) -> i32 { match p { P { hid: let s } => s } }"
        )
        .is_empty(),
        "visible in its own module"
    );
}

/// R53: "the diagnostic names one uncovered VALUE". A struct's or record
/// variant's witness is spelled field by field (before the repair a
/// struct's was just its type name, `P`), and a `Str` column's witness is
/// a string no arm already names (before the repair the candidates were
/// compared in a different spelling from the patterns, so `"other0"` was
/// offered as uncovered by a match whose first arm IS `"other0"`).
#[test]
fn i7v_witness_is_a_value_no_arm_covers() {
    assert_eq!(
        check_messages(
            "struct P { pub x: bool, pub y: bool }\nfn f(let p: P) -> i32 { match p { P { x: true } => 1, P { y: false } => 2 } }"
        ),
        vec![
            "T0053: the match is not exhaustive; for example, `P { x: false, y: true }` is not covered"
        ]
    );
    assert_eq!(
        check_messages(
            "enum S { rect { w: bool, h: bool }, e }\nfn f(let s: S) -> i32 { match s { .rect { w: true } => 1, .e => 0 } }"
        ),
        vec![
            "T0053: the match is not exhaustive; for example, `rect { w: false, h: false }` is not covered"
        ]
    );
    assert_eq!(
        check_messages("fn f(let s: Str) -> i32 { match s { \"other0\" => 1, \"other1\" => 2 } }"),
        vec!["T0053: the match is not exhaustive; for example, `\"other2\"` is not covered"]
    );
    assert_eq!(
        check_messages(
            "fn f(let o: Option[Option[bool]]) -> i32 { match o { some(some(true)) => 1, some(none) => 2, none => 3 } }"
        ),
        vec!["T0053: the match is not exhaustive; for example, `some(some(false))` is not covered"]
    );
}

/// Task D of I7 (the I6 verifier's finding): a NESTED explicit generic
/// argument parses as a `Bracket`, which `lower::nested_type_app` now
/// lowers like a `TypeApp` — one and two levels deep, in both directions.
#[test]
fn i7v_nested_explicit_generic_argument_lowers_at_every_depth() {
    // I8: `return a;` on a `let` parameter of unbounded rigid type is a
    // move out of a `let` parameter (ch01 R3, the clause
    // `copy-without-copyable-rejected` asserts), so the fixture carries
    // a `Copyable` bound. Nothing this probe measures changes.
    const ID: &str = "fn id[T: Copyable](let t: T) -> T { return t; }\n";
    assert_eq!(
        check_source(&format!(
            "{ID}fn f() -> Option[i64] {{ return id[Option[i64]](true); }}"
        )),
        vec!["T0026"]
    );
    assert!(
        check_source(&format!(
            "{ID}fn f() -> Option[i64] {{ return id[Option[i64]](some(1i64)); }}"
        ))
        .is_empty()
    );
    assert!(
        check_source(&format!(
            "{ID}fn f() -> Option[Option[i64]] {{ return id[Option[Option[i64]]](some(some(1i64))); }}"
        ))
        .is_empty()
    );
    assert_eq!(
        check_source(&format!(
            "{ID}fn f() -> Option[Option[i64]] {{ return id[Option[Option[i64]]](some(1i64)); }}"
        )),
        vec!["T0026"]
    );
}

// ------------------------------------------------- increment I8's probes

/// The fixture every move probe below is written against: a `Builder`
/// with a `sink self` consumer, a `let self` reader and an `inout self`
/// mutator, plus a non-`Copyable` wrapper to take a field out of.
const BUILDER: &str = "struct Builder { parts: i64 }\n\
     impl Builder {\n\
         fn finish(sink self: Builder) -> i64 { let p = self.parts; discard self; return p; }\n\
         fn peek(let self: Builder) -> i64 { return self.parts; }\n\
     }\n\
     struct Site { b: Builder, id: i64 }\n";

/// One mutation probe per mechanism the flow pass decides (design §11's
/// "typed mutations with expected code and site", brought forward for
/// I8's own rules). Each row is `(mechanism, rejected program, expected
/// code, the ONE mutation that repairs it)`: the rejected half proves the
/// rule fires, and the repaired half proves it fires for its own reason
/// and not because the fixture is ill-formed in some other way.
#[test]
fn every_flow_mechanism_fires_for_its_own_reason() {
    let rows: &[(&str, String, &str, String)] = &[
        (
            "ch01 R3: a move out of a `let` parameter",
            format!("{BUILDER}fn f(let d: Builder) -> i64 {{ return d.finish(); }}"),
            "O0003",
            format!("{BUILDER}fn f(sink d: Builder) -> i64 {{ return d.finish(); }}"),
        ),
        (
            "ch01 R4a(a): use after move",
            format!(
                "{BUILDER}fn f(sink b: Builder) -> i64 {{ let n = b.finish(); return n + b.peek(); }}"
            ),
            "O0004",
            format!("{BUILDER}fn f(sink b: Builder) -> i64 {{ let n = b.finish(); return n; }}"),
        ),
        (
            "ch01 R4a(a): a re-initialisation revives the place",
            format!(
                "{BUILDER}fn f(sink b: Builder) -> i64 {{ let n = b.finish(); return n + b.peek(); }}"
            ),
            "O0004",
            format!(
                "{BUILDER}fn f(sink b: Builder) -> i64 {{ let n = b.finish(); b = Builder {{ parts: 0 }}; return n + b.peek(); }}"
            ),
        ),
        (
            "ch01 R4a(b)/R8: a move inside a loop of a place declared outside it",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize) -> i64 {{ var t: i64 = 0; for i in 0 ..< n {{ t = t + b.finish(); }} return t; }}"
            ),
            "O0004",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize) -> i64 {{ var t: i64 = 0; for i in 0 ..< n {{ t = t + b.finish(); b = Builder {{ parts: 0 }}; }} return t; }}"
            ),
        ),
        (
            "ch01 R4a(b): a place declared INSIDE the loop may be moved there",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize) -> i64 {{ var t: i64 = 0; for i in 0 ..< n {{ t = t + b.finish(); }} return t; }}"
            ),
            "O0004",
            format!(
                "{BUILDER}fn f(let n: usize) -> i64 {{ var t: i64 = 0; for i in 0 ..< n {{ let c: Builder = Builder {{ parts: 1 }}; t = t + c.finish(); }} return t; }}"
            ),
        ),
        (
            "ch01 R4a(c): a partial move out of a field place",
            format!("{BUILDER}fn f(sink s: Site) -> i64 {{ return s.b.finish(); }}"),
            "O0004",
            format!("{BUILDER}fn f(sink b: Builder) -> i64 {{ return b.finish(); }}"),
        ),
        (
            "ch01 R4a(d): a move out of an `inout` parameter",
            format!("{BUILDER}fn f(inout d: Builder) -> i64 {{ return d.finish(); }}"),
            "O0004",
            format!("{BUILDER}fn f(inout d: Builder) -> i64 {{ return d.peek(); }}"),
        ),
        (
            "ch01 R4a(e): a closure body moving a place it captured",
            format!(
                "{BUILDER}fn f(sink b: Builder) -> i64 {{ let g: fn() -> i64 = || b.finish(); return g(); }}"
            ),
            "O0004",
            format!(
                "{BUILDER}fn f(sink b: Builder) -> i64 {{ let g: fn() -> i64 = || b.peek(); return g(); }}"
            ),
        ),
        (
            "ch01 R2: a `sink` argument needs `move`",
            format!(
                "{BUILDER}fn take(sink b: Builder) -> i64 {{ return b.finish(); }}\nfn f(sink b: Builder) -> i64 {{ return take(b); }}"
            ),
            "O0002",
            format!(
                "{BUILDER}fn take(sink b: Builder) -> i64 {{ return b.finish(); }}\nfn f(sink b: Builder) -> i64 {{ return take(move b); }}"
            ),
        ),
        (
            "ch01 R2: an `inout` argument needs `&`",
            "fn bump(inout x: i64) { x = x + 1; }\nfn f(inout n: i64) { bump(n); }".to_string(),
            "O0002",
            "fn bump(inout x: i64) { x = x + 1; }\nfn f(inout n: i64) { bump(&n); }".to_string(),
        ),
        (
            "ch01 R2: a `set` argument needs `&out`",
            "fn fill(set o: i64) { o = 7; }\nfn f() { var v: i64; fill(v); }".to_string(),
            "O0002",
            "fn fill(set o: i64) { o = 7; }\nfn f() { var v: i64; fill(&out v); }".to_string(),
        ),
        (
            "ch01 R2: a `let` argument carries no marker",
            "fn read(let x: i64) -> i64 { return x; }\nfn f(inout n: i64) -> i64 { return read(&n); }"
                .to_string(),
            "O0002",
            "fn read(let x: i64) -> i64 { return x; }\nfn f(inout n: i64) -> i64 { return read(n); }"
                .to_string(),
        ),
        (
            "ch01 R15d: a brand parameter used as the type of a value",
            "fn f[A: brand](sink x: A) { discard x; }".to_string(),
            "O0015",
            "struct Cell[T, A: brand] { v: T }\nfn f[A: brand](sink x: Cell[i64, A]) { discard x; }"
                .to_string(),
        ),
    ];
    let mut failures = Vec::new();
    for (what, bad, code, good) in rows {
        let got = check_source(bad);
        if got != vec![code.to_string()] {
            failures.push(format!("{what}: expected [{code}], got {got:?}"));
        }
        let fixed = check_source(good);
        if !fixed.is_empty() {
            failures.push(format!(
                "{what}: the repaired program must be accepted, got {fixed:?}"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "flow mechanism probes ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// ch01 Rule 8's round-6 note: the merge lattice is TWO-valued, with no
/// "maybe live" third element. A move made inside one branch of an `if`
/// is that branch's: a use in the SAME branch after the move is R4a(a),
/// a use in the sibling branch is not, and when both branches leave the
/// body nothing merges.
#[test]
fn a_move_in_one_branch_is_not_live_in_the_other() {
    let after_move_same_branch = format!(
        "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
         if c {{ let n = b.finish(); return n + b.peek(); }} return 0; }}"
    );
    assert_eq!(check_source(&after_move_same_branch), vec!["O0004"]);
    let sibling_branch = format!(
        "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
         if c {{ return b.finish(); }} else {{ return b.peek(); }} }}"
    );
    assert!(
        check_source(&sibling_branch).is_empty(),
        "got {:?}",
        check_source(&sibling_branch)
    );
}

/// ch01 Rule 8 proper (I8 verification, 2026-10-02): every path that
/// reaches a merge must agree on each place's liveness. A move on one
/// path through an `if`/`match` and not the other is the disagreement,
/// reported once at the move (O0008) whether or not the place is used
/// afterwards; a move on EVERY path leaves the place dead, so a use after
/// the merge is R4a(a); a path that leaves the body does not reach the
/// merge; a re-initialisation on only some paths disagrees the other way
/// round. Loops merge twice: at the head (R4a(b), against the entry
/// state, with a `continue` inside an alternative reaching it too) and at
/// the exit (the entry state against every `break`).
#[test]
fn every_path_must_agree_where_they_merge() {
    let rows: &[(&str, String, Vec<&str>)] = &[
        (
            "moved on one branch, used after the join",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
                 if c {{ let n = b.finish(); }} return b.peek(); }}"
            ),
            vec!["O0008"],
        ),
        (
            "moved on one branch, never used again: still a disagreement",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) {{ if c {{ let n = b.finish(); }} }}"
            ),
            vec!["O0008"],
        ),
        (
            "moved on both branches, then used",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
                 if c {{ let n = b.finish(); }} else {{ discard b; }} return b.peek(); }}"
            ),
            vec!["O0004"],
        ),
        (
            "moved on one arm of a `match`, the other arm leaves it live",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: i64) -> i64 {{ \
                 match n {{ 0 => {{ discard b; }} let o => {{ }} }} return 0; }}"
            ),
            vec!["O0008"],
        ),
        (
            "the moving branch returns: nothing merges",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
                 if c {{ let n = b.finish(); return n; }} return b.peek(); }}"
            ),
            vec![],
        ),
        (
            "re-initialised on the moving branch before the join",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
                 if c {{ let n = b.finish(); b = Builder {{ parts: n }}; }} return b.peek(); }}"
            ),
            vec![],
        ),
        (
            "dead before the `if`, re-initialised on one branch only",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
                 discard b; if c {{ b = Builder {{ parts: 0 }}; }} return 0; }}"
            ),
            vec!["O0008"],
        ),
        (
            "an `if` without `else` as the initialiser: the join precedes the `let`",
            format!(
                "{BUILDER}fn f(sink b: Builder, let c: bool) -> i64 {{ \
                 let x: i64 = if c {{ b.finish() }} else {{ 0 }}; return x; }}"
            ),
            vec!["O0008"],
        ),
        (
            "a loop re-initialises only on one branch: the head still disagrees",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize, let c: bool) -> i64 {{ \
                 var t: i64 = 0; for i in 0 ..< n {{ t = t + b.finish(); \
                 if c {{ b = Builder {{ parts: 0 }}; }} }} return t; }}"
            ),
            vec!["O0008"],
        ),
        (
            "a `continue` inside an alternative reaches the loop head",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize, let c: bool) -> i64 {{ \
                 for i in 0 ..< n {{ if c {{ let m = b.finish(); continue; }} }} return 0; }}"
            ),
            vec!["O0004"],
        ),
        (
            "a `break` after the move reaches the loop exit live-or-dead",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize) -> i64 {{ \
                 for i in 0 ..< n {{ let m = b.finish(); break; }} return 0; }}"
            ),
            vec!["O0008"],
        ),
        (
            "a `return` after the move reaches neither the head nor the exit",
            format!(
                "{BUILDER}fn f(sink b: Builder, let n: usize) -> i64 {{ \
                 for i in 0 ..< n {{ let m = b.finish(); return m; }} return b.peek(); }}"
            ),
            vec![],
        ),
        (
            "a `parallel` block runs once: its moves are the body's",
            format!(
                "{BUILDER}fn take(sink b: Builder) {{ discard b; }}\n\
                 fn f(sink b: Builder) -> i64 {{ parallel {{ spawn take(move b); }} return b.peek(); }}"
            ),
            vec!["O0004"],
        ),
        (
            "ch09 R46: the explicit form's message names the place, not the wrapper",
            format!(
                "{BUILDER}fn f(sink b: Builder) -> i64 {{ let n = (move b).finish(); return n + b.peek(); }}"
            ),
            vec!["O0004"],
        ),
    ];
    for (what, src, want) in rows {
        let got = check_source(src);
        assert_eq!(&got, want, "{what}:\n{src}");
    }
    let explicit = format!(
        "{BUILDER}fn f(sink b: Builder) -> i64 {{ let n = (move b).finish(); return n + b.peek(); }}"
    );
    let msgs = check_messages(&explicit);
    assert_eq!(msgs.len(), 1);
    assert!(
        msgs[0].contains("`b` was moved by the call `(move b).finish()`"),
        "got {:?}",
        msgs[0]
    );
}

/// ch09 R46's `Copyable` carve-out: a `Copyable` receiver is COPIED by a
/// `sink self` method, so the place stays usable and `move` is not
/// required at a `sink` argument either.
#[test]
fn a_copyable_receiver_is_copied_not_moved() {
    const P: &str = "struct P { x: i64 }\nimpl Copyable for P { }\nimpl P { fn take(sink self: P) -> i64 { return self.x; } }\n";
    assert!(
        check_source(&format!(
            "{P}fn f(let p: P) -> i64 {{ return p.take() + p.take(); }}"
        ))
        .is_empty()
    );
    assert!(
        check_source(&format!(
            "{P}fn eat(sink q: P) -> i64 {{ return q.x; }}\nfn f(let p: P) -> i64 {{ return eat(p) + p.x; }}"
        ))
        .is_empty()
    );
}

/// Metamorphic: the flow pass walks the tape in source order, so a
/// REORDERING of statements that touch disjoint places must not change
/// the diagnostic set. (It may change a diagnostic's position; the set of
/// codes is what this asserts, which is the property design §11 calls
/// metamorphic.)
#[test]
fn reordering_independent_statements_does_not_change_the_diagnostics() {
    fn permutations(stmts: &[&str]) -> Vec<String> {
        let n = stmts.len();
        let mut out = Vec::new();
        let mut idx: Vec<usize> = (0..n).collect();
        // Heap's algorithm, iterative, over at most 4 statements.
        let mut c = vec![0usize; n];
        out.push(idx.iter().map(|&i| stmts[i]).collect::<Vec<_>>().join(" "));
        let mut i = 0;
        while i < n {
            if c[i] < i {
                if i % 2 == 0 {
                    idx.swap(0, i);
                } else {
                    idx.swap(c[i], i);
                }
                out.push(idx.iter().map(|&k| stmts[k]).collect::<Vec<_>>().join(" "));
                c[i] += 1;
                i = 0;
            } else {
                c[i] = 0;
                i += 1;
            }
        }
        out
    }
    // Three independent statements, each on its own place, and a tail
    // that uses all three results.
    let clean = [
        "let x: i64 = a.finish();",
        "let y: i64 = b.finish();",
        "let z: i64 = c + 1;",
    ];
    let mut seen: Vec<Vec<String>> = Vec::new();
    for body in permutations(&clean) {
        let src = format!(
            "{BUILDER}fn f(sink a: Builder, sink b: Builder, let c: i64) -> i64 {{ {body} return x + y + z; }}"
        );
        seen.push(check_source(&src));
    }
    assert_eq!(seen.len(), 6);
    for got in &seen {
        assert!(
            got.is_empty(),
            "a permutation of independent statements changed the answer: {got:?}"
        );
    }
    // The same, with one statement that is an R3 violation: every
    // permutation must still report exactly that one diagnostic.
    let faulty = [
        "let x: i64 = a.finish();",
        "let y: i64 = d.finish();",
        "let z: i64 = c + 1;",
    ];
    let mut codes: Vec<Vec<String>> = Vec::new();
    for body in permutations(&faulty) {
        let src = format!(
            "{BUILDER}fn f(sink a: Builder, let d: Builder, let c: i64) -> i64 {{ {body} return x + y + z; }}"
        );
        codes.push(check_source(&src));
    }
    assert_eq!(codes.len(), 6);
    for got in &codes {
        assert_eq!(
            got,
            &vec!["O0003".to_string()],
            "a permutation changed the diagnostic set"
        );
    }
}

/// F7 (found by `std_checks_clean`, the first consumer-style check of
/// `std` under I8's rules): `lower::trait_ref` lowered every argument of a
/// trait application as a TYPE, so a brand parameter handed to a
/// brand-kinded trait slot — `std`'s `impl[A: brand] alloc.Allocator[A]
/// for Bump[A]`, nineteen times over — was ch01 R15d's "brand parameter
/// used as a type" (O0015). The slot's declared kind decides, exactly as
/// `type_args` already did for a nominal head; a type in a brand slot is
/// still rejected.
#[test]
fn f7_trait_ref_lowers_each_argument_by_its_declared_kind() {
    const TR: &str = "trait Tr[A: brand] { fn id(let self: Self) -> i64; }\n\
         struct Cell[A: brand] { v: i64 }\n";
    assert!(
        check_source(&format!(
            "{TR}impl[A: brand] Tr[A] for Cell[A] {{ fn id(let self: Self) -> i64 {{ return self.v; }} }}"
        ))
        .is_empty(),
        "a brand parameter in a brand-kinded trait slot is the declared use"
    );
    let got = check_source(&format!(
        "{TR}struct Plain {{ v: i64 }}\n\
         impl Tr[i64] for Plain {{ fn id(let self: Self) -> i64 {{ return self.v; }} }}"
    ));
    // ch01 R15d's "passing a non-brand type for [a brand parameter] MUST
    // be rejected" is not yet a diagnostic anywhere: `brand_arg` leaves
    // the slot open (`TY_ERROR`, silently) for a nominal head and, now, a
    // trait reference alike, and the impl header stays open with it. What
    // this fix guarantees is only that the type never reaches `param_ty`
    // as a brand-used-as-type.
    assert!(
        !got.contains(&"O0015".to_string()),
        "a type in a brand slot is not a brand-used-as-type: {got:?}"
    );
}

/// F7 (fmir-interpreter.md §4.1's gap, member.rs::user_index): `a[i]` on a
/// USER nominal type with exactly one matching `Index` impl now records
/// `MemberTarget::IndexImpl` so lowering has a fact to read, rather than
/// deciding the type and discarding which impl answered.
#[test]
fn f7_user_index_records_its_resolved_impl() {
    use fors_check::facts::MemberTarget;

    const SRC: &str = "\
struct Box { v: i64 }
impl Index[usize] for Box {
    type Output = i64;
    fn at(let self: Self, let i: usize) -> scoped(self) Self.Output { return self.v; }
}
impl IndexMut[usize] for Box {
    fn at_mut(inout self: Self, let i: usize) -> scoped(self) Self.Output { return self.v; }
}
fn read_it(let b: Box) -> i64 { return b[0]; }
fn write_it(inout b: Box) { b[0] = 2; }
";
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{SRC}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(
        parsed.diags.is_empty(),
        "probe must parse: {:?}",
        parsed.diags
    );
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    assert!(
        out.diagnostics.is_empty(),
        "probe must check clean: {:?}",
        out.diagnostics
            .iter()
            .map(|d| d.code.as_string())
            .collect::<Vec<_>>()
    );
    let defs = out.defs.as_ref().expect("defs");
    let at_def = defs
        .user_defs()
        .find(|(_, r)| r.name.is_some_and(|n| interner.resolve(n) == b"at"))
        .map(|(d, _)| d)
        .expect("Index::at's DefId");
    let at_mut_def = defs
        .user_defs()
        .find(|(_, r)| r.name.is_some_and(|n| interner.resolve(n) == b"at_mut"))
        .map(|(d, _)| d)
        .expect("IndexMut::at_mut's DefId");

    let find_index_impl = |fn_name: &[u8]| -> MemberTarget {
        let def = defs
            .user_defs()
            .find(|(_, r)| r.name.is_some_and(|n| interner.resolve(n) == fn_name))
            .map(|(d, _)| d)
            .unwrap_or_else(|| panic!("{} DefId", String::from_utf8_lossy(fn_name)));
        let (_, facts) = out
            .facts
            .iter()
            .find(|(d, _)| *d == def)
            .unwrap_or_else(|| panic!("{} BodyFacts", String::from_utf8_lossy(fn_name)));
        let (start, end) = facts.range();
        for node in start..end {
            if let m @ MemberTarget::IndexImpl { .. } = facts.member_of(node) {
                return m;
            }
        }
        panic!(
            "no MemberTarget::IndexImpl recorded in {}",
            String::from_utf8_lossy(fn_name)
        );
    };

    assert_eq!(
        find_index_impl(b"read_it"),
        MemberTarget::IndexImpl {
            at: at_def,
            at_mut: Some(at_mut_def)
        },
        "a read `b[0]` records `at` and the matching `at_mut`"
    );
    assert_eq!(
        find_index_impl(b"write_it"),
        MemberTarget::IndexImpl {
            at: at_def,
            at_mut: Some(at_mut_def)
        },
        "an assignment target `b[0] = 2` goes through the same `synth`, so it \
         records the same fact"
    );
}

// ------------------------------------------------- increment I8b probes
//
// Round-6 flow: ch01 R19c/R19d, R22-R22i, R23-R23f and the ch09 rows they
// amend (R10(c), R11, R23, R24, R50, R57). One MUTATION probe per
// mechanism — a program that differs from an accepted one by exactly the
// token the rule turns on — plus the three metamorphic tests design §13's
// I8b GATE names.

/// The prelude every linear probe shares: a declared-linear `Res` with a
/// `sink self` consumer, written once.
const RES: &str = "struct Res { fd: i32 }\n\
                   impl Linear for Res { }\n\
                   impl Res {\n\
                   fn open(let n: i32) -> Res { return Res { fd: n }; }\n\
                   fn close(sink self) { }\n\
                   fn poke(inout self) { }\n\
                   }\n";

/// ch01 R22a/R22d: the mutation is the `impl Linear` line itself. The same
/// body is silent without it and leaks with it, so the obligation comes
/// from the DECLARATION and from nothing else (R22: "whether a constructor
/// is linear is a fact of the constructor").
#[test]
fn the_impl_linear_line_is_what_creates_the_obligation() {
    const BODY: &str = "fn f() { var r: Res = Res.open(1); r.poke(); }\n";
    let without = check_source(&format!(
        "struct Res {{ fd: i32 }}\n\
         impl Res {{\n\
         fn open(let n: i32) -> Res {{ return Res {{ fd: n }}; }}\n\
         fn close(sink self) {{ }}\n\
         fn poke(inout self) {{ }}\n\
         }}\n{BODY}"
    ));
    assert!(
        without.is_empty(),
        "no `impl Linear`, no obligation: {without:?}"
    );
    let with = check_source(&format!("{RES}{BODY}"));
    assert_eq!(with, vec!["O0022"], "the `impl Linear` line turns it on");
}

/// ch01 R22a(b): linearity propagates into an aggregate, and the
/// aggregate's own consumption discharges the whole. The mutation is one
/// field type.
#[test]
fn linearity_propagates_into_an_aggregate_and_only_through_a_value_field() {
    let leaks = check_source(&format!(
        "{RES}struct Box {{ r: Res }}\n\
         fn f() {{ var b: Box = Box {{ r: Res.open(1) }}; }}\n"
    ));
    assert_eq!(leaks, vec!["O0022"], "`Box` is linear by inference");
    let behind_ref = check_source(&format!(
        "{RES}struct Keep {{ n: i32 }}\n\
         fn f() {{ var b: Keep = Keep {{ n: 1 }}; }}\n"
    ));
    assert!(
        behind_ref.is_empty(),
        "no linear field, no obligation: {behind_ref:?}"
    );
}

/// ch01 R22d: the discharge set is exactly (i)/(ii)/(iii). The mutation is
/// the verb: `r.close()` discharges, `discard r` and `consume r` do not.
#[test]
fn only_a_whole_place_move_discharges_an_obligation() {
    let moved = check_source(&format!(
        "{RES}fn f() {{ var r: Res = Res.open(1); r.close(); }}\n"
    ));
    assert!(
        moved.is_empty(),
        "an implicit receiver move discharges: {moved:?}"
    );
    for verb in ["discard r;", "consume r;"] {
        let got = check_source(&format!(
            "{RES}fn f() {{ var r: Res = Res.open(1); {verb} }}\n"
        ));
        assert_eq!(got, vec!["O0022"], "`{verb}` must not discharge");
    }
}

/// ch01 R22f / ch09 R10(c): the mutation is the `as dyn Tr`.
#[test]
fn a_linear_value_does_not_coerce_to_dyn() {
    const TR: &str = "trait Tr { fn go(let self); }\nimpl Tr for Res { fn go(let self) { } }\n";
    let erased = check_source(&format!(
        "{RES}{TR}fn f(sink r: Res) -> dyn Tr {{ return r as dyn Tr; }}\n"
    ));
    assert_eq!(erased, vec!["T0010"], "R22f: the obligation would vanish");
    let kept = check_source(&format!("{RES}{TR}fn f(sink r: Res) {{ r.close(); }}\n"));
    assert!(kept.is_empty(), "the same value consumed instead: {kept:?}");
}

/// ch01 R22g: a closure captures by ACCESS and never moves, so the
/// enclosing scope still owes the place. The mutation is whether the
/// closure's body touches `r` at all.
#[test]
fn a_closure_capture_leaves_the_obligation_with_the_enclosing_scope() {
    let owed = check_source(&format!(
        "{RES}fn f() {{ var r: Res = Res.open(1); let c: fn () = || {{ r.poke(); }}; c(); }}\n"
    ));
    assert_eq!(
        owed,
        vec!["O0022"],
        "still owed after the closure's last use"
    );
    let consumed = check_source(&format!(
        "{RES}fn f() {{ var r: Res = Res.open(1); let c: fn () = || {{ }}; c(); r.close(); }}\n"
    ));
    assert!(consumed.is_empty(), "{consumed:?}");
}

/// ch01 R23d(b)/R23b: `defer` consumes on every exit, `errdefer` on the
/// error exits only. The mutation is the one keyword.
#[test]
fn defer_consumes_on_every_exit_and_errdefer_only_on_error_exits() {
    const BODY: &str = "fn f() raises Err {\n\
                        var r: Res = Res.open(1);\n\
                        KW r.close();\n\
                        step()?;\n\
                        }\n";
    let prelude = format!("{RES}enum Err {{ boom }}\nfn step() raises Err {{ }}\n");
    let with_defer = check_source(&format!("{prelude}{}", BODY.replace("KW", "defer")));
    assert!(
        with_defer.is_empty(),
        "`defer` runs on both exits: {with_defer:?}"
    );
    let with_errdefer = check_source(&format!("{prelude}{}", BODY.replace("KW", "errdefer")));
    assert_eq!(
        with_errdefer,
        vec!["O0022"],
        "`errdefer` does not run on the normal exit"
    );
}

/// ch01 R23d(a): every place a deferred body mentions must be live at every
/// exit at which that body runs. The mutation is the extra `r.close();`.
#[test]
fn a_deferred_body_still_needs_the_place_it_mentions() {
    let ok = check_source(&format!(
        "{RES}fn f() {{ var r: Res = Res.open(1); defer r.close(); r.poke(); }}\n"
    ));
    assert!(ok.is_empty(), "{ok:?}");
    let moved = check_source(&format!(
        "{RES}fn f() {{ var r: Res = Res.open(1); defer r.close(); r.close(); }}\n"
    ));
    assert_eq!(moved, vec!["O0023"], "R23d(a)");
}

/// ch01 R23f / ch02 R7: a trap is not an exit and discharges nothing. The
/// mutation is which statement ends the body.
#[test]
fn a_trap_discharges_nothing() {
    let trapping = check_source(&format!(
        "{RES}fn f(let xs: Slice[i32], let i: usize) -> i32 {{\n\
         var r: Res = Res.open(1);\n\
         return xs[i];\n\
         }}\n"
    ));
    assert_eq!(
        trapping,
        vec!["O0022"],
        "the non-trapping path still owes `r`"
    );
    let consumed = check_source(&format!(
        "{RES}fn f(let xs: Slice[i32], let i: usize) -> i32 {{\n\
         var r: Res = Res.open(1);\n\
         r.close();\n\
         return xs[i];\n\
         }}\n"
    ));
    assert!(consumed.is_empty(), "{consumed:?}");
}

/// ch01 R22c / ch09 R57: the mutation is the bound. `Droppable`,
/// `Copyable` and `Iterator` each license the drop; `Linear` does not
/// ("`Linear` MAY be used as a bound, where it restricts instantiation and
/// adds NO operation").
#[test]
fn a_rigid_drop_needs_a_droppable_copyable_or_iterator_bound() {
    assert_eq!(check_source("fn f[T](sink x: T) { }\n"), vec!["T0057"]);
    assert_eq!(
        check_source("fn f[T: Linear](sink x: T) { }\n"),
        vec!["T0057"]
    );
    for bound in ["Droppable", "Copyable", "Iterator"] {
        let got = check_source(&format!("fn f[T: {bound}](sink x: T) {{ }}\n"));
        assert!(
            got.is_empty(),
            "`T: {bound}` licenses the drop, got {got:?}"
        );
    }
}

/// ch01 R22d(ii) / ch09 R50: the mutation is the sub-pattern. `let n`
/// binds the linear component, `_` and an omitted field drop it.
#[test]
fn a_pattern_must_bind_every_linear_component() {
    let bound = check_source(&format!(
        "{RES}struct Box {{ r: Res, n: i32 }}\n\
         fn f(sink b: Box) {{ match b {{ Box {{ r: let i, n: let k }} => {{ i.close(); }} }} }}\n"
    ));
    assert!(bound.is_empty(), "{bound:?}");
    let wild = check_source(&format!(
        "{RES}struct Box {{ r: Res, n: i32 }}\n\
         fn f(sink b: Box) {{ match b {{ Box {{ r: _, n: let k }} => {{ }} }} }}\n"
    ));
    assert_eq!(wild, vec!["O0022"], "`_` facing a linear component");
    let omitted = check_source(&format!(
        "{RES}struct Box {{ r: Res, n: i32 }}\n\
         fn f(sink b: Box) {{ match b {{ Box {{ n: let k }} => {{ }} }} }}\n"
    ));
    assert_eq!(omitted, vec!["O0022"], "an omitted linear field");
}

/// ch01 R19d: a closure over a LOCAL is a scoped value no function may
/// return. The mutation is whether the captured place is a local or a
/// parameter the result is `scoped(..)` to — here, nothing captured at all.
#[test]
fn a_closure_over_a_local_cannot_be_returned() {
    let captured = check_source(
        "fn f() -> fn (let i32) -> i32 {\n\
         let k: i32 = 3;\n\
         return |let x| x + k;\n\
         }\n",
    );
    assert_eq!(captured, vec!["O0019"], "R19/R19d");
    let closed = check_source(
        "fn f() -> fn (let i32) -> i32 {\n\
         return |let x| x + 3;\n\
         }\n",
    );
    assert!(
        closed.is_empty(),
        "a closure that captures nothing: {closed:?}"
    );
}

/// ch09 R12 with `U: Droppable` and `U := Res`, the mechanism
/// `adaptor-map-closure-returns-linear-rejected` tests — proved with the
/// adaptor trait supplied LOCALLY, because the ch09 harness checks each
/// file alone and `Iterator`'s provided `map` lives only in
/// `std/mem/seq.fors` (see `tests/data/pending_09.rs`).
#[test]
fn linear_closure_result_fails_its_droppable_bound() {
    let bad = check_source(&format!(
        "{RES}fn mapper[U: Droppable](let f: fn (sink i32) -> U) {{ }}\n\
         fn make(sink n: i32) -> Res {{ return Res.open(n); }}\n\
         fn g() {{ mapper(make); }}\n"
    ));
    assert_eq!(bad, vec!["T0012"], "`Res` is linear, so not `Droppable`");
    let good = check_source(&format!(
        "{RES}fn mapper[U: Droppable](let f: fn (sink i32) -> U) {{ }}\n\
         fn make(sink n: i32) -> i32 {{ return n; }}\n\
         fn g() {{ mapper(make); }}\n"
    ));
    assert!(good.is_empty(), "a droppable result: {good:?}");
}

/// The receiver-convention half of `adaptor-on-{field,inout}-receiver-
/// rejected`, with the adaptor trait supplied locally for the same reason.
#[test]
fn adaptor_receiver_conventions_are_decided_with_a_local_trait() {
    const TRAIT: &str = "trait Taker { fn take(sink self, let n: usize) -> Self; }\n\
                         struct It { n: usize }\n\
                         impl Taker for It { fn take(sink self, let n: usize) -> It { return self; } }\n\
                         struct Holder { it: It }\n";
    // A `sink self` method called on a FIELD place is R4a(c)'s partial
    // move, which is what the corpus file asserts.
    let field = check_source(&format!(
        "{TRAIT}fn f(sink h: Holder) -> It {{ return h.it.take(2); }}\n"
    ));
    assert_eq!(field, vec!["O0004"], "a `sink self` move out of a field");
    // The same call on an `inout` parameter is R4a(d).
    let inout = check_source(&format!(
        "{TRAIT}fn f(inout it: It) -> It {{ return it.take(2); }}\n"
    ));
    assert_eq!(inout, vec!["O0004"], "a `sink self` move out of an `inout`");
    let owned = check_source(&format!(
        "{TRAIT}fn f(sink it: It) -> It {{ return it.take(2); }}\n"
    ));
    assert!(owned.is_empty(), "the owning form is legal: {owned:?}");
}

/// design §13's I8b GATE: `lin_is_memoised_and_terminates` over ch09 R14's
/// recursive shapes. `lin` descends into fields and payloads but never into
/// `Own`, `Ref`, `Arena`, `Slice`, `rawptr`, `fn` or `dyn`, which is the
/// whole of R22a's finiteness argument — so a type that is recursive
/// THROUGH one of those answers, and answers once.
#[test]
fn lin_is_memoised_and_terminates() {
    // A list recursive through `Own`: `lin` stops at `Own`, which is
    // linear by language rule, so the answer is immediate.
    let list = check_source(
        "struct Node[A: brand] { next: Option[Own[Node[A], A]], n: i32 }\n\
         fn f[A: brand](sink x: Node[A]) { }\n",
    );
    assert_eq!(list, vec!["O0022"], "linear through `Own`, decided once");
    // Mutual recursion through `Ref`, which `lin` never enters.
    let pair = check_source(
        "struct Ay[B: brand] { b: Option[Ref[Bee[B], B]], n: i32 }\n\
         struct Bee[B: brand] { a: Option[Ref[Ay[B], B]], n: i32 }\n\
         fn f[B: brand](sink x: Ay[B]) { }\n",
    );
    assert!(pair.is_empty(), "`Ref` is never linear: {pair:?}");
    // The same question asked many times in one build gives one answer
    // and no blow-up: twelve bodies, twelve identical decisions.
    let mut many = String::from(RES);
    for i in 0..12 {
        many.push_str(&format!(
            "fn f{i}() {{ var r: Res = Res.open({i}); r.close(); }}\n"
        ));
    }
    assert!(check_source(&many).is_empty(), "memoised across bodies");
}

/// design §13's I8b GATE: the merge lattice is still TWO-VALUED (ch01 R8's
/// round-6 note forbids a third state, a "maybe live" and a drop flag).
/// The statement from the outside: a place consumed on one path and not the
/// other is the disagreement, reported ONCE; consuming on both paths
/// resolves it; and adding the linear obligation does not introduce a
/// third answer — the same program with a NON-linear type is accepted or
/// rejected by exactly the same clause.
#[test]
fn linear_merge_has_no_third_state() {
    let disagree = check_source(&format!(
        "{RES}fn f(let n: i32) {{\n\
         var r: Res = Res.open(1);\n\
         if n == 0 {{ r.close(); }}\n\
         }}\n"
    ));
    assert_eq!(
        disagree.len(),
        1,
        "one disagreement, one diagnostic: {disagree:?}"
    );
    let both = check_source(&format!(
        "{RES}fn f(let n: i32) {{\n\
         var r: Res = Res.open(1);\n\
         if n == 0 {{ r.close(); }} else {{ r.close(); }}\n\
         }}\n"
    ));
    assert!(both.is_empty(), "agreement on both paths: {both:?}");
    // The same shape on a NON-linear, non-`Copyable` type: R8's own
    // disagreement, the same single diagnostic, no extra state.
    let plain = check_source(
        "struct S { n: i32 }\n\
         fn sink_it(sink s: S) { }\n\
         fn f(let n: i32) {\n\
         var s: S = S { n: 1 };\n\
         if n == 0 { sink_it(move s); }\n\
         sink_it(move s);\n\
         }\n",
    );
    assert_eq!(plain.len(), 1, "R8's own disagreement: {plain:?}");
}

/// design §13's I8b GATE, ch09 R59: no linear error depends on an
/// instantiation. `lin` is decided from the DECLARATION, so a body's
/// linear diagnostics are identical however many ways its generic callees
/// are instantiated, and a generic body's own rigid-drop answer never
/// changes when a linear argument is supplied at a call.
#[test]
fn no_linear_error_depends_on_instantiation() {
    const BAD: &str = "fn drop_it[T](sink x: T) { }\n";
    let alone = check_source(BAD);
    assert_eq!(alone, vec!["T0057"], "R22c at the definition");
    let linear = format!("{RES}{BAD}");
    let once = check_source(&format!("{linear}fn u1() {{ drop_it(move Res.open(1)); }}"));
    let twice = check_source(&format!(
        "{linear}fn u1() {{ drop_it(move Res.open(1)); }}\n\
         fn u2() {{ drop_it(move 1); }}"
    ));
    let three = check_source(&format!(
        "{linear}fn u1() {{ drop_it(move Res.open(1)); }}\n\
         fn u2() {{ drop_it(move 1); }}\n\
         fn u3() {{ drop_it(move \"x\"); }}"
    ));
    assert_eq!(once, twice, "an instantiation changed the diagnostics");
    assert_eq!(twice, three, "an instantiation changed the diagnostics");
    assert_eq!(
        once,
        vec!["T0057".to_string()],
        "exactly the definition's own diagnostic, whatever the callers"
    );
    // The mirror: a body that is well-typed at its definition stays
    // silent however linear its instantiations are.
    const GOOD: &str = "fn pass[T](sink x: T) -> T { return move x; }\n";
    let g = format!("{RES}{GOOD}");
    assert!(
        check_source(&format!(
            "{g}fn u1() {{ var r: Res = pass(move Res.open(1)); r.close(); }}"
        ))
        .is_empty(),
        "a linear instantiation of a clean generic body"
    );
}

// ------------------------------------- I8b verifier's repairs, pinned

/// ch01 R22h at the `}` of a scope that sits INSIDE an outer `let`'s
/// initialiser: an arm's pattern binding, or a local of a closure body,
/// is owed at its own scope's exits, not deferred to the enclosing
/// statement. The mutation is the `r.close()` inside that inner scope.
#[test]
fn a_binding_inside_an_outer_let_initialiser_is_owed_at_its_own_scope() {
    let arm = check_source(&format!(
        "{RES}fn f(sink o: Option[Res]) -> i32 {{\n\
         let v: i32 = match o {{ some(let r) => 1, none => 2 }};\n\
         return v;\n}}\n"
    ));
    assert_eq!(arm, vec!["O0022"], "an arm expression's binding leaks");
    let arm_block = check_source(&format!(
        "{RES}fn f(sink o: Option[Res]) -> i32 {{\n\
         let v: i32 = match o {{ some(let r) => {{ 1 }} none => {{ 2 }} }};\n\
         return v;\n}}\n"
    ));
    assert_eq!(arm_block, vec!["O0022"], "an arm block's binding leaks");
    let arm_ok = check_source(&format!(
        "{RES}fn f(sink o: Option[Res]) -> i32 {{\n\
         let v: i32 = match o {{ some(let r) => {{ r.close(); 1 }} none => {{ 2 }} }};\n\
         return v;\n}}\n"
    ));
    assert!(arm_ok.is_empty(), "consumed in the arm: {arm_ok:?}");
    let closure = check_source(&format!(
        "{RES}fn f() {{ let c: fn () = || {{ var r: Res = Res.open(1); r.poke(); }}; c(); }}\n"
    ));
    assert_eq!(closure, vec!["O0022"], "a closure body's local leaks");
    let closure_ok = check_source(&format!(
        "{RES}fn f() {{ let c: fn () = || {{ var r: Res = Res.open(1); r.close(); }}; c(); }}\n"
    ));
    assert!(
        closure_ok.is_empty(),
        "consumed in the closure: {closure_ok:?}"
    );
    // The `let`'s own `?` still owes nothing for the binding it introduces.
    let own = check_source(&format!(
        "{RES}enum Err {{ boom }}\n\
         fn mk() -> Res raises Err {{ return Res.open(3); }}\n\
         fn f() raises Err {{ let s: Res = mk()?; s.close(); }}\n"
    ));
    assert!(own.is_empty(), "not yet bound at its own `?`: {own:?}");
}

/// ch01 R22h's "a call result that is not bound": a linear temporary in a
/// call position that does not consume it — the receiver of a `let self`
/// method, an argument to a `let` parameter — dies at the call. The
/// mutation is the convention of the position: `sink` consumes.
#[test]
fn a_linear_temporary_in_a_non_consuming_call_position_is_a_leak() {
    const PEEK: &str = "impl Res { fn peek(let self) -> i32 { return 0; } }\n";
    let recv = check_source(&format!(
        "{RES}{PEEK}fn f() -> i32 {{ return Res.open(1).peek(); }}\n"
    ));
    assert_eq!(recv, vec!["O0022"], "a `let self` receiver temporary");
    let recv_sink = check_source(&format!("{RES}fn f() {{ Res.open(1).close(); }}\n"));
    assert!(
        recv_sink.is_empty(),
        "a `sink self` receiver consumes: {recv_sink:?}"
    );
    let arg = check_source(&format!(
        "{RES}fn use_it(let r: Res) {{ }}\nfn f() {{ use_it(Res.open(1)); }}\n"
    ));
    assert_eq!(arg, vec!["O0022"], "a `let` argument temporary");
    let arg_sink = check_source(&format!(
        "{RES}fn h(sink r: Res) {{ r.close(); }}\nfn f() {{ h(Res.open(1)); }}\n"
    ));
    assert!(
        arg_sink.is_empty(),
        "a `sink` argument consumes: {arg_sink:?}"
    );
    // A PLACE in the same position is not a temporary: it stays owed by
    // its binding, which consumes it afterwards.
    let place = check_source(&format!(
        "{RES}{PEEK}fn f() {{ var r: Res = Res.open(1); let k: i32 = r.peek(); r.close(); }}\n"
    ));
    assert!(place.is_empty(), "a place receiver: {place:?}");
}

/// ch01 R22d: a `sink self` receiver is R22i's consumer of its own HEAD
/// and does not owe that, but a linear COMPONENT of `self` (R22a(b)) is
/// consumed only by a move or by a destructuring that binds it. The
/// mutation is the field's type.
#[test]
fn a_sink_self_receiver_owes_its_linear_components() {
    let plain = check_source(&format!(
        "{RES}struct P {{ n: i32 }} impl Linear for P {{ }} impl P {{ fn close(sink self) {{ }} }}\n"
    ));
    assert!(plain.is_empty(), "no linear component: {plain:?}");
    let inferred = check_source(&format!(
        "{RES}struct W {{ r: Res }} impl W {{ fn close(sink self) {{ }} }}\n"
    ));
    assert_eq!(inferred, vec!["O0022"], "an inferred-linear `W` drops `r`");
    let declared = check_source(&format!(
        "{RES}struct C {{ r: Res, n: i32 }} impl Linear for C {{ }} impl C {{ fn close(sink self) {{ }} }}\n"
    ));
    assert_eq!(declared, vec!["O0022"], "a declared-linear `C` drops `r`");
    let payload = check_source(&format!(
        "{RES}enum E {{ a(Res), b }} impl Linear for E {{ }} impl E {{ fn close(sink self) {{ }} }}\n"
    ));
    assert_eq!(payload, vec!["O0022"], "a payload is a component too");
    let destructured = check_source(&format!(
        "{RES}struct C {{ r: Res, n: i32 }} impl Linear for C {{ }} impl C {{\n\
         fn close(sink self) {{ match self {{ C {{ r: let x, n: let k }} => {{ x.close(); }} }} }} }}\n"
    ));
    assert!(
        destructured.is_empty(),
        "destructuring consumes: {destructured:?}"
    );
}
