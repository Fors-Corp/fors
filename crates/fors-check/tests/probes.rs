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
    const G: &str = "fn g[T](let a: T) -> T { return a; }\n";
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
    const B: &str = "struct Box[T] { v: T }\n\
         impl[T] Index[usize] for Box[T] {\n\
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
    const G: &str = "fn g[T](let a: T) -> T { return a; }\n";
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
