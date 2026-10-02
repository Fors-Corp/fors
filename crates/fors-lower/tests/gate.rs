//! F1 gate tests: `BodyFacts`-driven lowering + interpreter core.
//!
//! Each test mirrors one row of the F1 gate list (design §9, "F1"): the
//! source checks clean with I3.5+I4a facts only, lowers without diagnostics,
//! verifies clean under `fors-fmir::verify`, and runs to the pinned
//! observable — `return` with exact stdout bytes, or a trap of the pinned
//! kind. The rejection tests pin the F1 scope edge: generics, `defer`,
//! projections-era syntax, loops, `match`, closures and const refs each
//! produce a clean [`LowerError`](fors_lower::LowerError), never a panic.

use fors_index::{Interner, Segments};
use fors_interp::{Config, Exit, Outcome, ProgFn, Program, run};
use fors_lower::{LowerDiag, LowerError, lower_build};
use fors_resolve::FileInput;
use fors_syntax::parse_file;

const OUT_PRELUDE: &str = "struct Out { n: i64 }\nimpl Out { fn write_line(inout self: Out, let s: Str) { self.n = 1; } }\n";

struct Built {
    outcome: Option<Outcome>,
    lower_diags: Vec<LowerDiag>,
    check_diags: Vec<String>,
}

fn build(src: &str) -> Built {
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{OUT_PRELUDE}{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(
        parsed.diags.is_empty(),
        "fixture must parse: {:?}",
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
    let check_diags: Vec<String> = out.diagnostics.iter().map(|d| d.code.as_string()).collect();
    let lowered = lower_build(&inputs, &out, &mut interner);
    if !check_diags.is_empty() || !lowered.diags.is_empty() {
        return Built {
            outcome: None,
            lower_diags: lowered.diags,
            check_diags,
        };
    }
    for f in &lowered.fns {
        let diags = fors_fmir::verify::verify(&f.decl);
        assert!(
            diags.is_empty(),
            "lowered {} must verify clean: {diags:?}",
            f.name
        );
    }
    let fns: Vec<ProgFn> = lowered
        .fns
        .into_iter()
        .map(|f| ProgFn {
            name: f.name,
            decl: f.decl,
            strings: f.strings,
            intrinsics: f.intrinsics,
        })
        .collect();
    let prog = Program::entry_by_name(fns, "main", Config::v0_1()).expect("a main");
    let outcome = run(&prog, &out.fir.tys).expect("well-formed program runs");
    Built {
        outcome: Some(outcome),
        lower_diags: Vec::new(),
        check_diags: Vec::new(),
    }
}

/// Runs `main` end to end; panics unless checking, lowering and running
/// are all clean.
fn run_main(src: &str) -> Outcome {
    let built = build(src);
    assert!(
        built.check_diags.is_empty(),
        "check diags: {:?}",
        built.check_diags
    );
    assert!(
        built.lower_diags.is_empty(),
        "lower diags: {:?}",
        built.lower_diags
    );
    built.outcome.expect("an outcome")
}

fn run_ok(src: &str) {
    let out = run_main(src);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(
        out.stdout,
        b"ok\n",
        "stdout was {:?}",
        String::from_utf8_lossy(&out.stdout)
    );
}

fn run_trap(src: &str, kind: fors_fmir::op::TrapKind) {
    let out = run_main(src);
    assert_eq!(
        out.exit,
        Exit::Trap(kind),
        "stdout was {:?}",
        String::from_utf8_lossy(&out.stdout)
    );
}

fn lower_error(src: &str) -> LowerError {
    let built = build(src);
    assert!(
        built.check_diags.is_empty(),
        "check diags: {:?}",
        built.check_diags
    );
    assert_eq!(
        built.lower_diags.len(),
        1,
        "lower diags: {:?}",
        built.lower_diags
    );
    built.lower_diags.into_iter().next().unwrap().error
}

fn build_raw(src: &str) -> Built {
    build(src)
}

// -- literals, arithmetic, calls -------------------------------------------

#[test]
fn gate_literals() {
    run_ok(
        "fn main(inout out: Out) { if 1 + 2 == 3 and true { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_arith_add_sub_mul() {
    run_ok(
        "fn main(inout out: Out) { var r: i32 = (10 - 3) * 2 + 1; if r == 15 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_div_rem_neg() {
    run_ok(
        "fn main(inout out: Out) { if 7 / 2 == 3 and 7 % 3 == 1 and 0 - 7 / 2 == -3 and (0 - 7) % 2 == -1 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_neg() {
    run_ok(
        "fn neg(let a: i32) -> i32 { return 0 - a; }\nfn main(inout out: Out) { if neg(5) == (0 - 5) and neg(0 - 3) == 3 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_calls_direct() {
    run_ok(
        "fn id(let a: i32) -> i32 { return a; }\nfn add(let a: i32, let b: i32) -> i32 { return a + b; }\nfn main(inout out: Out) { if add(id(20), id(1)) == 21 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_method_calls_with_mutation() {
    run_ok(
        "struct C { n: i64 }\nimpl C { fn bump(inout self: C) { self.n = self.n + 1; } fn get(let self: C) -> i64 { return self.n; } }\nfn main(inout out: Out) { var c: C = C { n: 41 }; c.bump(); if c.get() == 42 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_qualified_method_call() {
    run_ok(
        "struct C { r: f64 }\nimpl C { fn twice(let self: C) -> f64 { return self.r + self.r; } }\nfn main(inout out: Out) { var c: C = C { r: 2.5 }; if C.twice(c) == 5.0 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

// -- fields -----------------------------------------------------------------

#[test]
fn gate_field_reads() {
    run_ok(
        "struct P { x: i32, y: i64 }\nfn main(inout out: Out) { var p: P = P { x: 1, y: 2 }; if p.x + 1 == 2 and p.y == 2 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_field_order_follows_declaration() {
    // Source order (`y` first) must not leak into the value: reads follow
    // the declaration order through D4's field indices.
    run_ok(
        "struct P { x: i32, y: i64 }\nfn main(inout out: Out) { var p: P = P { y: 20, x: 10 }; if p.x == 10 and p.y == 20 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_struct_rebind() {
    run_ok(
        "struct P { x: i32 }\nfn main(inout out: Out) { var p: P = P { x: 1 }; p = P { x: 2 }; if p.x == 2 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_field_write() {
    run_ok(
        "struct P { x: i32 }\nfn main(inout out: Out) { var p: P = P { x: 1 }; p.x = 9; if p.x == 9 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

// -- control flow ------------------------------------------------------------

#[test]
fn gate_if_else() {
    run_ok(
        "fn f(let x: i32) -> i32 { if x == 1 { return 10; } else { return 20; } }\nfn main(inout out: Out) { if f(1) == 10 and f(2) == 20 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_if_no_else() {
    run_ok(
        "fn main(inout out: Out) { var x: i32 = 1; if x == 1 { x = 10; } if x == 10 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_nested_if() {
    run_ok(
        "fn main(inout out: Out) { var x: i32 = 2; if x == 1 { out.write_line(\"fail\"); } else { if x == 2 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } } }\n",
    );
}

#[test]
fn gate_reassign() {
    run_ok(
        "fn main(inout out: Out) { var y: i32 = 5; y = y - 1; if y == 4 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_bool_ops() {
    run_ok(
        "fn main(inout out: Out) { if true and not false and (false or true) { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_cmp_signed_unsigned() {
    run_ok(
        "fn main(inout out: Out) { var s: i32 = 0 - 1; var u: u8 = 255; if s < 0 and u > 0 and s != 0 and u == 255 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

// -- conversions ---------------------------------------------------------------

#[test]
fn gate_checked_as_exact() {
    run_ok(
        "fn main(inout out: Out) { var x: u32 = 44; var y: u8 = x as u8; if y == 44u8 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_implicit_widen_with_as() {
    run_ok(
        "fn f(let x: u8) -> u32 { var y: u32 = x as u32; return y; }\nfn main(inout out: Out) { if f(5u8) == 5 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_int_fixed_width_i64() {
    run_ok(
        "fn f(let x: i64) -> i64 { return x; }\nfn main(inout out: Out) { if f(42) == 42 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

// -- floats ---------------------------------------------------------------------

#[test]
fn gate_float_no_fma() {
    // Corpus `float-default-no-fma-run-ok`: the interpreter computes the
    // strict unfused value; the fused answer would fail this comparison.
    run_ok(
        "fn main(inout out: Out) { var a: f64 = 1.6394267984578836; var b: f64 = 1.025010755222667; var c: f64 = -1.6804301008195948; var r: f64 = a * b + c; if r == -2.220446049250313e-16 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_float_basic() {
    run_ok(
        "fn main(inout out: Out) { var a: f64 = 1.5; if a * 2.0 + 1.0 == 4.0 and a - 0.5 == 1.0 and a / 0.5 == 3.0 and 0.0 - a == -1.5 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

#[test]
fn gate_float_f32() {
    run_ok(
        "fn main(inout out: Out) { var a: f32 = 1.5; if a + 1.0 == 2.5 { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

// -- shifts -----------------------------------------------------------------------

#[test]
fn gate_shifts_basic() {
    run_ok(
        "fn main(inout out: Out) { var x: u8 = 1; var s: i32 = 0 - 8; if (x << 7) == 128u8 and (128u8 >> 7) == 1u8 and (s >> 2) == (0 - 2) { out.write_line(\"ok\"); } else { out.write_line(\"fail\"); } }\n",
    );
}

// -- strings and output ------------------------------------------------------------

#[test]
fn gate_write_two_lines() {
    let out =
        run_main("fn main(inout out: Out) { out.write_line(\"a\"); out.write_line(\"b\"); }\n");
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"a\nb\n");
}

#[test]
fn gate_str_through_call() {
    let out = run_main(
        "fn echo(let s: Str) -> Str { return s; }\nfn main(inout out: Out) { out.write_line(echo(\"hi\")); }\n",
    );
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"hi\n");
}

// -- traps --------------------------------------------------------------------------

#[test]
fn gate_trap_overflow_add() {
    run_trap(
        "fn main() { var x: i32 = 2147483647; var y: i32 = 1; var z: i32 = x + y; }\n",
        fors_fmir::op::TrapKind::Overflow,
    );
}

#[test]
fn gate_trap_overflow_sub() {
    run_trap(
        "fn main() { var x: i32 = 0 - 2147483647 - 1; var z: i32 = x - 1; }\n",
        fors_fmir::op::TrapKind::Overflow,
    );
}

#[test]
fn gate_trap_overflow_mul() {
    run_trap(
        "fn main() { var x: i32 = 1000000; var z: i32 = x * x; }\n",
        fors_fmir::op::TrapKind::Overflow,
    );
}

#[test]
fn gate_trap_overflow_main() {
    // The `02-failure/trap-overflow` shape: the overflow is the program.
    run_trap(
        "fn f(let x: i32) -> i32 { return x + 1; }\nfn main() { var z: i32 = f(2147483647); }\n",
        fors_fmir::op::TrapKind::Overflow,
    );
}

#[test]
fn gate_trap_div_zero() {
    run_trap(
        "fn main() { var x: i32 = 10; var y: i32 = 0; var z: i32 = x / y; }\n",
        fors_fmir::op::TrapKind::DivZero,
    );
}

#[test]
fn gate_trap_shift_width() {
    run_trap(
        "fn main() { var x: u8 = 1; var n: u8 = 8; var z: u8 = x << n; }\n",
        fors_fmir::op::TrapKind::Shift,
    );
}

#[test]
fn gate_trap_checked_conversion() {
    run_trap(
        "fn main() { var x: u32 = 300; var y: u8 = x as u8; }\n",
        fors_fmir::op::TrapKind::CheckedConversion,
    );
}

#[test]
fn gate_trap_min_div_neg1_is_overflow() {
    // Design §11.1 Q4: representability, not a zero divisor. (The `i64`
    // suffix matters: unsuffixed literals synthesize `i32`.)
    run_trap(
        "fn main() { var m: i64 = 0i64 - 9223372036854775807i64 - 1i64; var z: i64 = m / (0i64 - 1i64); }\n",
        fors_fmir::op::TrapKind::Overflow,
    );
}

#[test]
fn gate_trap_min_rem_neg1_is_overflow() {
    run_trap(
        "fn main() { var m: i64 = 0i64 - 9223372036854775807i64 - 1i64; var z: i64 = m % (0i64 - 1i64); }\n",
        fors_fmir::op::TrapKind::Overflow,
    );
}

// -- scope edges: clean diagnostics, never panics --------------------------------------

#[test]
fn gate_reject_generic_fn() {
    // The `Copyable` bound is ch01 R3's, not this gate's: returning a
    // `let` parameter of unbounded rigid type is a move out of a `let`
    // parameter, which the checker's I8 flow pass now reports (ch09's
    // `copy-without-copyable-rejected` is the same program). The gate
    // here is that LOWERING refuses a generic `fn`, so the fixture has
    // to be checked-clean first.
    assert!(matches!(
        lower_error("fn id[T: Copyable](let a: T) -> T { return a; }\nfn main() { }\n"),
        LowerError::Generic(_)
    ));
}

#[test]
fn gate_reject_generic_call() {
    // I5 TYPES the call, so the caller is checked-clean now; lowering
    // still refuses it, because monomorphisation is ch03 R16-R18's and
    // the generic callee itself answers `Generic` (see above), so there
    // would be no body to call.
    let built = build_raw(
        "fn g[T: Copyable](let a: T) -> T { return a; }\nfn f() -> i32 { var y: i32 = g(1); return y; }\nfn main() { }\n",
    );
    assert!(
        built.check_diags.is_empty(),
        "check diags: {:?}",
        built.check_diags
    );
    let f = built
        .lower_diags
        .iter()
        .find(|d| d.name == "f")
        .expect("an f diag");
    assert!(
        matches!(f.error, LowerError::Generic(_)),
        "got {:?}",
        f.error
    );
}

#[test]
fn gate_reject_defer() {
    assert!(matches!(
        lower_error("fn g() { }\nfn f() { defer g(); }\n"),
        LowerError::Defer
    ));
}

#[test]
fn gate_reject_match() {
    assert!(matches!(
        lower_error(
            "fn f(let x: i32) -> i32 { match x { 1 => { return 10; } _ => { return 20; } } }\n"
        ),
        LowerError::Match
    ));
}

#[test]
fn gate_reject_loop() {
    assert!(matches!(
        lower_error("fn f() { while true { } }\n"),
        LowerError::Loop
    ));
}

#[test]
fn gate_reject_const_ref() {
    assert!(matches!(
        lower_error("const N: i32 = 5;\nfn f() -> i32 { return N; }\n"),
        LowerError::Comptime(_)
    ));
}

#[test]
fn gate_reject_closure_body_reports_checks_first() {
    // The checker rejects closures (I9 owns captures) before lowering ever
    // sees the body: the diagnostic is still clean, still no panic.
    let built = build_raw("fn f() { let g = |x| x; }\n");
    assert!(
        !built.check_diags.is_empty(),
        "the checker must speak first"
    );
    assert_eq!(
        built.lower_diags.len(),
        1,
        "lower diags: {:?}",
        built.lower_diags
    );
    assert!(
        matches!(built.lower_diags[0].error, LowerError::CheckErrors),
        "got {:?}",
        built.lower_diags[0].error
    );
}
