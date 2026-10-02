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
fn gate_reject_parallel_for() {
    // `for`/`while` lower from F1-completion on; the M3 concurrency
    // statements (design §1.2) still do not.
    assert!(matches!(
        lower_error("fn f(let xs: Slice[i64]) { parallel for x in xs { } }\n"),
        LowerError::Loop
    ));
}

#[test]
fn gate_reject_enum_match_names_the_missing_fact() {
    // The GRAMMAR decides a `PatLit`/`PatWild` arm on a scalar; everything
    // else needs I7's decisions, which `BodyFacts` does not carry (see
    // `FnLower::lower_match_stmt`). A clean `LowerError::Match`, never a
    // guess at what a one-segment pattern path meant.
    assert!(matches!(
        lower_error(
            "enum E { a, b }\nfn f(let e: E) -> i64 { match e { E.a => { return 1; } E.b => { return 2; } } }\n"
        ),
        LowerError::Match
    ));
}

// -- `match` on a scalar: `switch_discr` ------------------------------------

#[test]
fn gate_match_scalar_literal_arm_wins() {
    run_ok(
        "fn pick(let x: i32) -> i32 { var r: i32 = 0; match x { 1 => { r = 10; } 2 => { r = 20; } _ => { r = 30; } } return r; }\nfn main(inout out: Out) { if pick(2) == 20 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_scalar_falls_to_the_wildcard() {
    run_ok(
        "fn pick(let x: i32) -> i32 { var r: i32 = 0; match x { 1 => { r = 10; } _ => { r = 30; } } return r; }\nfn main(inout out: Out) { if pick(7) == 30 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_arms_fall_through_to_one_join() {
    // Every arm that falls off its block branches to the SAME join, so the
    // statement after the `match` runs exactly once whichever arm ran.
    run_ok(
        "fn pick(let x: i32) -> i32 { var r: i32 = 0; match x { 1 => { r = 1; } _ => { r = 2; } } r = r + 10; return r; }\nfn main(inout out: Out) { if pick(1) == 11 and pick(9) == 12 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_negative_literal_pattern() {
    // The pattern literal is narrowed to the scrutinee's width, so it
    // compares equal to the zero-extended slot the interpreter reads.
    run_ok(
        "fn pick(let x: i32) -> i32 { var r: i32 = 0; match x { -1 => { r = 5; } _ => { r = 6; } } return r; }\nfn main(inout out: Out) { if pick(-1) == 5 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_on_bool_without_a_wildcard() {
    // Exhaustive by ch09 R56, so the default edge is `unreachable` and is
    // never taken.
    run_ok(
        "fn pick(let b: bool) -> i32 { var r: i32 = 0; match b { true => { r = 1; } false => { r = 2; } } return r; }\nfn main(inout out: Out) { if pick(false) == 2 { out.write_line(\"ok\"); } }\n",
    );
}

// -- loops ------------------------------------------------------------------

#[test]
fn gate_while_counts_up() {
    run_ok(
        "fn f(let n: i64) -> i64 { var i: i64 = 0; while i < n { i = i + 1; } return i; }\nfn main(inout out: Out) { if f(4) == 4 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_while_never_entered() {
    run_ok(
        "fn f(let n: i64) -> i64 { var i: i64 = 0; while i < n { i = i + 1; } return i; }\nfn main(inout out: Out) { if f(-3) == 0 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_for_over_a_range_accumulates() {
    run_ok(
        "fn f(let n: i64) -> i64 { var acc: i64 = 0; for i in 0 ..< n { acc = acc + i; } return acc; }\nfn main(inout out: Out) { if f(5) == 10 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_for_over_an_array_accumulates() {
    run_ok(
        "fn main(inout out: Out) { var data: Array[i64, 3] = [2, 3, 4]; var acc: i64 = 0; for x in data { acc = acc + x; } if acc == 9 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_for_over_a_slice_accumulates() {
    run_ok(
        "fn sum(let xs: Slice[i64]) -> i64 { var acc: i64 = 0; for x in xs { acc = acc + x; } return acc; }\nfn main(inout out: Out) { var data: Array[i64, 4] = [1, 2, 3, 4]; let xs: Slice[i64] = data[1 ..< 4]; if sum(xs) == 9 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_for_over_an_empty_slice_runs_zero_times() {
    run_ok(
        "fn sum(let xs: Slice[i64]) -> i64 { var acc: i64 = 1; for x in xs { acc = acc + x; } return acc; }\nfn main(inout out: Out) { var data: Array[i64, 3] = [1, 2, 3]; let xs: Slice[i64] = data[2 ..< 2]; if sum(xs) == 1 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_break_leaves_the_loop() {
    run_ok(
        "fn f() -> i64 { var i: i64 = 0; while i < 100 { if i == 3 { break; } i = i + 1; } return i; }\nfn main(inout out: Out) { if f() == 3 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_continue_runs_the_for_latch_exactly_once() {
    // `continue` lands on the LATCH, so the induction variable still
    // advances and the loop terminates (a `continue` that jumped to the
    // header would spin forever).
    run_ok(
        "fn f() -> i64 { var acc: i64 = 0; for i in 0i64 ..< 5i64 { if i == 2i64 { continue; } acc = acc + i; } return acc; }\nfn main(inout out: Out) { if f() == 8 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_nested_loops_break_the_inner_one_only() {
    run_ok(
        "fn f() -> i64 { var acc: i64 = 0; for i in 0i64 ..< 3i64 { for j in 0i64 ..< 10i64 { if j == 2i64 { break; } acc = acc + 1i64; } } return acc; }\nfn main(inout out: Out) { if f() == 6 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_break_outside_a_loop_is_the_checkers_diagnostic() {
    // ch01 R8's own rejection is the checker's flow pass (I8), which speaks
    // first; lowering's `loops` stack keeps the case a clean
    // `LowerError::Unresolved` rather than a panic if it ever gets there.
    let built = build_raw("fn f() { break; }\n");
    assert!(
        !built.check_diags.is_empty(),
        "the checker must speak first: {:?}",
        built.lower_diags
    );
}

// -- scalar indexing and `len` ----------------------------------------------

#[test]
fn gate_index_an_array() {
    run_ok(
        "fn main(inout out: Out) { var data: Array[i64, 3] = [7, 8, 9]; if data[1] == 8 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_index_a_slice_is_relative_to_its_window() {
    run_ok(
        "fn main(inout out: Out) { var data: Array[i64, 4] = [1, 2, 3, 4]; let xs: Slice[i64] = data[2 ..< 4]; if xs[0] == 3 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_index_write_an_array_element() {
    run_ok(
        "fn main(inout out: Out) { var data: Array[i64, 3] = [1, 2, 3]; data[2] = 30; if data[2] == 30 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_index_write_through_a_slice_reaches_the_base() {
    run_ok(
        "fn main(inout out: Out) { var data: Array[i64, 3] = [1, 2, 3]; var xs: Slice[i64] = data[1 ..< 3]; xs[0] = 20; if data[1] == 20 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_index_past_the_end_traps_bounds() {
    run_trap(
        "fn main() { var data: Array[i64, 3] = [1, 2, 3]; var i: usize = 3; var z: i64 = data[i]; }\n",
        fors_fmir::op::TrapKind::Bounds,
    );
}

#[test]
fn gate_index_write_past_the_end_traps_bounds() {
    run_trap(
        "fn main() { var data: Array[i64, 3] = [1, 2, 3]; var i: usize = 7; data[i] = 1; }\n",
        fors_fmir::op::TrapKind::Bounds,
    );
}

#[test]
fn gate_len_of_an_array_and_of_a_slice() {
    run_ok(
        "fn main(inout out: Out) { var data: Array[i64, 4] = [1, 2, 3, 4]; let xs: Slice[i64] = data[1 ..< 3]; if data.len == 4 and xs.len == 2 { out.write_line(\"ok\"); } }\n",
    );
}

// -- ch03 Rules 4 and 6: explicit arithmetic and the lossy conversions -----

#[test]
fn gate_wrap_add_wraps_instead_of_trapping() {
    run_ok(
        "fn main(inout out: Out) { var x: i32 = 2147483647; var y: i32 = 1; var z: i32 = x.wrap_add(y); if z == -2147483648 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_sat_mul_saturates() {
    run_ok(
        "fn main(inout out: Out) { var x: i32 = 2000000000; var z: i32 = x.sat_mul(2); if z == 2147483647 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_wrap_neg_of_min_is_min() {
    run_ok(
        "fn main(inout out: Out) { var x: i32 = -2147483648; var z: i32 = x.wrap_neg(); if z == -2147483648 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_wrap_shl_still_traps_at_the_width() {
    // `fors-interp::arith::int_binop`'s standing decision: "`div-zero` and
    // `shift` trap in every mode (only representability is
    // mode-dependent)". ch03 Rule 4's modes are about representability, and
    // design §11.1 Q4 fixes the shift condition as exactly `count >=
    // width`, which `wrap_`/`sat_` do not make representable. Pinned here
    // so the lowering side cannot drift from the executor's answer.
    run_trap(
        "fn main() { var x: u8 = 1; var n: u8 = 8; var z: u8 = x.wrap_shl(n); }\n",
        fors_fmir::op::TrapKind::Shift,
    );
}

#[test]
fn gate_wrap_div_still_traps_on_a_zero_divisor() {
    run_trap(
        "fn main() { var x: i32 = 10; var y: i32 = 0; var z: i32 = x.wrap_div(y); }\n",
        fors_fmir::op::TrapKind::DivZero,
    );
}

#[test]
fn gate_trunc_as_rounds_toward_zero() {
    run_ok(
        "fn main(inout out: Out) { var f: f64 = -3.9; var i: i32 = f.trunc_as[i32](); if i == -3 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_user_method_named_like_a_ch03_method_keeps_its_body() {
    // The ch03 family is reached only through a SILENT lookup on a
    // primitive receiver; a user method the checker resolved runs its own
    // body, whatever it is spelled (`is_ch03_prim_site` condition 2).
    run_ok(
        "struct B { n: i32 }\nimpl B { fn wrap_add(let self: B, let k: i32) -> i32 { return 100; } }\nfn main(inout out: Out) { var b: B = B { n: 1 }; if b.wrap_add(2) == 100 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_non_final_wildcard_arm_is_the_checkers_diagnostic() {
    // ch09's unreachable-arm rule (T0054) catches this first; lowering's
    // own guard keeps the `switch_discr` arm table from being built with a
    // default that the surface reading says shadows a later arm.
    let built = build_raw(
        "fn f(let x: i32) -> i32 { match x { _ => { return 1; } 2 => { return 2; } } }\n",
    );
    assert_eq!(built.check_diags, vec!["T0054".to_string()]);
}

#[test]
fn gate_reject_unknown_prefixed_method() {
    // `wrap_foo` is not in ch03's family, so it is an ordinary R43 miss on
    // a primitive — the checker's diagnostic, not a lowering stand-in.
    let built = build_raw("fn main() { var x: i32 = 1; var y: i32 = x.wrap_foo(1); }\n");
    assert!(
        !built.check_diags.is_empty(),
        "the checker must speak first: {:?}",
        built.lower_diags
    );
}

// -- `@fastmath` ------------------------------------------------------------

#[test]
fn gate_fastmath_block_lowers_and_computes_strict() {
    // design E7: the mask is CARRIED, and the interpreter always computes
    // the strict result, so the value inside the block is the unfused one
    // too.
    run_ok(
        "fn main(inout out: Out) { var a: f64 = 1.6394267984578836; var b: f64 = 1.025010755222667; var c: f64 = -1.6804301008195948; var r: f64 = 0.0; @fastmath(contract) { r = a * b + c; } if r == -2.220446049250313e-16 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_reject_unknown_attribute_block() {
    assert!(matches!(
        lower_error("fn f() { @inline { } }\n"),
        LowerError::Unsupported(_)
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

// -- F1-completion verification repairs ---------------------------------------
//
// Each test below pins a defect the adversarial verification of
// F1-completion found and repaired; the comment names the observable the
// producer's own tests missed.

#[test]
fn gate_index_read_and_write_through_a_field_projection() {
    // `self.data[i]` in both positions. The checker types the `Bracket`
    // but leaves the path `self.data` `NO_TY`; before the repair the write
    // PANICKED in `seq_elem_ty` (`TyStore::unqual` indexed with `NO_TY`)
    // and the read reported "no element type".
    run_ok(
        "struct Buf { data: Array[i64, 3], len: usize }\nimpl Buf { fn set(inout self: Buf, let i: usize, let v: i64) { self.data[i] = v; } fn get(let self: Buf, let i: usize) -> i64 { return self.data[i]; } }\nfn main(inout out: Out) { var b: Buf = Buf { data: [1, 2, 3], len: 2 }; b.set(1, 20); if b.get(1) == 20 and b.get(2) == 3 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_index_write_through_a_field_projection_traps_bounds() {
    run_trap(
        "struct Buf { data: Array[i64, 3] }\nimpl Buf { fn set(inout self: Buf, let i: usize, let v: i64) { self.data[i] = v; } }\nfn main() { var b: Buf = Buf { data: [1, 2, 3] }; var k: usize = 3; b.set(k, 1); }\n",
        fors_fmir::op::TrapKind::Bounds,
    );
}

#[test]
fn gate_explicit_arithmetic_in_assignment_keeps_the_local_an_integer() {
    // ch03's own example shape (`total = total.wrap_add(..)` in a loop):
    // the call node is `TY_ERROR` in `facts`, and the assignment used to
    // RETYPE `total` to it, so the second call saw a "non-integer
    // receiver".
    run_ok(
        "fn main(inout out: Out) { var total: u32 = 4294967295; var i: i64 = 0; while i < 3 { total = total.wrap_add(1); i = i + 1; } total = total.wrap_add(5); if total == 7 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_cast_of_an_explicit_arithmetic_result() {
    run_ok(
        "fn main(inout out: Out) { var x: i32 = 7; var y: i64 = x.wrap_mul(3) as i64; if y == 21 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_wrap_as_widening_a_negative_keeps_its_value() {
    // `wrap_as` is the value modulo `2^w`: `(-1i8).wrap_as[i32]()` is `-1`
    // and `(-5i32).wrap_as[u64]()` is `2^64 - 5`, not the zero-extended
    // source bits.
    run_ok(
        "fn main(inout out: Out) { var a: i8 = -1; var b: i32 = a.wrap_as[i32](); var c: i32 = a.trunc_as[i32](); var e: i32 = -5; var g: u64 = e.wrap_as[u64](); if b == -1 and c == -1 and g == 18446744073709551611 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_sat_shl_clamps_to_the_bounds() {
    // design §5.5: `sat_*` clamps the TRUE result; `7i32.sat_shl(31)` is
    // `i32::MAX`, `128u8.sat_shl(1)` is `255` (it was the wrapped `MIN` /
    // `0`).
    run_ok(
        "fn main(inout out: Out) { var j: i32 = 7; var k: i32 = j.sat_shl(31); var n: u8 = 128; var o: u8 = n.sat_shl(1); var q: u8 = n.wrap_shl(1); if k == 2147483647 and o == 255 and q == 0 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_unchecked_outside_an_unsafe_declaration_is_refused() {
    // ch03 Rule 4 / ch04 Rule 10: `unchecked_<op>` MUST NOT appear outside
    // `@unsafe(invariant: ..)`. The checker's rejection is I10's; lowering
    // refuses to build the form rather than letting it run.
    assert!(matches!(
        lower_error("fn f(let x: i32) -> i32 { return x.unchecked_add(1); }\n"),
        LowerError::Unsupported(_)
    ));
}

#[test]
fn gate_unchecked_inside_an_unsafe_declaration_runs() {
    run_ok(
        "@unsafe(invariant: \"the caller keeps x below MAX\")\nfn bump(let x: i32) -> i32 { return x.unchecked_add(1); }\nfn main(inout out: Out) { var x: i32 = 41; if bump(x) == 42 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_inexact_f64_to_f32_as_traps() {
    // ch03 Rule 6: `as` traps unless exactly representable; `0.1f64 as
    // f32` loses bits.
    run_trap(
        "fn main() { var z: f64 = 0.1; var zz: f32 = z as f32; }\n",
        fors_fmir::op::TrapKind::CheckedConversion,
    );
}

#[test]
fn gate_exact_f64_to_f32_as_is_accepted() {
    run_ok(
        "fn main(inout out: Out) { var x: f64 = 0.5; var y: f32 = x as f32; if y == 0.5f32 { out.write_line(\"ok\"); } }\n",
    );
}
