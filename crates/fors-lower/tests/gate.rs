//! F1 gate tests: `BodyFacts`-driven lowering + interpreter core.
//!
//! Each test mirrors one row of the F1 gate list (design §9, "F1"): the
//! source checks clean with I3.5+I4a facts only, lowers without diagnostics,
//! verifies clean under `fors-fmir::verify`, and runs to the pinned
//! observable — `return` with exact stdout bytes, or a trap of the pinned
//! kind. The rejection tests pin the current scope edge: the M3 concurrency
//! statements, closures and const refs each produce a clean
//! [`LowerError`](fors_lower::LowerError), never a panic (`defer` lowers as
//! of F4, and `?`/`else |e|`/`raise` as of F3).
//!
//! F-mono adds the monomorphisation and pattern rows at the end of the file:
//! generic functions, generic structs and trait methods through a bound are
//! INSTANTIATED rather than refused (so F1's `gate_reject_generic_fn`/
//! `gate_reject_generic_call` became the positive tests
//! `gate_generic_fn_has_no_fmir_of_its_own`/
//! `gate_generic_call_lowers_to_an_instance`), enum/struct/tuple/literal
//! patterns lower (so F1-completion's `gate_reject_enum_match_names_the_
//! missing_fact` is deleted — the fact exists as of checker increment I10a),
//! and `Buffer.empty`'s storage comes from a real uninitialised-aggregate
//! primitive whose premature read is `ub: uninit-read`.

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
    /// Every lowered function's name, in lowering order. A monomorphised
    /// instance is named `<callee>$<argument TyIds>` (`fors_lower::mono`).
    instance_names: Vec<String>,
    /// The lowered FMIR, so a test can assert on the lowering itself and not
    /// only on the run.
    decls: Vec<(String, fors_fmir::decl::DeclFmir)>,
}

impl Built {
    /// Every `const_int` value the function named `name` holds, which is how
    /// the discriminant test reads the comparison constants back out.
    fn const_ints_of(&self, name: &str) -> Vec<u64> {
        self.decls
            .iter()
            .filter(|(n, _)| n == name)
            .flat_map(|(_, d)| d.insts.all_rows())
            .filter(|(_, row)| row.op == fors_fmir::op::Op::ConstInt)
            .map(|(_, row)| ((row.b as u64) << 32) | row.a as u64)
            .collect()
    }
}

/// The checker's frozen `TyStore` digest before and after lowering, plus
/// whether the lowering-owned store is at least as large: the owner decision
/// F-mono rests on, asserted rather than assumed.
fn fir_digest_around_lowering(src: &str) -> (u128, u128, bool) {
    let mut interner = Interner::new();
    let source = format!("module m;\nneeds {{ }};\n{OUT_PRELUDE}{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(parsed.diags.is_empty(), "fixture must parse");
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let before = out.fir.tys.digest();
    let n_before = out.fir.tys.len();
    let lowered = lower_build(&inputs, &out, &mut interner);
    let after = out.fir.tys.digest();
    (before, after, lowered.tys.len() >= n_before)
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
    let instance_names: Vec<String> = lowered.fns.iter().map(|f| f.name.clone()).collect();
    let decls: Vec<(String, fors_fmir::decl::DeclFmir)> = lowered
        .fns
        .iter()
        .map(|f| (f.name.clone(), f.decl.clone()))
        .collect();
    if !check_diags.is_empty() || !lowered.diags.is_empty() {
        return Built {
            outcome: None,
            lower_diags: lowered.diags,
            check_diags,
            instance_names,
            decls,
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
    // F-mono: the program runs against the LOWERING-OWNED store, because an
    // instantiated body's types were interned there (see `fors_lower::mono`).
    let tys = lowered.tys;
    let names = lowered.names;
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
    let prog = Program::entry_by_name(fns, "main", Config::v0_1())
        .expect("a main")
        .with_names(names);
    let outcome = run(&prog, &tys).expect("well-formed program runs");
    Built {
        outcome: Some(outcome),
        lower_diags: Vec::new(),
        check_diags: Vec::new(),
        instance_names,
        decls,
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
fn gate_generic_fn_has_no_fmir_of_its_own() {
    // F-mono replaces F1's `gate_reject_generic_fn`. A generic declaration
    // still produces NO FMIR — its types are rigid — but that is a fact, not
    // a diagnostic: ch03 R16-R18 give it one body per instantiation, and this
    // program instantiates it nowhere, so nothing named `id` is lowered and
    // nothing is reported.
    let built = build_raw("fn id[T: Copyable](let a: T) -> T { return a; }\nfn main() { }\n");
    assert!(
        built.lower_diags.is_empty(),
        "lower diags: {:?}",
        built.lower_diags
    );
    assert!(
        !built.instance_names.iter().any(|n| n.starts_with("id")),
        "no instance without a call: {:?}",
        built.instance_names
    );
}

#[test]
fn gate_generic_call_lowers_to_an_instance() {
    // F-mono: the caller lowers, and the generic callee is reached through
    // its INSTANCE. (This replaces F1's `gate_reject_generic_call`, whose
    // scope edge monomorphisation removed.)
    let built = build_raw(
        "fn g[T: Copyable](let a: T) -> T { return a; }\nfn f() -> i32 { var y: i32 = g(1); return y; }\nfn main() { }\n",
    );
    assert!(
        built.check_diags.is_empty(),
        "check diags: {:?}",
        built.check_diags
    );
    assert!(
        !built.lower_diags.iter().any(|d| d.name == "f"),
        "f must lower now: {:?}",
        built.lower_diags
    );
}

/// F4 replaces F1's `gate_reject_defer`: `defer` is lowered now, from I8b's
/// published D7 rows. The scope edge it used to pin is gone, so this is the
/// same program asserted POSITIVELY — a `DeferRow` in the pool, one FMIR
/// scope per `defer` statement, and the function exit carrying it.
#[test]
fn gate_defer_lowers_to_a_pool_row_a_scope_and_an_exit_edge() {
    let built = build("fn g() { }\nfn f() { defer g(); }\nfn main() { }\n");
    assert!(
        !built.lower_diags.iter().any(|d| d.name == "f"),
        "`defer` lowers as of F4: {:?}",
        built.lower_diags
    );
    let decl = &built
        .decls
        .iter()
        .find(|(n, _)| n == "f")
        .expect("f is lowered")
        .1;
    assert_eq!(decl.defers.len(), 1, "one `DeferRow` for one `defer`");
    assert_eq!(
        decl.defers.get(0..1)[0].kind,
        fors_fmir::scope::DeferKind::Defer
    );
    assert_eq!(
        decl.scopes.len(),
        2,
        "the body's root scope plus one per `defer` statement (ch01 R23a's textual cut, \
         made structural)"
    );
    let edges: Vec<_> = decl.exits.all_rows().collect();
    assert_eq!(edges.len(), 1, "one exit edge: the function exit");
    let (_, row) = &edges[0];
    assert!(row.is_function_exit());
    assert_eq!(
        decl.exits.pending(row.pending.clone()),
        &[fors_fmir::ids::DeferId(0)],
        "the `ret` carries the body, in R23a's order"
    );
}

/// The two F4 gate rows that WERE held out on F3, at FMIR level: the
/// handler is a `try_br` on the call whose edges leave no scope (so the
/// callee's `errdefer`, reached only by normal exits, is on no edge at all),
/// and `raise` out of `main` is an ERROR exit edge carrying the `defer` body.
#[test]
fn f3_former_f4_hold_outs_lower_to_try_br_and_an_error_edge() {
    use fors_fmir::exit::ExitKind;
    use fors_fmir::op::Op;
    // `01-ownership/errdefer-skipped-on-return-run-ok`'s shape.
    let built = build_raw(
        "enum E { boom }\nfn g() { }\nfn w(inout o: Out) raises E { errdefer g(); return; }\n         fn main(inout out: Out) { w(&out) else |e| { return; }; }\n",
    );
    assert!(built.check_diags.is_empty(), "{:?}", built.check_diags);
    assert!(built.lower_diags.is_empty(), "{:?}", built.lower_diags);
    let main = &built.decls.iter().find(|(n, _)| n == "main").unwrap().1;
    assert!(
        main.blocks.all_rows().any(|(_, b)| b.term.op == Op::TryBr),
        "the handler is a `try_br` on the call"
    );
    let w = &built.decls.iter().find(|(n, _)| n == "w").unwrap().1;
    assert!(
        w.exits.all_rows().all(|(_, e)| e.kind == ExitKind::Normal),
        "`w` has no error exit"
    );
    assert_eq!(built.outcome.as_ref().unwrap().exit, Exit::Return);
    // `02-failure/main-raises-after-defer-run-error`'s shape.
    let built =
        build_raw("enum E { boom }\nfn main() raises E { defer g(); raise E.boom; }\nfn g() { }\n");
    assert!(built.check_diags.is_empty(), "{:?}", built.check_diags);
    assert!(built.lower_diags.is_empty(), "{:?}", built.lower_diags);
    let main = &built.decls.iter().find(|(n, _)| n == "main").unwrap().1;
    let raise_edges: Vec<_> = main
        .exits
        .all_rows()
        .filter(|(_, e)| main.blocks.row(e.from).term.op == Op::Raise)
        .collect();
    assert_eq!(raise_edges.len(), 1, "one `raise` edge");
    let (_, edge) = &raise_edges[0];
    assert_eq!(edge.kind, ExitKind::Error);
    assert_eq!(
        main.exits.pending(edge.pending.clone()),
        &[fors_fmir::ids::DeferId(0)],
        "the `defer` body runs on the error exit"
    );
    let out = built.outcome.unwrap();
    assert_eq!(out.exit, Exit::Raise);
    assert_eq!(out.stderr, b"error: m.E.boom\n");
}

/// ch02 R3: a `?` across two error types applies exactly ONE `ErrorFrom`
/// conversion, on the `err` edge, and nothing chains a second. Asserted on
/// the FMIR (the `err` block holds one call, then the `raise`) and on the
/// run (the converted error is what `main` renders).
#[test]
fn f3_question_mark_applies_exactly_one_error_from_conversion() {
    use fors_fmir::op::Op;
    let built = build_raw(
        "enum NetError { timeout }\nenum AppError { net(i64) }\n\
         impl ErrorFrom[NetError] for AppError {\n    fn from(let e: NetError) -> AppError { return AppError.net(7); }\n}\n\
         fn get(let n: i64) -> i64 raises NetError {\n    if n == 0 { raise NetError.timeout; }\n    return n;\n}\n\
         fn main() raises AppError { get(0)?; }\n",
    );
    assert!(built.check_diags.is_empty(), "{:?}", built.check_diags);
    assert!(built.lower_diags.is_empty(), "{:?}", built.lower_diags);
    let main = &built.decls.iter().find(|(n, _)| n == "main").unwrap().1;
    let (_, try_block) = main
        .blocks
        .all_rows()
        .find(|(_, b)| b.term.op == Op::TryBr)
        .expect("a try_br");
    let err = main.blocks.row(fors_fmir::ids::BlockId(try_block.term.c));
    assert_eq!(err.term.op, Op::Raise, "the `err` edge raises");
    let calls = (err.first_inst..err.first_inst + err.inst_len)
        .filter(|&i| main.insts.row(fors_fmir::ids::InstId(i)).op == Op::CallDirect)
        .count();
    assert_eq!(
        calls, 1,
        "exactly one `ErrorFrom.from` call on the edge (ch02 R3)"
    );
    let out = built.outcome.unwrap();
    assert_eq!(out.exit, Exit::Raise);
    assert_eq!(out.stderr, b"error: m.AppError.net(7)\n");
}

/// ch02 R16: a `raise` inside a handler makes an ERROR exit, so the
/// enclosing function's `errdefer` runs; a handler yielding a value makes a
/// normal one, so it does not.
#[test]
fn f3_a_handler_that_raises_is_an_error_exit() {
    // `write_line` is F1's stdout stand-in whatever its owner, so the
    // `errdefer` body's line reaching stdout is the observation.
    let out = run_main(
        "enum E { boom }\nfn step() raises E { raise E.boom; }\n\
         fn work(inout o: Out) raises E { errdefer o.write_line(\"undone\"); step() else |e| { raise e; }; }\n\
         fn keep(inout o: Out) raises E { errdefer o.write_line(\"wrong\"); step() else |e| { }; }\n\
         fn main(inout out: Out) { work(&out) else |e| { }; keep(&out) else |e| { }; out.write_line(\"ok\"); }\n",
    );
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"undone\nok\n");
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

// F1-completion's `gate_reject_enum_match_names_the_missing_fact` is DELETED:
// the fact it named (`BodyFacts::patterns`) exists as of checker increment
// I10a, and an enum `match` now lowers. `gate_match_enum_unit_variants` below
// is the same program, run.

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
    // F3: a call is a ch03 numeric primitive iff the checker published a
    // D11 `NumericCallRow` for it; a user method that merely shares the
    // spelling has none and lowers as an ORDINARY call to its own body.
    let src = "struct B { n: i32 }\nimpl B { fn wrap_add(let self: B, let k: i32) -> i32 { return 100; } }\nfn main(inout out: Out) { var b: B = B { n: 1 }; if b.wrap_add(2) == 100 { out.write_line(\"ok\"); } }\n";
    run_ok(src);
    let built = build_raw(src);
    let main = &built.decls.iter().find(|(n, _)| n == "main").unwrap().1;
    assert!(
        !main
            .insts
            .all_rows()
            .any(|(_, r)| r.op == fors_fmir::op::Op::Add(fors_fmir::op::ArithMode::Wrap)),
        "no wrapping add was emitted for the user's `wrap_add`"
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
    // `@unsafe(invariant: ..)`. The checker rejects it (I10's D0004), and
    // lowering still refuses to build the form on its own, so a build that
    // skipped the checker could not let it run either.
    let built = build("fn f(let x: i32) -> i32 { return x.unchecked_add(1); }\n");
    assert_eq!(
        built.check_diags,
        ["D0004"],
        "check diags: {:?}",
        built.check_diags
    );
    assert!(
        built
            .lower_diags
            .iter()
            .any(|d| matches!(d.error, LowerError::Unsupported(_))),
        "lower diags: {:?}",
        built.lower_diags
    );
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

// -- F-mono: monomorphisation ------------------------------------------------

#[test]
fn gate_generic_fn_instantiated_at_two_types_in_one_body() {
    // ch03 R16-R18: one generic declaration, two instances, both reached from
    // the SAME body. Each instance's body is lowered once, at its own
    // arguments, and the two do not share a declaration key.
    run_ok(
        "fn id[T: Copyable](let a: T) -> T { return a; }\n\
         fn main(inout out: Out) { var i: i64 = id(7); var b: bool = id(true); if i == 7 and b { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_generic_fn_instantiated_twice_at_the_same_type_is_one_instance() {
    // The instantiation cache: two calls at the same arguments are ONE
    // lowered body, which is what "lower the body once per distinct (callee,
    // args)" means.
    let built = build_raw(
        "fn id[T: Copyable](let a: T) -> T { return a; }\n\
         fn main(inout out: Out) { var i: i64 = id(1); var j: i64 = id(2); if i + j == 3 { out.write_line(\"ok\"); } }\n",
    );
    assert!(
        built.lower_diags.iter().all(|d| d.name != "main"),
        "lower diags: {:?}",
        built.lower_diags
    );
    assert_eq!(
        built
            .instance_names
            .iter()
            .filter(|n| n.starts_with("id$"))
            .count(),
        1,
        "one instance for two calls at the same type: {:?}",
        built.instance_names
    );
}

#[test]
fn gate_generic_struct_method_at_two_instantiations() {
    // The container's parameters come FIRST in the determined-argument row
    // (R38(a)), so a method of `impl[T] Box[T]` is instantiated by the
    // receiver's own argument.
    run_ok(
        "struct Box[T] { v: T }\n\
         impl[T: Copyable] Box[T] { fn get(let self: Self) -> T { return self.v; } }\n\
         fn main(inout out: Out) { var a: Box[i64] = Box { v: 5 }; var b: Box[bool] = Box { v: true }; if a.get() == 5 and b.get() { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_trait_method_through_a_bound() {
    // `x.m()` where the receiver is a rigid `T: Tr`: the trait declaration
    // has no body, so lowering selects the IMPL from the `Self` the call
    // determined and instantiates the impl's item.
    run_ok(
        "trait Tr { fn two(let self: Self) -> i64; }\n\
         struct S { n: i64 }\n\
         impl Tr for S { fn two(let self: Self) -> i64 { return self.n * 2; } }\n\
         fn twice[T: Tr](let x: T) -> i64 { return x.two(); }\n\
         fn main(inout out: Out) { var s: S = S { n: 21 }; if twice(s) == 42 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_two_instances_of_one_callee_are_two_lowered_bodies() {
    let built = build_raw(
        "fn id[T: Copyable](let a: T) -> T { return a; }\n\
         fn main(inout out: Out) { var i: i64 = id(7); var b: bool = id(true); if i == 7 and b { out.write_line(\"ok\"); } }\n",
    );
    assert!(
        built.lower_diags.is_empty(),
        "lower diags: {:?}",
        built.lower_diags
    );
    let n = built
        .instance_names
        .iter()
        .filter(|n| n.starts_with("id$"))
        .count();
    assert_eq!(n, 2, "two distinct instances: {:?}", built.instance_names);
}

// -- F-mono: pattern lowering ------------------------------------------------

#[test]
fn gate_match_enum_unit_variants() {
    run_ok(
        "enum E { a, b }\n\
         fn pick(let e: E) -> i64 { match e { E.a => { return 1; } E.b => { return 2; } } }\n\
         fn main(inout out: Out) { if pick(E.a) == 1 and pick(E.b) == 2 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_enum_payload_binding_and_a_nested_pattern() {
    // One arm binds a payload component; another tests a NESTED literal
    // inside the payload, and R54 makes the first matching arm win.
    run_ok(
        "enum E { one(i64), two(i64, i64) }\n\
         fn score(let e: E) -> i64 { match e { E.two(1, let b) => { return 100 + b; } E.two(let a, let b) => { return a + b; } E.one(let v) => { return v; } } }\n\
         fn main(inout out: Out) { if score(E.one(7)) == 7 and score(E.two(1, 5)) == 105 and score(E.two(2, 5)) == 7 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_tuple_pattern() {
    run_ok(
        "fn pick(let p: (i64, i64)) -> i64 { match p { (0, let b) => { return b; } (let a, let b) => { return a * b; } } }\n\
         fn main(inout out: Out) { if pick((0, 9)) == 9 and pick((3, 4)) == 12 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_literal_arm_with_a_negative() {
    // The decided `ConstValue` is compared, narrowed to the faced type, so a
    // negative literal arm matches the zero-extended slot the interpreter
    // holds. The arm list is not all-literal (there is a `Str` sibling
    // nowhere here, but the enum shape forces the chain path in the test
    // below), so this one pins the scalar chain's own negative handling.
    run_ok(
        "enum W { v(i64) }\n\
         fn pick(let w: W) -> i64 { match w { W.v(-1) => { return 5; } W.v(let n) => { return n; } } }\n\
         fn main(inout out: Out) { if pick(W.v(-1)) == 5 and pick(W.v(3)) == 3 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_match_str_literal_arm_compares_bytes() {
    run_ok(
        "enum M { s(Str) }\n\
         fn pick(let m: M) -> i64 { match m { M.s(\"hi\") => { return 1; } M.s(_) => { return 2; } } }\n\
         fn main(inout out: Out) { if pick(M.s(\"hi\")) == 1 and pick(M.s(\"no\")) == 2 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_struct_destructuring_moves_a_non_copyable_field() {
    // ch01 R22d(ii): the binding's copy-or-move is the CHECKER's published
    // conv. A moving destructuring takes the scrutinee apart, so the
    // scrutinee place is moved out of once the components are bound — and
    // that is asserted on the FMIR, not only on the run: a `move_from` on the
    // scrutinee place is what makes a later read of it `ub: use-after-move`.
    const SRC: &str = "struct Inner { n: i64 }\n\
         struct Outer { a: Inner, b: i64 }\n\
         fn take(let o: Outer) -> i64 { match o { Outer { a: let a, b: let b } => { return a.n + b; } } }\n\
         fn main(inout out: Out) { var o: Outer = Outer { a: Inner { n: 40 }, b: 2 }; if take(o) == 42 { out.write_line(\"ok\"); } }\n";
    run_ok(SRC);
    let built = build_raw(SRC);
    let moves = built
        .decls
        .iter()
        .filter(|(n, _)| n == "take")
        .flat_map(|(_, d)| d.insts.all_rows())
        .filter(|(_, row)| row.op == fors_fmir::op::Op::MoveFrom)
        .count();
    assert_eq!(
        moves, 1,
        "the destructuring takes the scrutinee place apart exactly once"
    );
}

#[test]
fn gate_let_tuple_destructuring() {
    run_ok(
        "fn main(inout out: Out) { let (a, b) = (17, 25); if a + b == 42 { out.write_line(\"ok\"); } }\n",
    );
}

// -- F-mono: the discriminant mapping and the frozen store -------------------

#[test]
fn gate_enum_discriminants_come_from_fors_layout() {
    // The MUTATION guard. The arm table a `match` on an enum builds must hold
    // exactly the discriminants `fors-layout`'s rule (owner Q1) decides. The
    // second assertion is the mutation: an `index + 1` mapping would produce
    // a different table, so breaking `FnLower::discriminant_of` fails here and
    // in `gate_match_enum_unit_variants`, which runs the same program.
    // The arm bodies return 10/20/30 so the discriminant constants (0/1/2)
    // and the body constants cannot be confused for one another.
    let built = build_raw(
        "enum E { a, b, c }\n\
         fn pick(let e: E) -> i64 { match e { E.a => { return 10; } E.b => { return 20; } E.c => { return 30; } } }\n\
         fn main(inout out: Out) { if pick(E.c) == 30 { out.write_line(\"ok\"); } }\n",
    );
    let want: Vec<u64> = (0..3u32)
        .map(|i| {
            let bytes = fors_layout::encode_discriminant(i, 3).expect("in range");
            fors_layout::decode_discriminant(&bytes, 3).expect("round trip") as u64
        })
        .collect();
    assert_eq!(want, vec![0, 1, 2], "the layout rule numbers variants 0..n");
    let mutated: Vec<u64> = want.iter().map(|v| v + 1).collect();
    let seen = built.const_ints_of("pick");
    for w in &want {
        assert!(
            seen.contains(w),
            "the lowered `pick` must compare against the layout discriminant {w}: {seen:?}"
        );
    }
    assert_ne!(want, mutated, "the mutation must differ from the rule");
    assert!(
        !mutated.iter().all(|m| seen.contains(m)),
        "an `index + 1` mapping must NOT be what was lowered: {seen:?}"
    );
}

#[test]
fn gate_lowering_leaves_the_frozen_fir_type_store_byte_identical() {
    // The owner decision F-mono rests on: instantiated types are interned in
    // a store `fors-lower` OWNS, so the checker's frozen store — which backs
    // every `sig_hash` and every query content key — does not move.
    let (before, after, grew) = fir_digest_around_lowering(
        "struct Box[T] { v: T }\n\
         impl[T: Copyable] Box[T] { fn get(let self: Self) -> T { return self.v; } }\n\
         fn main(inout out: Out) { var a: Box[i64] = Box[i64] { v: 5 }; if a.get() == 5 { out.write_line(\"ok\"); } }\n",
    );
    assert_eq!(before, after, "the checker's TyStore must not move");
    assert!(
        grew,
        "the lowering-owned store must be at least as large as the checker's"
    );
}

// -- F-mono: the uninitialised-aggregate primitive ---------------------------

/// A `Buffer`-shaped fixed-capacity container, declared in the fixture so the
/// gate runs WITHOUT `std` in the build: the same two fields `std/mem.fors`'s
/// `Buffer[T, N]` has, the same `empty()` over the uninitialised-aggregate
/// primitive `buffer_uninit_data`, and `push`/`pop`/indexing checked against
/// `len` rather than `N` (ch10 S23).
///
/// Why a fixture copy and not `std`'s own `Buffer`: `Buffer` is a ch08 R17
/// PRELUDE type name, and `fors-resolve` answers `Entity::PreludeType` for it,
/// which `fors-check`'s R45 qualified-call and struct-literal paths both
/// require to be an `Entity::Item` — so `Buffer.empty()` and `Buffer { .. }`
/// are silently `TY_ERROR` even with the real `std` sources in the build (see
/// the hold-out note on `conformance_f2.rs`'s
/// `gate_buffer_index_past_len_trap`). The primitive, the instantiation and
/// the `ub: uninit-read` are all exercised here regardless.
const VAULT: &str = "struct Vault[T, N: usize] { len: usize, data: Array[T, N] }\n\
impl[T: Copyable, N: usize] Vault[T, N] {\n\
  fn empty() -> Vault[T, N] { return Vault { len: 0, data: Vault.buffer_uninit_data() }; }\n\
  fn buffer_uninit_data() -> Array[T, N] { return Vault.buffer_uninit_data(); }\n\
  fn cap(let self: Self) -> usize { return N; }\n\
  fn push(inout self: Self, let v: T) -> bool { if self.len == N { return false; } self.data[self.len] = v; self.len = self.len + 1; return true; }\n\
  fn pop(inout self: Self) -> T { self.len = self.len - 1; return self.data[self.len]; }\n\
  fn at(let self: Self, let i: usize) -> T { return self.data[i]; }\n\
}\n";

#[test]
fn gate_buffer_push_pop_index_at_two_instantiations() {
    // `Vault[i64, 4]` and `Vault[Str, 2]`: every method is instantiated once
    // per argument row, and `N` is read as a VALUE out of the instantiation
    // (`cap`'s `return N;`).
    let src = format!(
        "{VAULT}fn main(inout out: Out) {{          var b: Vault[i64, 4] = Vault.empty();          var ok1: bool = b.push(11);          var x: i64 = b.at(0);          var y: i64 = b.pop();          var s: Vault[Str, 2] = Vault.empty();          var ok2: bool = s.push(\"hi\");          if ok1 and ok2 and x == 11 and y == 11 and b.cap() == 4 and s.cap() == 2 {{ out.write_line(\"ok\"); }} }}\n"
    );
    run_ok(&src);
    let built = build_raw(&src);
    for stem in ["empty$", "push$", "cap$"] {
        assert_eq!(
            built
                .instance_names
                .iter()
                .filter(|n| n.starts_with(stem))
                .count(),
            2,
            "two instances of `{stem}`: {:?}",
            built.instance_names
        );
    }
}

#[test]
fn gate_buffer_empty_cells_are_uninitialised_not_zero() {
    // `agg_uninit` is a REAL primitive: reading a cell before `push` wrote it
    // is `ub: uninit-read` with its site, never a silent zero. This is what
    // makes `empty()`'s `len: 0` the safety story rather than a formality.
    let src = format!(
        "{VAULT}fn main(inout out: Out) {{          var b: Vault[i64, 4] = Vault.empty();          var x: i64 = b.at(0);          if x == 0 {{ out.write_line(\"ok\"); }} }}\n"
    );
    let out = run_main(&src);
    assert_eq!(
        out.exit,
        Exit::Ub(fors_interp::UbClass::UninitRead),
        "stdout was {:?}",
        String::from_utf8_lossy(&out.stdout)
    );
    let report = out.ub.expect("a ub record");
    assert!(
        report.detail.contains("initialised"),
        "the record names the uninitialised read: {:?}",
        report
    );
}

// -- F-mono verification repairs ---------------------------------------------
//
// Each test below pins a defect the adversarial verification of F-mono found
// and repaired; the comment names the observable the producer's own tests
// missed.

#[test]
fn gate_assoc_type_through_a_bound_normalises_at_the_instance() {
    // `fn pull[T: Src](x: T) -> T.Out`: at `T := A` the return type is the
    // projection `A.Out`, which only `impl Src for A { type Out = i64; }`
    // answers. Lowering substituted with NO projection solver, so every
    // instance reported "a projection no normalisation collapsed".
    run_ok(
        "trait Src { type Out: Copyable; fn get(let self: Self) -> Self.Out; }\n\
         struct A { n: i64 }\n\
         struct B { f: bool }\n\
         impl Src for A { type Out = i64; fn get(let self: Self) -> Self.Out { return self.n; } }\n\
         impl Src for B { type Out = bool; fn get(let self: Self) -> Self.Out { return self.f; } }\n\
         fn pull[T: Src](let x: T) -> T.Out { return x.get(); }\n\
         fn main(inout out: Out) { var a: A = A { n: 4 }; var b: B = B { f: true }; var r: i64 = pull(a); var q: bool = pull(b); if r == 4 and q { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_trait_arguments_select_the_impl() {
    // `impl Conv[i64] for S` and `impl Conv[bool] for S` are two impls of
    // one trait for one type. A call through `T: Conv[i64]` names the
    // first; impl selection that matched on the trait alone reported
    // "2 impls match" and refused both instances.
    run_ok(
        "trait Conv[U] { fn conv(let self: Self) -> U; }\n\
         struct S { n: i64 }\n\
         impl Conv[i64] for S { fn conv(let self: Self) -> i64 { return self.n; } }\n\
         impl Conv[bool] for S { fn conv(let self: Self) -> bool { return self.n > 0; } }\n\
         fn to_i[T: Conv[i64]](let x: T) -> i64 { return x.conv(); }\n\
         fn to_b[T: Conv[bool]](let x: T) -> bool { return x.conv(); }\n\
         fn main(inout out: Out) { var s: S = S { n: 5 }; if to_i(s) == 5 and to_b(s) { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_a_user_method_sharing_the_primitives_spelling_keeps_its_body() {
    // The `buffer_uninit_data` interception is scoped to the self-recursive
    // stand-in SHAPE. A user method of that name with a body of its own was
    // swallowed by the `agg_uninit` intrinsic, so its caller read
    // `ub: uninit-read` instead of the `7` the body wrote.
    run_ok(
        "struct Mine { d: Array[i64, 2] }\n\
         impl Mine { fn buffer_uninit_data() -> Array[i64, 2] { return [7, 7]; } fn make() -> Mine { return Mine { d: Mine.buffer_uninit_data() }; } }\n\
         fn main(inout out: Out) { var m: Mine = Mine.make(); if m.d[0] == 7 { out.write_line(\"ok\"); } }\n",
    );
}

#[test]
fn gate_trait_method_on_a_parameter_free_impl_is_not_an_instance() {
    // The impl's item has nothing to instantiate: it lowers once, as a root
    // body, under its own key. Minting a `$`-instance with an empty row
    // lowered it twice and gave two impls' items one name.
    let built = build_raw(
        "trait Tr { fn two(let self: Self) -> i64; }\n\
         struct S { n: i64 }\n\
         struct U { n: i64 }\n\
         impl Tr for S { fn two(let self: Self) -> i64 { return self.n * 2; } }\n\
         impl Tr for U { fn two(let self: Self) -> i64 { return self.n * 3; } }\n\
         fn twice[T: Tr](let x: T) -> i64 { return x.two(); }\n\
         fn main(inout out: Out) { var s: S = S { n: 21 }; var u: U = U { n: 1 }; if twice(s) + twice(u) == 45 { out.write_line(\"ok\"); } }\n",
    );
    assert!(built.lower_diags.is_empty(), "{:?}", built.lower_diags);
    assert_eq!(
        built.instance_names.iter().filter(|n| *n == "two").count(),
        2,
        "both impl items lower once each, as themselves: {:?}",
        built.instance_names
    );
    assert!(
        !built.instance_names.iter().any(|n| n.starts_with("two$")),
        "no `$`-instance for a parameter-free impl item: {:?}",
        built.instance_names
    );
    assert_eq!(built.outcome.expect("ran").stdout, b"ok\n");
}

#[test]
fn gate_two_instances_differ_in_trap_behaviour() {
    // `Arr[i64, 4].third()` reads element 2 and returns; `Arr[i64, 2].third()`
    // is the SAME body at another `N` and traps bounds. One lowered body per
    // instance is what makes the two outcomes differ.
    let out = run_main(
        "struct Arr[T, N: usize] { d: Array[T, N] }\n\
         impl[T: Copyable, N: usize] Arr[T, N] { fn third(let self: Self) -> T { var k: usize = 2; return self.d[k]; } }\n\
         fn main(inout out: Out) { var a: Arr[i64, 4] = Arr { d: [0, 0, 0, 0] }; var b: Arr[i64, 2] = Arr { d: [0, 0] }; if a.third() == 0 { out.write_line(\"four\"); } if b.third() == 0 { out.write_line(\"two\"); } }\n",
    );
    assert_eq!(out.exit, Exit::Trap(fors_fmir::op::TrapKind::Bounds));
    assert_eq!(out.stdout, b"four\n");
}

// ---------------------------------------------------------------- F6's gate
//
// design §9's F6 list, the LOWERING half. The interpreter half landed earlier
// on hand-written FMIR (`crates/fors-interp/tests/ub.rs`); what follows is
// the SOURCE-level twin of each case the surface can express today, plus the
// scope/brand/region assertions on the lowering itself.
//
// HELD OUT, each with the reason:
//
// - `ub_use_after_free` and `ub_allocator_mismatch` — the heap pair needs
//   `Own[T, A]` through `h.create(..)`/`h.deinit(move b)` (ch01 R18), and
//   reading the pointee back needs a `[Deref, Field]` place FMIR does not
//   have before F7/M2 plus D12's layout ([HOLE-6]). For the MISMATCH the
//   hold-out is permanent at source level by design: ch01 R18 makes the
//   typed case a COMPILE error, so the interpreter's row exists for the
//   erased case only and no accepted program can reach it.
// - `ub_uninit_read_through_out` — a `set` parameter read before it is
//   written is rejected by the checker, so no accepted source reaches it;
//   `&out x` lowering (`borrow_out`, which marks the slot uninitialised) is
//   here and is what the fixture test drives.
// - `arena_gen_wraps_safely` ([HOLE-2]) — it needs `u32::MAX` resets of one
//   arena; no source program expresses that, and `ArenaVal::reset` is the
//   unit under test. `f6_arena_reset_then_a_fresh_ref_is_live` is the
//   source-reachable half of the same mechanism.
// - D9's closure case ("a closure capturing a scoped place carries the
//   source set into its FMIR fn") — a closure literal is still
//   `LowerError::Closure`, and D9 publishes no row for any body in the
//   corpus that lowers.

/// `with arena` gives its block a FRESH brand and a `WithArena` region;
/// `with allocator` gives it a brand and NO region, because an allocator's
/// identity IS the brand `@alloc`/`@free` compare (ch01 R15, R18; design
/// §3.7, §3.4a).
#[test]
fn f6_with_blocks_open_a_branded_scope() {
    let built = build(
        "struct N[A: brand] { val: i64 }\n\
         fn main() { with arena a: Arena[N[a]] { let r: Ref[N[a], a] = a.alloc(N { val: 1 }); } }\n",
    );
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
    let decl = &built
        .decls
        .iter()
        .find(|(n, _)| n == "main")
        .expect("main lowers")
        .1;
    let branded: Vec<_> = decl
        .scopes
        .all_rows()
        .filter(|(_, s)| s.brand != fors_fmir::ids::BrandId::NONE)
        .collect();
    assert_eq!(branded.len(), 1, "one `with` block, one fresh brand");
    let (_, scope) = &branded[0];
    assert_ne!(
        scope.region,
        fors_fmir::ids::RegionId::NONE,
        "a `with arena` block is a region (design §3.7)"
    );
    assert_eq!(
        decl.regions.row(scope.region).kind,
        fors_fmir::region::RegionKind::WithArena
    );
    assert_eq!(
        decl.regions.row(scope.region).brand,
        scope.brand,
        "the region and its scope name the same brand"
    );
    // §3.4a: every `arena_alloc`/`arena_deref` result carries the brand as
    // its alias seed — compile-time IR metadata only, which no execution
    // reads (`arena_brand_survives_lowering`).
    let seeds: Vec<_> = decl
        .insts
        .all_rows()
        .filter(|(_, r)| {
            matches!(
                r.op,
                fors_fmir::op::Op::ArenaAlloc | fors_fmir::op::Op::ArenaDeref
            )
        })
        .map(|(id, _)| decl.insts.aliases.get(id.index()))
        .collect();
    assert!(!seeds.is_empty(), "the arena surface lowered");
    for seed in &seeds {
        assert_eq!(*seed, fors_fmir::alias::AliasSeed::Arena(scope.brand));
    }
}

/// ch01 R17's other half, from source: after `reset` a FRESH `Ref` is at the
/// new generation and dereferences cleanly. (`arena_gen_wraps_safely` is the
/// `u32::MAX` end of the same counter and has no source surface — see the
/// hold-out list above.)
#[test]
fn f6_arena_reset_then_a_fresh_ref_is_live() {
    let out = run_main(
        "struct N[A: brand] { val: i64 }\n\
         fn main(inout out: Out) {\n\
           with arena a: Arena[N[a]] {\n\
             let r: Ref[N[a], a] = a.alloc(N { val: 1 });\n\
             a.reset();\n\
             let s: Ref[N[a], a] = a.alloc(N { val: 7 });\n\
             let v: i64 = a[s].val;\n\
             if v == 7 { out.write_line(\"ok\"); } else { out.write_line(\"bad\"); }\n\
           }\n\
         }\n",
    );
    assert_eq!(out.exit, Exit::Return, "{:?}", out.ub);
    assert!(out.ub.is_none(), "a live `Ref` is not UB: {:?}", out.ub);
    assert_eq!(out.stdout, b"ok\n");
}

/// A `Ref` dereferenced after its arena was `reset` is ch01 R17's **program
/// trap**, in every build mode — the source twin of the interpreter half's
/// `arena_generation_trap_on_a_stale_ref`, and the mechanism the corpus row
/// `01-ownership/arena-generation-trap` pins.
#[test]
fn f6_stale_ref_after_reset_traps_arena_generation() {
    let out = run_main(
        "struct N[A: brand] { val: i64 }\n\
         fn main(inout out: Out) {\n\
           with arena a: Arena[N[a]] {\n\
             let r: Ref[N[a], a] = a.alloc(N { val: 1 });\n\
             a.reset();\n\
             let v: i64 = a[r].val;\n\
             out.write_line(\"unreachable\");\n\
           }\n\
         }\n",
    );
    assert_eq!(
        out.exit,
        Exit::Trap(fors_fmir::op::TrapKind::ArenaGeneration)
    );
    assert!(
        out.ub.is_none(),
        "R17 makes this a TRAP, not a `ub:` report"
    );
}

/// ch01 R7, from source: "Two overlapping `let` accesses MUST be ACCEPTED".
/// The shape is the corpus's own `01-ownership/excl-let-let-overlap-
/// accepted` (a `parse-ok` row there), RUN — which is the property E14 ranks
/// above the positive detections: a false `ub: aliasing` exits 70 and would
/// fail the corpus on accepted code.
///
/// The borrow STACK itself (two shared tags in one SharedRO group) is driven
/// by the interpreter half's `ub_aliasing_accepts_two_let_borrows`: a `let`
/// argument is passed by value here, so no `let` borrow reaches the stack
/// from source until `Op::Borrow` lowering arrives with F7/M2's sub-range
/// borrow stacks.
#[test]
fn f6_source_twin_aliasing_accepts_two_let_borrows() {
    let out = run_main(
        "fn combine(let x: i64, let y: i64) -> i64 { return x + y; }\n\
         struct Pair { b: i64 }\n\
         fn main(inout out: Out) {\n\
           let a: Pair = Pair { b: 5 };\n\
           if combine(a.b, a.b) == 10 { out.write_line(\"ok\"); } else { out.write_line(\"bad\"); }\n\
         }\n",
    );
    assert_eq!(out.exit, Exit::Return);
    assert!(
        out.ub.is_none(),
        "accepted code must not report UB: {:?}",
        out.ub
    );
    assert_eq!(out.stdout, b"ok\n");
}

/// The nested shape of the same rule: a second `let` access opens inside the
/// first's extent and the FIRST is read again afterwards.
#[test]
fn f6_source_twin_aliasing_accepts_nested_let_under_let() {
    let out = run_main(
        "fn combine(let x: i64, let y: i64) -> i64 { return x + y; }\n\
         fn main(inout out: Out) {\n\
           var x: i64 = 9;\n\
           let outer: i64 = x;\n\
           {\n\
             let inner: i64 = x;\n\
             var t: i64 = combine(outer, inner);\n\
           }\n\
           if combine(outer, x) == 18 { out.write_line(\"ok\"); } else { out.write_line(\"bad\"); }\n\
         }\n",
    );
    assert_eq!(out.exit, Exit::Return);
    assert!(
        out.ub.is_none(),
        "accepted code must not report UB: {:?}",
        out.ub
    );
    assert_eq!(out.stdout, b"ok\n");
}

/// By-reference arguments (ch07 Rule 4's `&x` / `&out x`), design §3.3:
/// a SCALAR place is passed as a pointer — `&x` is one `borrow_mut`, `&out
/// x` one `borrow_out` (which marks the slot uninitialised so §5.2's
/// "uninitialised read (incl. through `&out`)" can fire) — each carrying
/// §3.4a's "parameter convention" alias seed. An AGGREGATE is a cell shared
/// by handle in FMIR's value model, so `&c` passes the handle by value under
/// the `Inout` convention on the call row, exactly as a method receiver
/// does; no unique tag is pushed for it. A plain `let` argument carries NO
/// tag either (ch01 R7: "no-alias facts therefore never come from a `let`
/// parameter").
#[test]
fn f6_by_reference_arguments_lower_to_borrows_with_a_convention_seed() {
    // Scalar: a pointer.
    let built = build(
        "fn inc(inout n: i32) { n = n + 1; }\nfn fill(set n: i32) { n = 5; }\n\
         fn main(inout out: Out) { var a: i32 = 1; inc(&a); var b: i32 = 0; fill(&out b); }\n",
    );
    assert!(
        built.lower_diags.is_empty(),
        "lower diags: {:?}",
        built.lower_diags
    );
    let decl = &built
        .decls
        .iter()
        .find(|(n, _)| n == "main")
        .expect("main lowers")
        .1;
    let muts: Vec<_> = decl
        .insts
        .all_rows()
        .filter(|(_, r)| r.op == fors_fmir::op::Op::BorrowMut)
        .collect();
    assert_eq!(muts.len(), 1, "`&a` on a scalar is one `borrow_mut`");
    assert_eq!(
        decl.insts.aliases.get(muts[0].0.index()),
        fors_fmir::alias::AliasSeed::Conv(fors_fir::sig::Conv::Inout)
    );
    let outs: Vec<_> = decl
        .insts
        .all_rows()
        .filter(|(_, r)| r.op == fors_fmir::op::Op::BorrowOut)
        .collect();
    assert_eq!(outs.len(), 1, "`&out b` on a scalar is one `borrow_out`");
    assert_eq!(
        decl.insts.aliases.get(outs[0].0.index()),
        fors_fmir::alias::AliasSeed::Conv(fors_fir::sig::Conv::Set)
    );
    // The callee reaches the caller's slot THROUGH the pointer: every place
    // rooted at the parameter carries one `Deref`.
    let inc = &built
        .decls
        .iter()
        .find(|(n, _)| n == "inc")
        .expect("inc lowers")
        .1;
    let derefs = inc
        .places
        .all_rows()
        .filter(|(id, _)| inc.places.segs(*id) == [fors_fmir::place::Seg::Deref])
        .count();
    assert!(
        derefs >= 1,
        "`inc`'s `n` is read and written through `[Deref]`"
    );

    // Aggregate: the shared cell, by value, under the `Inout` convention.
    let built = build("fn g(inout a: Out) { }\nfn main(inout out: Out) { g(&out); }\n");
    assert!(
        built.lower_diags.is_empty(),
        "lower diags: {:?}",
        built.lower_diags
    );
    let decl = &built
        .decls
        .iter()
        .find(|(n, _)| n == "main")
        .expect("main lowers")
        .1;
    assert!(
        !decl.insts.all_rows().any(|(_, r)| matches!(
            r.op,
            fors_fmir::op::Op::BorrowMut | fors_fmir::op::Op::BorrowOut
        )),
        "an aggregate `&out` pushes no unique tag: its cell is shared by handle"
    );
    let call = decl
        .insts
        .calls
        .iter()
        .find(|c| matches!(c.callee, fors_fmir::inst::Callee::Direct(_)))
        .expect("the call to `g`");
    let convs = &decl.insts.arg_convs[call.args.start as usize..call.args.end as usize];
    assert_eq!(
        convs,
        &[fors_fir::sig::Conv::Inout],
        "the call row carries the access"
    );
}

/// The run-time half of the same contract, which is what the verifier found
/// MISSING: a callee's write to a scalar `inout`/`set` parameter must land in
/// the CALLER's slot (before this, `inc(&n)` lowered, ran, and silently left
/// `n` unchanged). Forwarding a by-reference parameter passes the caller's
/// pointer on rather than re-borrowing a `[Deref]` place.
#[test]
fn f6_scalar_inout_and_set_arguments_write_the_callers_slot() {
    let out = run_main(
        "fn inc(inout n: i32) { n = n + 1; }\n\
         fn twice(inout n: i32) { inc(&n); inc(&n); n = n + 4; }\n\
         fn fill(set n: i32) { n = 5; }\n\
         fn main(inout out: Out) {\n\
           var n: i32 = 1;\n\
           inc(&n);\n\
           inc(&n);\n\
           var m: i32 = 1;\n\
           twice(&m);\n\
           var k: i32 = 0;\n\
           fill(&out k);\n\
           var hits: i32 = 0;\n\
           if n == 3 { hits = hits + 1; }\n\
           if m == 7 { hits = hits + 1; }\n\
           if k == 5 { hits = hits + 1; }\n\
           if hits == 3 { out.write_line(\"ok\"); } else { out.write_line(\"bad\"); }\n\
         }\n",
    );
    assert_eq!(out.exit, Exit::Return, "{:?}", out.ub);
    assert!(
        out.ub.is_none(),
        "accepted code must not report UB: {:?}",
        out.ub
    );
    assert_eq!(out.stdout, b"ok\n");
}

/// An aggregate under `&c` is the method-receiver contract: the callee's
/// field write lands in the shared cell.
#[test]
fn f6_aggregate_inout_argument_shares_the_cell() {
    run_ok(
        "struct C { n: i64 }\nfn bump(inout c: C) { c.n = c.n + 1; }\n\
         fn main(inout out: Out) { var c: C = C { n: 41 }; bump(&c); if c.n == 42 { out.write_line(\"ok\"); } else { out.write_line(\"bad\"); } }\n",
    );
}

/// ch01 R23c: "Bodies MAY NEST: a `defer` written inside a body is a
/// statement of that body's block and runs when that block exits." The body
/// is lowered as a region of its own, so the nested body's edge sits inside
/// the sub-CFG before `br BODY_END`.
#[test]
fn f4_a_defer_body_may_nest_a_defer() {
    let out = run_main(
        "fn main(inout out: Out) {\n\
           defer { defer out.write_line(\"inner\"); out.write_line(\"outer\"); }\n\
           out.write_line(\"main\");\n\
         }\n",
    );
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"main\nouter\ninner\n");
}

/// ch01 R23a's textual cut, end to end: a `defer` whose statement does NOT
/// precede the exit is not pending there. `B` is registered after the
/// `break`, so the breaking iteration runs `A` only; the first iteration
/// runs both, in reverse textual order. (The structural guard is the
/// one-scope-per-`defer` assertion in `conformance_f2.rs`; this is the
/// observable it protects.)
#[test]
fn f4_a_defer_after_the_break_is_not_pending_on_it() {
    let out = run_main(
        "fn main(inout out: Out) {\n\
           for i in 0 ..< 3 {\n\
             defer out.write_line(\"A\");\n\
             if i == 1 { break; }\n\
             defer out.write_line(\"B\");\n\
             out.write_line(\"body\");\n\
           }\n\
           out.write_line(\"done\");\n\
         }\n",
    );
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"body\nB\nA\nA\ndone\n");
}

/// `with allocator` (ch01 R15, R18): the block opens a branded scope and NO
/// region, because an allocator's identity IS the scope's brand — which is
/// exactly what `fors-interp`'s `allocator_at` reads off the executing
/// block's scope so `@free` can compare it against `@alloc`'s
/// `AllocKind::Heap(owner)` (design §3.7, §5.2's allocator-mismatch row).
///
/// The `Own[T, A]` surface on top of it (`h.create(n)`, `h.deinit(move b)`,
/// and reading the pointee back) is HELD OUT: it needs a `[Deref, Field]`
/// place FMIR does not have before F7/M2 plus D12's layout ([HOLE-6]), so
/// the body here is the brand itself and nothing more.
#[test]
fn f6_with_allocator_opens_a_branded_scope_and_no_region() {
    let built = build("fn main() { with allocator h: Out { } }\n");
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
    let decl = &built
        .decls
        .iter()
        .find(|(n, _)| n == "main")
        .expect("main lowers")
        .1;
    let branded: Vec<_> = decl
        .scopes
        .all_rows()
        .filter(|(_, s)| s.brand != fors_fmir::ids::BrandId::NONE)
        .collect();
    assert_eq!(branded.len(), 1, "one `with` block, one fresh brand");
    assert_eq!(
        branded[0].1.region,
        fors_fmir::ids::RegionId::NONE,
        "an allocator block is not a region: its identity is the brand"
    );
    assert!(
        decl.regions.is_empty(),
        "no `region_enter` is needed for `with allocator`"
    );
}

/// ch03 R9 (F3): `N as T` from a `comptime_int` constant is the converted
/// CONSTANT, folded at lowering — to an integer and to a float.
#[test]
fn f3_comptime_int_as_folds_to_the_converted_constant() {
    run_ok(
        "const N: comptime_int = 300;\nfn main(inout out: Out) { var x: i32 = N as i32; var f: f64 = N as f64; if x == 300 { if f == 300.0 { out.write_line(\"ok\"); } } }\n",
    );
}

/// ch03 R6/R9 (F3): a `comptime_int` the target cannot represent exactly is
/// a NAMED comptime refusal at lowering, never a silently truncated constant.
#[test]
fn f3_comptime_int_as_out_of_range_is_a_named_refusal() {
    let built = build_raw(
        "const N: comptime_int = 300;\nfn f() -> u8 { var x: u8 = N as u8; return x; }\n",
    );
    assert!(built.check_diags.is_empty(), "{:?}", built.check_diags);
    assert!(
        built.lower_diags.iter().any(
            |d| matches!(&d.error, LowerError::Comptime(w) if w.contains("cannot represent 300"))
        ),
        "lower diags: {:?}",
        built.lower_diags
    );
}

/// F9 (design §6): a statement-form `comptime` block is lowered as its OWN
/// thunk — a function carrying a freshly minted key, whose body is the
/// block — and the enclosing run-time body contains nothing of it (it was
/// evaluated at build time, never deferred to run time).
#[test]
fn f9_comptime_block_lowers_as_its_own_thunk() {
    let mut interner = Interner::new();
    let src = "fn main(inout out: Out) { comptime { var i: i64 = 0; while i < 3 { i = \
               i.wrap_add(1); } } out.write_line(\"ok\"); }\n";
    let source = format!("module m;\nneeds {{ }};\n{OUT_PRELUDE}{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(parsed.diags.is_empty(), "fixture must parse");
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    assert!(out.diagnostics.is_empty(), "check diags");
    let lowered = lower_build(&inputs, &out, &mut interner);
    assert!(lowered.diags.is_empty(), "{:?}", lowered.diags);
    assert_eq!(lowered.comptime.len(), 1);
    let t = &lowered.comptime[0];
    assert_eq!(
        (t.enclosing.as_str(), t.name.as_str()),
        ("main", "main#comptime0")
    );
    assert!(t.error.is_none() && t.inputs.is_empty());
    let main = lowered.fns.iter().find(|f| f.name == "main").expect("main");
    let thunk = lowered
        .fns
        .iter()
        .find(|f| f.name == t.name)
        .expect("thunk");
    assert_ne!(main.decl.decl, thunk.decl.decl, "the thunk has its own key");
    let has_loop_compare = |d: &fors_fmir::decl::DeclFmir| {
        d.insts
            .all_rows()
            .any(|(_, r)| matches!(r.op, fors_fmir::op::Op::Icmp(_)))
    };
    assert!(
        has_loop_compare(&thunk.decl),
        "the block's loop is in the thunk"
    );
    assert!(
        !has_loop_compare(&main.decl),
        "and nowhere in the run-time body"
    );
    for f in &lowered.fns {
        assert!(fors_fmir::verify::verify(&f.decl).is_empty(), "{}", f.name);
    }
}

/// F9 (verifier): a VALUE-position `comptime` block (`let x = comptime {
/// ... };`) is a NAMED thunk row, never a clean build. Before this, the
/// block was evaluated as if it were a statement and the enclosing
/// function's run-time body silently failed to lower — a `fors build`
/// with exit 0 and a function with no body.
#[test]
fn f9_value_position_comptime_block_is_a_named_thunk_row() {
    let mut interner = Interner::new();
    let src = "fn helper() -> i64 { let x: i64 = comptime { 5 }; return x; }\nfn main(inout \
               out: Out) { out.write_line(\"ok\"); }\n";
    let source = format!("module m;\nneeds {{ }};\n{OUT_PRELUDE}{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(parsed.diags.is_empty(), "fixture must parse");
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let lowered = lower_build(&inputs, &out, &mut interner);
    assert_eq!(lowered.comptime.len(), 1);
    let t = &lowered.comptime[0];
    assert_eq!(t.enclosing, "helper");
    match &t.error {
        Some(LowerError::Comptime(w)) => assert!(w.contains("used as a value"), "{w}"),
        other => panic!("a value-position block must be a named row, got {other:?}"),
    }
    assert!(
        !lowered.fns.iter().any(|f| f.name == t.name),
        "no thunk is lowered for a block the build cannot splice"
    );
    assert!(
        lowered
            .diags
            .iter()
            .any(|d| d.name == "helper" && matches!(d.error, LowerError::Comptime(_))),
        "and the run-time body refuses it too: {:?}",
        lowered.diags
    );
}

/// F9 (verifier): a `comptime` block in a `const` initialiser has no body
/// facts, so the thunk loop never sees it; it is a NAMED row, not a block
/// that is neither evaluated nor reported.
#[test]
fn f9_comptime_block_in_a_const_initialiser_is_a_named_thunk_row() {
    let mut interner = Interner::new();
    let src = "const K: i64 = comptime { 5 };\nfn main(inout out: Out) { out.write_line(\"ok\"); \
               }\n";
    let source = format!("module m;\nneeds {{ }};\n{OUT_PRELUDE}{src}");
    let bytes = source.into_bytes();
    let name: Segments = vec![interner.intern(b"m")];
    let parsed = parse_file(&bytes);
    assert!(parsed.diags.is_empty(), "fixture must parse");
    let inputs = [FileInput {
        tree: &parsed.tree,
        tokens: &parsed.tokens,
        source: &bytes,
        name,
    }];
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), Some(b"m"));
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let lowered = lower_build(&inputs, &out, &mut interner);
    let rows: Vec<_> = lowered
        .comptime
        .iter()
        .filter(|t| t.enclosing == "K")
        .collect();
    assert_eq!(rows.len(), 1, "{:?}", lowered.comptime);
    match &rows[0].error {
        Some(LowerError::Comptime(w)) => assert!(w.contains("`const` initialiser"), "{w}"),
        other => panic!("a const-initialiser block must be a named row, got {other:?}"),
    }
}
