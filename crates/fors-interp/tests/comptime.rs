//! F9 (design `fmir-interpreter.md` §6, §9 F9's GATE): comptime mode over
//! hand-written FMIR — the half of the gate that needs no source program.
//! The five ch04 corpus files run end to end through `fors build` in
//! `fors-cli/tests/comptime_f9.rs`.
//!
//! - `address_observation_blocks_tierup` (named in the GATE): a
//!   pointer-to-integer conversion marks the evaluation ineligible for
//!   tier-up (ch04 R15), and the address it observes is the synthetic,
//!   deterministic `(AllocId << 32) | offset`.
//! - every intrinsic whose `comptime` column is `Forbidden` is a build error
//!   naming it and its site, and the host is never touched (ch04 R12);
//! - `input_read` serves exactly the declared bytes and rejects anything
//!   else (ch04 R13), and is forbidden at run time (ch10 R42);
//! - the step, allocation and build-wide budgets are named errors with the
//!   counts (ch04 R14, owner Q6);
//! - the memo key is a function of content only (design §6).

mod fixture;

use fixture::Fx;
use fors_fir::defpath::DeclKeyId;
use fors_fir::ty::{PrimKind, TyStore};
use fors_fmir::ids::{ScopeId, ValId};
use fors_fmir::inst::{CallRow, Callee};
use fors_fmir::op::{CmpPred, NO_OPERAND, Op};
use fors_index::interner::Symbol;
use fors_interp::budget::{BuildMeter, Exceeded, Limits};
use fors_interp::comptime::{
    ComptimeEnv, ComptimeFault, DeclaredInputs, ErrorKind, Memo, encode, evaluate,
    evaluate_memoized, memo_key, target_hash,
};
use fors_interp::intrinsic::{TABLE, When};
use fors_interp::{Config, InterpError, ProgFn, Program};

const SYM: u32 = 40;

fn program(fx: Fx, intrinsic: Option<&str>) -> (Program, TyStore) {
    let (decl, tys, strings) = fx.finish();
    let diags = fors_fmir::verify::verify(&decl);
    assert!(
        diags.is_empty(),
        "fixture does not verify: {:?}",
        diags
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>()
    );
    let prog = Program {
        fns: vec![ProgFn {
            name: "thunk".into(),
            decl,
            strings,
            intrinsics: intrinsic
                .map(|n| vec![(SYM, n.to_string())])
                .unwrap_or_default(),
        }],
        entry: 0,
        config: Config::v0_1(),
        names: Default::default(),
    };
    (prog, tys)
}

fn eval(
    prog: &Program,
    tys: &TyStore,
    inputs: &DeclaredInputs,
    limits: Limits,
) -> Result<fors_interp::Evaluation, fors_interp::ComptimeError> {
    let env = ComptimeEnv {
        inputs,
        limits,
        externs: &[],
    };
    let mut build = BuildMeter::new(&limits);
    evaluate(prog, tys, &env, &mut build, "setup")
}

fn intrinsic_call(fx: &mut Fx, args: &[ValId], ty: fors_fir::ty::TyId, line: u32) -> ValId {
    let args = fx.decl.insts.push_plain_operands(args);
    let call = fx.decl.insts.push_call(CallRow {
        callee: Callee::Intrinsic(Symbol(SYM)),
        args,
    });
    let site = fx.site(line, 9);
    fx.emit_at(Op::Intrinsic, call, NO_OPERAND, NO_OPERAND, ty, site)
}

// -- address_observation_blocks_tierup --------------------------------------

/// `alloc` then, optionally, a `ptr -> u64` conversion of the pointer,
/// returned as the result.
fn alloc_program(cast: bool) -> (Program, TyStore) {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let u64_ty = fx.ty(PrimKind::U64);
    let b = fx.reserve();
    fx.begin(b, ScopeId(0));
    let size = fx.const_int(8, usize_ty);
    let align = fx.const_int(8, usize_ty);
    let p = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    let out = if cast {
        fx.emit(Op::ConvWrap, p.0, NO_OPERAND, NO_OPERAND, u64_ty)
    } else {
        fx.const_int(5, u64_ty)
    };
    fx.end(fx.term(Op::Ret, out.0, NO_OPERAND, NO_OPERAND));
    program(fx, None)
}

/// ch04 R15, design §6: a pointer-to-integer cast observes an address, so
/// the body may not tier up; the value observed is the synthetic
/// `(AllocId << 32) | offset` (allocation 1: row 0 is the placeholder), the
/// same in every evaluation and every process.
#[test]
fn address_observation_blocks_tierup() {
    let (prog, tys) = alloc_program(true);
    let a = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default()).expect("evaluates");
    assert!(a.observed_address, "a ptr-to-int cast is an observation");
    assert!(
        !a.tier_up_eligible(),
        "an observing body must run interpreted"
    );
    let mut want = vec![encode::INT, 64, 0];
    want.extend_from_slice(&(1u64 << 32).to_le_bytes());
    assert_eq!(a.value, want, "the synthetic address of allocation 1");
    let again = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default()).expect("again");
    assert_eq!(a, again, "the observed address is deterministic");

    let (prog, tys) = alloc_program(false);
    let b = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default()).expect("evaluates");
    assert!(
        !b.observed_address && b.tier_up_eligible(),
        "no cast, no bar"
    );
    assert_eq!(b.bytes, 8, "the allocation is charged its size");
}

/// ch04 R15's second form: comparing pointers into DIFFERENT allocations
/// observes their addresses; comparing within one allocation does not.
#[test]
fn cross_allocation_pointer_compare_is_an_observation() {
    for cross in [true, false] {
        let mut fx = Fx::new();
        let usize_ty = fx.ty(PrimKind::Usize);
        let ptr_ty = fx.ty(PrimKind::RawPtr);
        let bool_ty = fx.ty(PrimKind::Bool);
        let b = fx.reserve();
        fx.begin(b, ScopeId(0));
        let size = fx.const_int(8, usize_ty);
        let p = fx.emit(Op::Alloc, size.0, size.0, NO_OPERAND, ptr_ty);
        let q = if cross {
            fx.emit(Op::Alloc, size.0, size.0, NO_OPERAND, ptr_ty)
        } else {
            p
        };
        let eq = fx.emit(Op::Icmp(CmpPred::Eq), p.0, q.0, NO_OPERAND, bool_ty);
        fx.end(fx.term(Op::Ret, eq.0, NO_OPERAND, NO_OPERAND));
        let (prog, tys) = program(fx, None);
        let e = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default()).expect("runs");
        assert_eq!(e.observed_address, cross, "cross = {cross}");
        assert_eq!(e.value, vec![encode::BOOL, (!cross) as u8]);
    }
}

// -- the comptime column ------------------------------------------------------

/// ch04 R12, design §5.8/§6: every row whose `comptime` cell is `Forbidden`
/// stops the evaluation BEFORE the door runs — a build error naming the
/// intrinsic and the site, with no operand inspected and no host touched
/// (`evaluate` asserts the sealed oracle served nothing).
#[test]
fn every_forbidden_intrinsic_is_a_named_build_error() {
    let forbidden: Vec<_> = TABLE
        .iter()
        .filter(|r| r.comptime == When::Forbidden)
        .collect();
    assert!(forbidden.len() >= 8, "the host doors are all forbidden");
    for row in forbidden {
        let mut fx = Fx::new();
        let u64_ty = fx.ty(PrimKind::U64);
        let b = fx.reserve();
        fx.begin(b, ScopeId(0));
        let recv = fx.const_unit();
        let _ = intrinsic_call(&mut fx, &[recv], u64_ty, 11);
        fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        let (prog, tys) = program(fx, Some(row.name));
        let err = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default())
            .expect_err("a forbidden door is a build error");
        match &err.kind {
            ErrorKind::Fault(ComptimeFault::ForbiddenIntrinsic {
                intrinsic, site, ..
            }) => {
                assert_eq!(intrinsic, row.name);
                assert_eq!(*site, (11, 9), "the site of the call");
            }
            other => panic!("{}: expected ForbiddenIntrinsic, got {other:?}", row.name),
        }
        assert_eq!(err.code().as_string(), "A0012");
        assert!(err.message().contains(row.name) && err.message().contains("`setup`"));
    }
}

/// A program the table does not know is refused by name in either mode.
#[test]
fn an_intrinsic_outside_the_table_is_unknown() {
    let mut fx = Fx::new();
    let u64_ty = fx.ty(PrimKind::U64);
    let b = fx.reserve();
    fx.begin(b, ScopeId(0));
    let _ = intrinsic_call(&mut fx, &[], u64_ty, 3);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (prog, tys) = program(fx, Some("getenv"));
    let err = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default()).expect_err("unknown");
    assert!(matches!(
        err.kind,
        ErrorKind::Interp(InterpError::UnknownIntrinsic(ref n)) if n == "getenv"
    ));
}

// -- input_read ----------------------------------------------------------------

fn input_read_program(path: &str) -> (Program, TyStore) {
    let mut fx = Fx::new();
    let str_ty = fx.ty(PrimKind::Str);
    let b = fx.reserve();
    fx.begin(b, ScopeId(0));
    // `Fx::print`'s constant numbering starts at 0; this program prints
    // nothing, so constant 0 is ours.
    let s = fx.emit(Op::ConstStr, 0, NO_OPERAND, NO_OPERAND, str_ty);
    let data = intrinsic_call(&mut fx, &[s], str_ty, 4);
    fx.end(fx.term(Op::Ret, data.0, NO_OPERAND, NO_OPERAND));
    let (mut prog, tys) = program(fx, Some("input_read"));
    prog.fns[0].strings.push((0, path.as_bytes().to_vec()));
    (prog, tys)
}

/// ch04 R13 / ch10 R42: `input_read` serves exactly the bytes the build
/// declared and read, records the content hash it read, and rejects a path
/// the header does not declare — by name, as a build error.
#[test]
fn input_read_serves_declared_bytes_and_rejects_undeclared() {
    let (prog, tys) = input_read_program(".config");
    let inputs = DeclaredInputs::new(vec![(b".config".to_vec(), b"mode = fast\n".to_vec())]);
    let e = eval(&prog, &tys, &inputs, Limits::default()).expect("a declared read evaluates");
    let mut want = vec![encode::STR];
    want.extend_from_slice(&12u64.to_le_bytes());
    want.extend_from_slice(b"mode = fast\n");
    assert_eq!(e.value, want);
    assert_eq!(
        e.inputs_read,
        vec![(
            b".config".to_vec(),
            fors_index::fingerprint::hash_bytes(b"mode = fast\n")
        )]
    );

    let err = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default())
        .expect_err("an undeclared read is a build error");
    assert!(matches!(
        &err.kind,
        ErrorKind::Fault(ComptimeFault::UndeclaredInput { path, .. }) if path == ".config"
    ));
    assert_eq!(err.code().as_string(), "A0013");
    let other = DeclaredInputs::new(vec![(b"other".to_vec(), b"x".to_vec())]);
    assert!(eval(&prog, &tys, &other, Limits::default()).is_err());
}

/// ch10 R42: the comptime file read is comptime-only — its row's `run` cell
/// is `Forbidden`, so a run-mode machine refuses it by name.
#[test]
fn input_read_is_forbidden_at_run_time() {
    let (prog, tys) = input_read_program(".config");
    let got = fors_interp::run(&prog, &tys);
    assert_eq!(got, Err(InterpError::NotAtRunTime("input_read".into())));
}

// -- budgets ------------------------------------------------------------------

/// `b0: br b0` — runs until a budget stops it.
fn spin_program() -> (Program, TyStore) {
    let mut fx = Fx::new();
    let b = fx.reserve();
    fx.begin(b, ScopeId(0));
    fx.end(fx.term(Op::Br, b.0, NO_OPERAND, NO_OPERAND));
    program(fx, None)
}

/// ch04 R14: exceeding the step budget is a build error naming the
/// declaration, with the count — one past the limit, the first step that
/// did not fit; charged per instruction, never wall time.
#[test]
fn step_budget_is_named_with_the_counts() {
    let (prog, tys) = spin_program();
    let limits = Limits {
        step: 1000,
        ..Limits::default()
    };
    let err = eval(&prog, &tys, &DeclaredInputs::empty(), limits).expect_err("spins");
    assert_eq!(
        err.kind,
        ErrorKind::Fault(ComptimeFault::Budget(Exceeded::Steps {
            steps: 1001,
            limit: 1000
        }))
    );
    assert_eq!(err.steps, 1001);
    assert_eq!(err.code().as_string(), "A0014");
    assert!(err.message().contains("`setup`") && err.message().contains("COMPTIME_STEP_BUDGET"));
}

/// ch04 R14's allocation budget: bytes are charged per allocation.
#[test]
fn alloc_budget_is_named_with_the_counts() {
    let (prog, tys) = alloc_program(false);
    let limits = Limits {
        alloc: 4,
        ..Limits::default()
    };
    let err = eval(&prog, &tys, &DeclaredInputs::empty(), limits).expect_err("8 > 4 bytes");
    assert_eq!(
        err.kind,
        ErrorKind::Fault(ComptimeFault::Budget(Exceeded::Bytes {
            bytes: 8,
            limit: 4
        }))
    );
}

/// Owner Q6: the BUILD cap is the sum over evaluations, and exceeding it
/// names the most expensive declaration so far.
#[test]
fn build_step_cap_names_the_most_expensive_declaration() {
    let (prog, tys) = spin_program();
    let limits = Limits {
        step: 1000,
        alloc: 1 << 20,
        build_step: 2500,
    };
    let env = ComptimeEnv {
        inputs: &DeclaredInputs::empty(),
        limits,
        externs: &[],
    };
    let mut build = BuildMeter::new(&limits);
    for name in ["first", "second"] {
        let e = evaluate(&prog, &tys, &env, &mut build, name).expect_err("each spins");
        assert!(matches!(
            e.kind,
            ErrorKind::Fault(ComptimeFault::Budget(Exceeded::Steps { .. }))
        ));
    }
    assert_eq!(build.steps, 2002);
    let e = evaluate(&prog, &tys, &env, &mut build, "third").expect_err("the build cap trips");
    match &e.kind {
        ErrorKind::Fault(ComptimeFault::Budget(Exceeded::Build {
            build_steps,
            limit,
            most_expensive,
        })) => {
            assert_eq!(*limit, 2500);
            assert_eq!(
                *build_steps,
                2500 + 1,
                "every step charged, one past the cap"
            );
            assert_eq!(most_expensive.as_ref().map(|m| m.0.as_str()), Some("first"));
        }
        other => panic!("expected the build cap, got {other:?}"),
    }
    assert!(e.message().contains("COMPTIME_BUILD_STEP_BUDGET"));
    assert!(e.message().contains("`first`"));
}

// -- the memo -----------------------------------------------------------------

fn const_program(v: u64, extra: Option<u64>) -> (Program, TyStore) {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(PrimKind::I64);
    let b = fx.reserve();
    fx.begin(b, ScopeId(0));
    let x = fx.const_int(v, i64_ty);
    fx.end(fx.term(Op::Ret, x.0, NO_OPERAND, NO_OPERAND));
    let (mut prog, tys) = program(fx, None);
    if let Some(e) = extra {
        // A second declaration the thunk never calls.
        let mut fy = Fx::new();
        let _ = fy.ty(PrimKind::I64);
        let i64y = fy.ty(PrimKind::I64);
        let by = fy.reserve();
        fy.begin(by, ScopeId(0));
        let y = fy.const_int(e, i64y);
        fy.end(fy.term(Op::Ret, y.0, NO_OPERAND, NO_OPERAND));
        let (mut d, _, s) = fy.finish();
        d.decl = DeclKeyId(99);
        prog.fns.push(ProgFn {
            name: "unrelated".into(),
            decl: d,
            strings: s,
            intrinsics: Vec::new(),
        });
    }
    (prog, tys)
}

/// design §6: the key is `target_hash ‖ fmir hashes of the reachable
/// declarations ‖ input hashes ‖ budget` — a function of CONTENT. Equal
/// content gives an equal key (a hit that evaluates nothing); a changed
/// body, input or budget changes it; a declaration the evaluation cannot
/// reach does not enter it.
#[test]
fn comptime_memo_is_content_addressed_over_fmir() {
    let none = DeclaredInputs::empty();
    let lim = Limits::default();
    let t = target_hash(&Config::v0_1());
    let key = |p: &Program, i: &DeclaredInputs, l: &Limits| memo_key(p, t, i, l);
    let (a, tys) = const_program(42, None);
    let (a2, _) = const_program(42, None);
    let (b, _) = const_program(43, None);
    let (with1, _) = const_program(42, Some(1));
    let (with2, _) = const_program(42, Some(2));
    assert_eq!(key(&a, &none, &lim), key(&a2, &none, &lim), "same content");
    assert_ne!(key(&a, &none, &lim), key(&b, &none, &lim), "a body edit");
    assert_eq!(
        key(&with1, &none, &lim),
        key(&with2, &none, &lim),
        "an unreachable declaration is not part of the evaluation"
    );
    let in1 = DeclaredInputs::new(vec![(b"p".to_vec(), b"1".to_vec())]);
    let in2 = DeclaredInputs::new(vec![(b"p".to_vec(), b"2".to_vec())]);
    assert_ne!(key(&a, &in1, &lim), key(&a, &in2, &lim), "input content");
    let small = Limits { step: 10, ..lim };
    assert_ne!(key(&a, &none, &lim), key(&a, &none, &small), "the budget");
    let other_target = Config {
        ptr_bits: 32,
        ..Config::v0_1()
    };
    assert_ne!(
        memo_key(&a, target_hash(&other_target), &none, &lim),
        key(&a, &none, &lim),
        "the target"
    );

    // Through the memo: the second, content-equal program is a HIT and
    // charges the build nothing.
    let env = ComptimeEnv {
        inputs: &none,
        limits: lim,
        externs: &[],
    };
    let mut build = BuildMeter::new(&lim);
    let mut memo = Memo::new();
    let (first, hit1) =
        evaluate_memoized(&a, &tys, &env, &mut build, &mut memo, "setup").expect("evaluates");
    let charged = build.steps;
    let (second, hit2) =
        evaluate_memoized(&a2, &tys, &env, &mut build, &mut memo, "setup").expect("hits");
    assert!(!hit1 && hit2);
    assert_eq!(first.to_bytes(), second.to_bytes());
    assert_eq!(build.steps, charged, "a hit evaluates nothing");
    assert_eq!(memo.hit_rate(), Some(0.5));
    let mut want = vec![encode::INT, 64, 1];
    want.extend_from_slice(&42u64.to_le_bytes());
    assert_eq!(first.value, want);
}

// -- step accounting, counted by hand --------------------------------------

/// ch04 R14, design §6: one step per INSTRUCTION and one per TERMINATOR,
/// nothing else. Two blocks — three constants and a `br`, then two
/// constants and a `ret` — are exactly 3 + 1 + 2 + 1 = 7 steps, and a
/// budget of 6 stops on the seventh.
#[test]
fn steps_are_one_per_instruction_and_terminator() {
    let build = || {
        let mut fx = Fx::new();
        let i64_ty = fx.ty(PrimKind::I64);
        let a = fx.reserve();
        let b = fx.reserve();
        fx.begin(a, ScopeId(0));
        let _ = fx.const_int(1, i64_ty);
        let _ = fx.const_int(2, i64_ty);
        let _ = fx.const_int(3, i64_ty);
        fx.end(fx.term(Op::Br, b.0, NO_OPERAND, NO_OPERAND));
        fx.begin(b, ScopeId(0));
        let _ = fx.const_int(4, i64_ty);
        let x = fx.const_int(5, i64_ty);
        fx.end(fx.term(Op::Ret, x.0, NO_OPERAND, NO_OPERAND));
        program(fx, None)
    };
    let (prog, tys) = build();
    let ev = eval(&prog, &tys, &DeclaredInputs::empty(), Limits::default()).expect("evaluates");
    assert_eq!((ev.steps, ev.bytes), (7, 0), "3 insts + br + 2 insts + ret");
    let (prog, tys) = build();
    let err = eval(
        &prog,
        &tys,
        &DeclaredInputs::empty(),
        Limits {
            step: 6,
            ..Limits::default()
        },
    )
    .expect_err("the seventh step does not fit");
    assert_eq!(
        err.kind,
        ErrorKind::Fault(ComptimeFault::Budget(Exceeded::Steps {
            steps: 7,
            limit: 6
        }))
    );
}
