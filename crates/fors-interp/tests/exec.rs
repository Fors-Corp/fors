//! Dispatch-loop tests over hand-built FMIR (design §5.1-§5.4).
//!
//! These cover what end-to-end lowering cannot spell yet (explicit
//! arithmetic modes, direct trap terminators, malformed programs) plus the
//! F1 structural gates: no optimisation-level input, no host word size in
//! `value.rs`/`arith.rs`, no fused or libm float remainder in `src/`.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::FnSigId;
use fors_fir::ty::{PrimKind, TyId, TyStore};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::BlockRow;
use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{BlockId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow};
use fors_fmir::op::{ArithMode, NO_OPERAND, Op, TrapKind};
use fors_fmir::value::{ValDef, ValRow};
use fors_index::interner::Symbol;
use fors_interp::{Config, Endian, Exit, InterpError, ProgFn, Program, run};

/// Minimal FMIR builder for tests: one block at a time, values in order.
struct B {
    tys: TyStore,
    decl: DeclFmir,
    /// (block, start) pairs under construction.
    starts: Vec<usize>,
    insts: Vec<InstRow>,
    cur: usize,
}

impl B {
    fn new() -> B {
        let tys = TyStore::new();
        let decl = DeclFmir::empty(DeclKeyId(7), FnSigId(9));
        B {
            tys,
            decl,
            starts: vec![0],
            insts: Vec::new(),
            cur: 0,
        }
    }

    fn ty(&mut self, p: PrimKind) -> TyId {
        self.tys.prim(p)
    }

    fn val(&mut self, ty: TyId) -> ValId {
        let inst = self.insts.len() as u32;
        self.decl.push_val(ValRow::new(
            ty,
            false,
            0,
            ValDef::Inst(fors_fmir::ids::InstId(inst)),
        ))
    }

    fn emit(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) -> ValId {
        let v = self.val(ty);
        self.insts.push(InstRow {
            op,
            a,
            b,
            c,
            ty,
            site: SiteId(0),
        });
        v
    }

    fn const_int(&mut self, v: u64, ty: TyId) -> ValId {
        self.emit(Op::ConstInt, v as u32, (v >> 32) as u32, NO_OPERAND, ty)
    }

    fn const_str(&mut self, cid: u32, ty: TyId) -> ValId {
        self.emit(Op::ConstStr, cid, NO_OPERAND, NO_OPERAND, ty)
    }

    fn term(&mut self, op: Op, a: u32, b: u32, c: u32) {
        let start = self.starts[self.cur];
        let row = BlockRow {
            first_inst: start as u32,
            inst_len: (self.insts.len() - start) as u32,
            term: InstRow {
                op,
                a,
                b,
                c,
                ty: fors_fir::ty::TY_UNIT,
                site: SiteId(0),
            },
            scope: ScopeId(0),
        };
        // Tests build blocks in order, so pushing directly is exact.
        self.decl.blocks.push(row);
    }

    fn finish(mut self) -> (DeclFmir, TyStore) {
        for row in std::mem::take(&mut self.insts) {
            self.decl.push_inst(row, AliasSeed::None);
        }
        // Drop `empty`'s sentinel block (index 0); tests built theirs after.
        let mut blocks = fors_fmir::block::BlockPool::new();
        for (_, b) in self.decl.blocks.all_rows().skip(1) {
            blocks.push(b);
        }
        self.decl.blocks = blocks;
        self.decl.entry = BlockId(0);
        (self.decl, self.tys)
    }
}

fn prog_of(
    decl: DeclFmir,
    strings: Vec<(u32, Vec<u8>)>,
    intrinsics: Vec<(u32, String)>,
) -> Program {
    Program {
        fns: vec![ProgFn {
            name: "main".into(),
            decl,
            strings,
            intrinsics,
        }],
        entry: 0,
        config: Config::v0_1(),
    }
}

#[test]
fn const_add_returns() {
    let mut b = B::new();
    let i32 = b.ty(PrimKind::I32);
    let x = b.const_int(20, i32);
    let y = b.const_int(22, i32);
    let z = b.emit(Op::Add(ArithMode::Trap), x.0, y.0, NO_OPERAND, i32);
    b.term(Op::Ret, z.0, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    assert!(fors_fmir::verify::is_ok(&decl));
    let out = run(&prog_of(decl, vec![], vec![]), &tys).unwrap();
    assert_eq!(out.exit, Exit::Return);
}

#[test]
fn trapping_ops_become_trap_outcomes() {
    for (op, a, b, kind) in [
        (
            Op::Add(ArithMode::Trap),
            0x7FFF_FFFFu64,
            1u64,
            TrapKind::Overflow,
        ),
        (Op::Sub(ArithMode::Trap), 0x8000_0000, 1, TrapKind::Overflow),
        (Op::Div(ArithMode::Trap), 10, 0, TrapKind::DivZero),
        (Op::Shl(ArithMode::Trap), 1, 32, TrapKind::Shift),
        (Op::ConvChecked, 300, 0, TrapKind::CheckedConversion),
    ] {
        let mut bx = B::new();
        let (from, to) = if matches!(op, Op::ConvChecked) {
            (bx.ty(PrimKind::U32), bx.ty(PrimKind::U8))
        } else {
            (bx.ty(PrimKind::I32), bx.ty(PrimKind::I32))
        };
        let x = bx.const_int(a, from);
        // `ConvChecked` is unary; the binary ops read a second operand.
        let inst = if matches!(op, Op::ConvChecked) {
            bx.emit(op, x.0, NO_OPERAND, NO_OPERAND, to)
        } else {
            let y = bx.const_int(b, from);
            bx.emit(op, x.0, y.0, NO_OPERAND, to)
        };
        let _ = inst;
        bx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
        let (decl, tys) = bx.finish();
        assert!(fors_fmir::verify::is_ok(&decl));
        let out = run(&prog_of(decl, vec![], vec![]), &tys).unwrap();
        assert_eq!(out.exit, Exit::Trap(kind), "op {op:?}");
    }
}

#[test]
fn trap_terminator_aborts_with_its_kind() {
    let mut b = B::new();
    b.term(Op::Trap, TrapKind::Bounds as u32, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    assert!(fors_fmir::verify::is_ok(&decl));
    let out = run(&prog_of(decl, vec![], vec![]), &tys).unwrap();
    assert_eq!(out.exit, Exit::Trap(TrapKind::Bounds));
}

#[test]
fn call_direct_runs_the_callee() {
    // callee: `add_one(a) = a + 1`.
    let mut c = B::new();
    let i32 = c.ty(PrimKind::I32);
    let pa = c
        .decl
        .push_val(ValRow::new(i32, false, 0, ValDef::Param(0)));
    let one = c.const_int(1, i32);
    let r = c.emit(Op::Add(ArithMode::Trap), pa.0, one.0, NO_OPERAND, i32);
    c.term(Op::Ret, r.0, NO_OPERAND, NO_OPERAND);
    let (mut cdecl, tys) = c.finish();
    cdecl.decl = DeclKeyId(100);
    // caller: `main = add_one(41)` then write nothing; assert via return.
    let mut m = B::new();
    let i32m = m.ty(PrimKind::I32);
    let arg = m.const_int(41, i32m);
    let range = m
        .decl
        .insts
        .push_operands(&[arg], &[fors_fir::sig::Conv::Let]);
    let call = m.decl.insts.push_call(CallRow {
        callee: Callee::Direct(DeclKeyId(100)),
        args: range,
    });
    let v = m.emit(Op::CallDirect, call, NO_OPERAND, NO_OPERAND, i32m);
    // The entry return value is not observable, so the oracle is a trap:
    // `1 / (v - 42)` traps `div-zero` exactly when the callee answered 42.
    let f = m.const_int(42, i32m);
    let d = m.emit(Op::Sub(ArithMode::Trap), v.0, f.0, NO_OPERAND, i32m);
    let one = m.const_int(1, i32m);
    let _ = m.emit(Op::Div(ArithMode::Trap), one.0, d.0, NO_OPERAND, i32m);
    m.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (mdecl, _) = m.finish();
    // Both builders interned `i32` first in a fresh store, so the ids agree.
    let prog = Program {
        fns: vec![
            ProgFn {
                name: "add_one".into(),
                decl: cdecl,
                strings: vec![],
                intrinsics: vec![],
            },
            ProgFn {
                name: "main".into(),
                decl: mdecl,
                strings: vec![],
                intrinsics: vec![],
            },
        ],
        entry: 1,
        config: Config::v0_1(),
    };
    let out = run(&prog, &tys).unwrap();
    assert_eq!(out.exit, Exit::Trap(TrapKind::DivZero));
}

#[test]
fn stdout_write_line_appends_lines() {
    let mut b = B::new();
    let str_ty = b.ty(PrimKind::Str);
    let sym = Symbol(3);
    let s0 = b.const_str(0, str_ty);
    let s1 = b.const_str(1, str_ty);
    let recv = b.emit(
        Op::ConstUnit,
        NO_OPERAND,
        NO_OPERAND,
        NO_OPERAND,
        fors_fir::ty::TY_UNIT,
    );
    for s in [s0, s1] {
        let range = b.decl.insts.push_operands(
            &[recv, s],
            &[fors_fir::sig::Conv::Let, fors_fir::sig::Conv::Let],
        );
        let call = b.decl.insts.push_call(CallRow {
            callee: Callee::Intrinsic(sym),
            args: range,
        });
        b.emit(
            Op::Intrinsic,
            call,
            NO_OPERAND,
            NO_OPERAND,
            fors_fir::ty::TY_UNIT,
        );
    }
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let prog = prog_of(
        decl,
        vec![(0, b"ok".to_vec()), (1, b"fail".to_vec())],
        vec![(sym.0, "stdout_write_line".into())],
    );
    let out = run(&prog, &tys).unwrap();
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"ok\nfail\n");
}

/// One `intrinsic` call with a result: `callee(args...) -> ty`.
fn call_intrinsic(b: &mut B, sym: Symbol, args: &[ValId], ty: TyId) -> ValId {
    let convs = vec![fors_fir::sig::Conv::Let; args.len()];
    let range = b.decl.insts.push_operands(args, &convs);
    let call = b.decl.insts.push_call(CallRow {
        callee: Callee::Intrinsic(sym),
        args: range,
    });
    b.emit(Op::Intrinsic, call, NO_OPERAND, NO_OPERAND, ty)
}

/// F7 (ch10 R26): `str_byte_slice(s, start, end)` is a fresh `Str` handle
/// over exactly `s[start ..< end]`, observed through `write_line`.
#[test]
fn str_byte_slice_materialises_the_byte_range() {
    let mut b = B::new();
    let str_ty = b.ty(PrimKind::Str);
    let usize_ty = b.ty(PrimKind::Usize);
    let (slice_sym, line_sym) = (Symbol(3), Symbol(4));
    let s = b.const_str(0, str_ty);
    let start = b.const_int(1, usize_ty);
    let end = b.const_int(3, usize_ty);
    let sub = call_intrinsic(&mut b, slice_sym, &[s, start, end], str_ty);
    let recv = b.emit(
        Op::ConstUnit,
        NO_OPERAND,
        NO_OPERAND,
        NO_OPERAND,
        fors_fir::ty::TY_UNIT,
    );
    call_intrinsic(&mut b, line_sym, &[recv, sub], fors_fir::ty::TY_UNIT);
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    // "a\xc3\xa9b": bytes 1..<3 are the two-byte sequence for U+00E9.
    let prog = prog_of(
        decl,
        vec![(0, b"a\xc3\xa9b".to_vec())],
        vec![
            (slice_sym.0, "str_byte_slice".into()),
            (line_sym.0, "stdout_write_line".into()),
        ],
    );
    let out = run(&prog, &tys).unwrap();
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(out.stdout, b"\xc3\xa9\n");
}

/// A range past the handle's bytes is a bug (`Str.slice`'s own `pre` runs
/// first in Fors): trap `bounds`, never a clamp.
#[test]
fn str_byte_slice_past_end_traps_bounds() {
    let mut b = B::new();
    let str_ty = b.ty(PrimKind::Str);
    let usize_ty = b.ty(PrimKind::Usize);
    let sym = Symbol(3);
    let s = b.const_str(0, str_ty);
    let start = b.const_int(2, usize_ty);
    let end = b.const_int(10, usize_ty);
    call_intrinsic(&mut b, sym, &[s, start, end], str_ty);
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let prog = prog_of(
        decl,
        vec![(0, b"abc".to_vec())],
        vec![(sym.0, "str_byte_slice".into())],
    );
    let out = run(&prog, &tys).unwrap();
    assert_eq!(out.exit, Exit::Trap(TrapKind::Bounds));
}

/// A `Str` intrinsic whose receiver is not a handle into the byte table is
/// a lowering bug, reported as a diagnostic — never a zero length or an
/// empty string (F7 verification: a user method that merely shares the
/// intrinsic's spelling used to reach here and print `0`).
#[test]
fn str_intrinsic_on_a_non_str_receiver_is_a_diagnostic() {
    let mut b = B::new();
    let usize_ty = b.ty(PrimKind::Usize);
    let sym = Symbol(3);
    let bogus = b.const_int(999, usize_ty);
    call_intrinsic(&mut b, sym, &[bogus], usize_ty);
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let prog = prog_of(decl, vec![], vec![(sym.0, "str_byte_len".into())]);
    let err = run(&prog, &tys).unwrap_err();
    assert!(matches!(err, InterpError::MissingString(999)), "{err:?}");
}

#[test]
fn unsupported_op_is_a_diagnostic_not_a_trap() {
    let mut b = B::new();
    let i32 = b.ty(PrimKind::I32);
    let x = b.const_int(1, i32);
    // `const_fn` is verifier-clean but outside the F1 execution subset.
    let _ = b.emit(Op::ConstFn, x.0, NO_OPERAND, NO_OPERAND, i32);
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    assert!(fors_fmir::verify::is_ok(&decl));
    let err = run(&prog_of(decl, vec![], vec![]), &tys).unwrap_err();
    assert!(matches!(err, InterpError::UnsupportedOp(_)), "{err:?}");
}

#[test]
fn dangling_block_is_a_diagnostic_never_a_panic() {
    let mut b = B::new();
    b.term(Op::Br, 99, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let err = run(&prog_of(decl, vec![], vec![]), &tys).unwrap_err();
    assert!(matches!(err, InterpError::DanglingBlock(99)), "{err:?}");
}

#[test]
fn unknown_intrinsic_is_a_diagnostic() {
    let mut b = B::new();
    let sym = Symbol(11);
    let call = b.decl.insts.push_call(CallRow {
        callee: Callee::Intrinsic(sym),
        args: 0..0,
    });
    b.emit(
        Op::Intrinsic,
        call,
        NO_OPERAND,
        NO_OPERAND,
        fors_fir::ty::TY_UNIT,
    );
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let err = run(&prog_of(decl, vec![], vec![]), &tys).unwrap_err();
    assert!(matches!(err, InterpError::UnknownIntrinsic(_)), "{err:?}");
}

#[test]
fn uninit_place_read_is_a_ub_report_not_a_trap() {
    // F1 reported this as an `InterpError`; **F6 promoted it** to design
    // §5.2's row "Uninitialised read (incl. through `&out`) ->
    // `ub: uninit-read`", which exits 70 with a machine-readable record and
    // is still not a trap (ch02 R15's kind list is closed at eight, E4).
    let mut b = B::new();
    let i32 = b.ty(PrimKind::I32);
    let pid = b.decl.places.intern(0, &[], i32);
    let _ = b.emit(Op::CopyFrom, pid.0, NO_OPERAND, NO_OPERAND, i32);
    b.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let out = run(&prog_of(decl, vec![], vec![]), &tys).expect("a ub: report, not an error");
    assert_eq!(out.exit, Exit::Ub(fors_interp::UbClass::UninitRead));
    assert!(!matches!(out.exit, Exit::Trap(_)));
    assert_eq!(
        fors_interp::entry_exit(&out),
        fors_interp::ExitStatus::Status(fors_interp::UB_EXIT_STATUS)
    );
}

#[test]
fn reaching_unreachable_is_a_diagnostic() {
    let mut b = B::new();
    b.term(Op::Unreachable, NO_OPERAND, NO_OPERAND, NO_OPERAND);
    let (decl, tys) = b.finish();
    let err = run(&prog_of(decl, vec![], vec![]), &tys).unwrap_err();
    assert!(matches!(err, InterpError::TypeMismatch(_)), "{err:?}");
}

#[test]
fn interp_has_no_opt_level_input() {
    // Exhaustive construction: adding an optimisation-level field to
    // `Config` breaks this test at compile time (design §3.6, ch02 R10).
    let c = Config {
        ptr_bits: 64,
        endian: Endian::Little,
    };
    assert_eq!(c, Config::v0_1());
}

fn src_files() -> Vec<(String, String)> {
    let dir = format!("{}/src", env!("CARGO_MANIFEST_DIR"));
    let mut out = Vec::new();
    for name in ["lib.rs", "value.rs", "arith.rs", "exec.rs", "program.rs"] {
        let path = format!("{dir}/{name}");
        let text = std::fs::read_to_string(&path).unwrap();
        out.push((name.to_string(), text));
    }
    out
}

#[test]
fn no_host_word_size_in_value_or_arith() {
    // Design §5.1: program-visible values never flow through the host word
    // size. The FILES `value.rs`/`arith.rs` must not even name it.
    for (name, text) in src_files() {
        if name == "value.rs" || name == "arith.rs" {
            assert!(
                !text.contains("usize"),
                "{name} mentions the host word size"
            );
        }
    }
}

#[test]
fn no_fma_or_libm_float_rem() {
    // Design §5.5/§5.6: no fused ops, no host libm, no float `%` anywhere
    // in `src/` (tests may use integer `%` freely; they are not the oracle).
    for (name, text) in src_files() {
        assert!(!text.contains("mul_add"), "{name} contains mul_add");
        assert!(!text.contains("fmod"), "{name} contains fmod");
        for (i, line) in text.lines().enumerate() {
            let has_pct = line.contains('%');
            let looks_float = line.contains("f32") || line.contains("f64") || line.contains("frem");
            assert!(
                !(has_pct && looks_float),
                "{name}:{} looks like float `%`: {line}",
                i + 1
            );
        }
    }
}
