//! M2-0's OIR gates (`docs/design/m2-dev-backend.md` §10 M2-0 gate table):
//! `oir_from_fmir_subset_counts`, `oir_verify_requires_secret_and_ct`,
//! `oir_verify_requires_alias_class`, `oir_rejects_tile_op`.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::{PrimKind, TY_UNIT, TyId, TyStore};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::{BlockPool, BlockRow};
use fors_fmir::decl::DeclFmir;
use fors_fmir::flags::CT_UNSPECIFIED;
use fors_fmir::ids::{BlockId, InstId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow};
use fors_fmir::op::{ArithMode, CmpPred, NO_OPERAND, Op};
use fors_fmir::value::{ValDef, ValRow};
use fors_index::interner::Symbol;
use fors_oir::from_fmir::reason;
use fors_oir::{AliasClass, FmirInput, OirFunc, OirOp, VerifyError, from_fmir, verify};

struct B {
    tys: TyStore,
    d: DeclFmir,
}

impl B {
    fn new() -> B {
        let mut d = DeclFmir::empty(DeclKeyId(7), FnSigId(7));
        d.blocks = BlockPool::new();
        B {
            tys: TyStore::new(),
            d,
        }
    }
    fn t(&mut self, p: PrimKind) -> TyId {
        self.tys.prim(p)
    }
    fn row(&mut self, op: Op, a: u32, b: u32, ty: TyId) -> ValId {
        let inst = self.d.insts.len() as u32;
        let v = self
            .d
            .push_val(ValRow::new(ty, false, 0, ValDef::Inst(InstId(inst))));
        self.void(op, a, b, ty);
        v
    }
    fn void(&mut self, op: Op, a: u32, b: u32, ty: TyId) {
        self.d.push_inst(
            InstRow {
                op,
                a,
                b,
                c: NO_OPERAND,
                ty,
                site: SiteId(0),
            },
            AliasSeed::None,
        );
    }
    fn intrinsic(&mut self, sym: u32, args: &[ValId]) {
        let convs = vec![Conv::Let; args.len()];
        let range = self.d.insts.push_operands(args, &convs);
        let call = self.d.insts.push_call(CallRow {
            callee: Callee::Intrinsic(Symbol(sym)),
            args: range,
        });
        self.void(Op::Intrinsic, call, NO_OPERAND, TY_UNIT);
    }
    fn finish(mut self) -> (DeclFmir, TyStore) {
        let n = self.d.insts.len() as u32;
        let mut pool = BlockPool::new();
        pool.push(BlockRow {
            first_inst: 0,
            inst_len: n,
            term: InstRow {
                op: Op::Ret,
                a: NO_OPERAND,
                b: NO_OPERAND,
                c: NO_OPERAND,
                ty: TY_UNIT,
                site: SiteId(0),
            },
            scope: ScopeId(0),
        });
        self.d.blocks = pool;
        self.d.entry = BlockId(0);
        (self.d, self.tys)
    }
}

const STRINGS: &[(u32, &[u8])] = &[(0, b"hi")];

fn lower(d: &DeclFmir, tys: &TyStore) -> Result<OirFunc, fors_oir::Refusal> {
    let strings: Vec<(u32, Vec<u8>)> = STRINGS.iter().map(|(i, s)| (*i, s.to_vec())).collect();
    let intrinsics = vec![
        (1, "stdout_write_line".to_string()),
        (2, "stdout_write_uint".to_string()),
        (3, "clock_mono".to_string()),
    ];
    from_fmir(&FmirInput {
        decl: d,
        tys,
        strings: &strings,
        intrinsics: &intrinsics,
    })
}

/// A body that uses every op of M2-0's subset at least once.
fn every_subset_op() -> (DeclFmir, TyStore) {
    let mut b = B::new();
    let i32t = b.t(PrimKind::I32);
    let u8t = b.t(PrimKind::U8);
    let boolt = b.t(PrimKind::Bool);
    let strt = b.t(PrimKind::Str);
    let x = b.row(Op::ConstInt, 5, 0, i32t);
    let y = b.row(Op::ConstInt, 3, 0, i32t);
    for m in [ArithMode::Trap, ArithMode::Wrap, ArithMode::Sat] {
        for op in [
            Op::Add(m),
            Op::Sub(m),
            Op::Mul(m),
            Op::Div(m),
            Op::Rem(m),
            Op::Shl(m),
            Op::Shr(m),
        ] {
            b.row(op, x.0, y.0, i32t);
        }
        b.row(Op::Neg(m), x.0, NO_OPERAND, i32t);
    }
    for op in [Op::And, Op::Or, Op::Xor] {
        b.row(op, x.0, y.0, i32t);
    }
    b.row(Op::Not, x.0, NO_OPERAND, i32t);
    let c = b.row(Op::Icmp(CmpPred::Lt), x.0, y.0, boolt);
    let t = b.row(Op::ConstBool, 1, NO_OPERAND, boolt);
    b.row(Op::Xor, c.0, t.0, boolt);
    for op in [Op::ConvChecked, Op::ConvWrap, Op::ConvSat] {
        b.row(op, x.0, NO_OPERAND, u8t);
    }
    let p = b.d.places.intern(0, &[], i32t);
    b.void(Op::Init, p.0, x.0, TY_UNIT);
    let l = b.row(Op::CopyFrom, p.0, NO_OPERAND, i32t);
    let unit = b.row(Op::ConstUnit, NO_OPERAND, NO_OPERAND, TY_UNIT);
    b.intrinsic(2, &[unit, l]);
    let s = b.row(Op::ConstStr, 0, NO_OPERAND, strt);
    b.intrinsic(1, &[unit, s]);
    b.finish()
}

#[test]
fn oir_from_fmir_subset_counts() {
    let (d, tys) = every_subset_op();
    assert!(
        fors_fmir::verify::verify(&d).is_empty(),
        "fixture is valid FMIR"
    );
    let f = lower(&d, &tys).expect("every subset op lowers");
    verify(&f).expect("and verifies");
    assert_eq!(f.rows.len(), d.insts.len(), "one OIR row per FMIR row");
    assert_eq!(f.slots.len(), 1);
    let dump = fors_oir::dump::dump(&f);
    assert!(
        dump.contains("slot_store $s0") && dump.contains("{root 0, affine}"),
        "{dump}"
    );

    // Every op outside the subset is refused BY NAME.
    for op in [
        Op::Fadd(Default::default()),
        Op::ConvTrunc,
        Op::Alloc,
        Op::Free,
        Op::CallDirect,
        Op::AggNew,
        Op::Index,
        Op::Declassify,
        Op::TileOp,
    ] {
        let mut b = B::new();
        let i64t = b.t(PrimKind::I64);
        let x = b.row(Op::ConstInt, 1, 0, i64t);
        b.row(op, x.0, x.0, i64t);
        let (d, tys) = b.finish();
        let r = lower(&d, &tys).expect_err("out of subset");
        assert_eq!(r.reason, reason::OP, "{op:?}");
        assert_eq!(r.inst, Some(1));
        assert_eq!(r.op, format!("{op:?}"), "the refusal names the op");
    }
    // An intrinsic other than the two output rows.
    let mut b = B::new();
    let unit = b.row(Op::ConstUnit, NO_OPERAND, NO_OPERAND, TY_UNIT);
    b.intrinsic(3, &[unit, unit]);
    let (d, tys) = b.finish();
    assert_eq!(lower(&d, &tys).unwrap_err().reason, reason::INTRINSIC);
}

fn valid() -> OirFunc {
    let (d, tys) = every_subset_op();
    let f = lower(&d, &tys).unwrap();
    verify(&f).unwrap();
    f
}

#[test]
fn oir_verify_requires_secret_and_ct() {
    let mut f = valid();
    f.values.secret.pop();
    let e = verify(&f).unwrap_err();
    assert!(matches!(e, VerifyError::MissingSecret { .. }), "{e}");
    assert_eq!(e.name(), "missing-secret");

    let mut f = valid();
    f.values.ct.pop();
    assert_eq!(verify(&f).unwrap_err().name(), "missing-ct");

    let mut f = valid();
    f.values.ct[3] = CT_UNSPECIFIED;
    assert_eq!(
        verify(&f).unwrap_err(),
        VerifyError::MissingCt { value: 3 },
        "the unspecified sentinel is not a ct"
    );
}

#[test]
fn oir_verify_requires_alias_class() {
    let f = valid();
    let slot_row = f
        .rows
        .op
        .iter()
        .position(|&o| o == OirOp::SlotStore)
        .unwrap();
    let mut g = f.clone();
    g.rows.alias[slot_row] = None;
    let e = verify(&g).unwrap_err();
    assert_eq!(
        e,
        VerifyError::MissingAliasClass {
            row: slot_row as u32
        }
    );
    assert_eq!(e.name(), "missing-alias-class");

    let mut g = f.clone();
    let Some(AliasClass::Root { source, .. }) = g.rows.alias[slot_row] else {
        unreachable!()
    };
    g.rows.alias[slot_row] = Some(AliasClass::Root { root: 99, source });
    assert_eq!(verify(&g).unwrap_err().name(), "untraceable-alias-class");
}

#[test]
fn oir_rejects_tile_op() {
    let mut f = valid();
    let n = f.rows.len() as u32;
    f.rows.push(
        OirOp::Tile,
        fors_oir::NONE,
        fors_oir::NONE,
        fors_oir::LowTy::Unit,
        fors_oir::Mode::None,
        None,
        0,
        fors_oir::NONE,
    );
    let e = verify(&f).unwrap_err();
    assert_eq!(e, VerifyError::TileOp { row: n });
    assert_eq!(e.name(), "tile-op-at-oir");
}
