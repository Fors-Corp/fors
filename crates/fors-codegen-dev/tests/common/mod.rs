//! A straight-line FMIR builder for the backend's tests: one function, one
//! block (or more, to test that refusal), lowered through
//! `fors_oir::from_fmir` exactly as the oracle does.

#![allow(dead_code)]

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::{PrimKind, TY_UNIT, TyId, TyStore};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::{BlockPool, BlockRow};
use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{BlockId, InstId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow};
use fors_fmir::op::{NO_OPERAND, Op, TrapKind};
use fors_fmir::place::Seg;
use fors_fmir::value::{ValDef, ValRow};
use fors_index::interner::Symbol;
use fors_oir::{FmirInput, OirFunc, Refusal};

pub struct B {
    pub tys: TyStore,
    pub d: DeclFmir,
    pub strings: Vec<(u32, Vec<u8>)>,
    unit: Option<ValId>,
    extra_blocks: u32,
    term: InstRow,
}

pub const INTRINSICS: [(u32, &str); 3] = [
    (1, "stdout_write_line"),
    (2, "stdout_write_uint"),
    (3, "clock_mono"),
];

impl Default for B {
    fn default() -> Self {
        Self::new()
    }
}

impl B {
    pub fn new() -> B {
        let mut d = DeclFmir::empty(DeclKeyId(1000), FnSigId(1000));
        d.blocks = BlockPool::new();
        B {
            tys: TyStore::new(),
            d,
            strings: Vec::new(),
            unit: None,
            extra_blocks: 0,
            term: InstRow {
                op: Op::Ret,
                a: NO_OPERAND,
                b: NO_OPERAND,
                c: NO_OPERAND,
                ty: TY_UNIT,
                site: SiteId(0),
            },
        }
    }

    pub fn t(&mut self, p: PrimKind) -> TyId {
        self.tys.prim(p)
    }

    pub fn val(&mut self, op: Op, a: u32, b: u32, ty: TyId, secret: bool) -> ValId {
        let inst = self.d.insts.len() as u32;
        let v = self
            .d
            .push_val(ValRow::new(ty, secret, 0, ValDef::Inst(InstId(inst))));
        self.void(op, a, b, ty);
        v
    }

    pub fn row(&mut self, op: Op, a: u32, b: u32, ty: TyId) -> ValId {
        self.val(op, a, b, ty, false)
    }

    pub fn void(&mut self, op: Op, a: u32, b: u32, ty: TyId) {
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

    pub fn int(&mut self, p: PrimKind, bits: u64) -> ValId {
        let t = self.t(p);
        self.row(Op::ConstInt, bits as u32, (bits >> 32) as u32, t)
    }

    pub fn unit(&mut self) -> ValId {
        if let Some(u) = self.unit {
            return u;
        }
        let u = self.row(Op::ConstUnit, NO_OPERAND, NO_OPERAND, TY_UNIT);
        self.unit = Some(u);
        u
    }

    pub fn intrinsic(&mut self, sym: u32, args: &[ValId]) {
        let convs = vec![Conv::Let; args.len()];
        let range = self.d.insts.push_operands(args, &convs);
        let call = self.d.insts.push_call(CallRow {
            callee: Callee::Intrinsic(Symbol(sym)),
            args: range,
        });
        self.void(Op::Intrinsic, call, NO_OPERAND, TY_UNIT);
    }

    pub fn write_uint(&mut self, v: ValId) {
        let u = self.unit();
        self.intrinsic(2, &[u, v]);
    }

    pub fn write_line(&mut self, text: &[u8]) {
        let id = self.strings.len() as u32;
        self.strings.push((id, text.to_vec()));
        let u = self.unit();
        let st = self.t(PrimKind::Str);
        let s = self.row(Op::ConstStr, id, NO_OPERAND, st);
        self.intrinsic(1, &[u, s]);
    }

    pub fn init(&mut self, root: u32, v: ValId, ty: TyId, path: &[Seg]) {
        let p = self.d.places.intern(root, path, ty);
        self.void(Op::Init, p.0, v.0, TY_UNIT);
    }

    pub fn param(&mut self, p: PrimKind) -> ValId {
        let t = self.t(p);
        self.d.push_val(ValRow::new(t, false, 0, ValDef::Param(0)))
    }

    pub fn extra_block(&mut self) {
        self.extra_blocks += 1;
    }

    pub fn trap(&mut self, k: TrapKind) {
        self.term.op = Op::Trap;
        self.term.a = k as u32;
    }

    pub fn finish(mut self) -> (DeclFmir, TyStore, Vec<(u32, Vec<u8>)>) {
        let n = self.d.insts.len() as u32;
        let mut pool = BlockPool::new();
        pool.push(BlockRow {
            first_inst: 0,
            inst_len: n,
            term: self.term,
            scope: ScopeId(0),
        });
        for _ in 0..self.extra_blocks {
            pool.push(BlockRow {
                first_inst: n,
                inst_len: 0,
                term: self.term,
                scope: ScopeId(0),
            });
        }
        self.d.blocks = pool;
        self.d.entry = BlockId(0);
        (self.d, self.tys, self.strings)
    }

    /// FMIR -> OIR, as the oracle's native engine does.
    pub fn lower(self) -> Result<OirFunc, Refusal> {
        let (d, tys, strings) = self.finish();
        let intrinsics: Vec<(u32, String)> = INTRINSICS
            .iter()
            .map(|(s, n)| (*s, n.to_string()))
            .collect();
        fors_oir::from_fmir(&FmirInput {
            decl: &d,
            tys: &tys,
            strings: &strings,
            intrinsics: &intrinsics,
        })
    }
}
