//! Shared by the `tests/native*.rs` files: a tiny straight-line FMIR builder
//! (one function `main`, one block, no parameters — exactly M2-0's surface)
//! and the arithmetic edge-table cases whose expected output comes from
//! `fors_interp::arith`, the executable definition of every integer op
//! (`docs/design/m2-dev-backend.md` §10 M2-0: "Semantics are
//! `fors-interp/src/arith.rs`, not this document").
//!
//! The FMIR text format (`fors_fmir::parse`) deliberately has no constants
//! (see `fors-fmir/src/dump.rs`'s scope note), so a program that must trip a
//! trap on known values is built through the pool API here instead.

#![allow(dead_code)]

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::{PrimKind, TY_UNIT, TyId, TyStore};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::{BlockPool, BlockRow};
use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{BlockId, InstId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow};
use fors_fmir::op::{ArithMode, CmpPred, NO_OPERAND, Op, TrapKind};
use fors_fmir::value::{ValDef, ValRow};
use fors_index::interner::Symbol;
use fors_interp::arith::{self, IntKind, NumKind};
use fors_interp::{Config, ProgFn, Program};
use fors_oracle::Candidate;

pub const WRITE_LINE: u32 = 1;
pub const WRITE_UINT: u32 = 2;

pub const KINDS: [IntKind; 8] = [
    IntKind::I8,
    IntKind::I16,
    IntKind::I32,
    IntKind::I64,
    IntKind::U8,
    IntKind::U16,
    IntKind::U32,
    IntKind::U64,
];

pub fn prim_of(k: IntKind) -> PrimKind {
    match k {
        IntKind::I8 => PrimKind::I8,
        IntKind::I16 => PrimKind::I16,
        IntKind::I32 => PrimKind::I32,
        IntKind::I64 => PrimKind::I64,
        IntKind::U8 => PrimKind::U8,
        IntKind::U16 => PrimKind::U16,
        IntKind::U32 => PrimKind::U32,
        IntKind::U64 => PrimKind::U64,
    }
}

fn mask(w: u32) -> u64 {
    if w == 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// A straight-line `main` under construction.
pub struct Builder {
    pub tys: TyStore,
    decl: DeclFmir,
    strings: Vec<(u32, Vec<u8>)>,
    unit: Option<ValId>,
    /// The one `ConstStr ""` value [`Builder::newline`] reuses (a batched
    /// edge program prints thousands of lines; one value per line would
    /// exhaust the 32 KiB frame).
    empty: Option<ValId>,
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder {
    pub fn new() -> Builder {
        let mut decl = DeclFmir::empty(DeclKeyId(1000), FnSigId(1000));
        decl.blocks = BlockPool::new();
        Builder {
            tys: TyStore::new(),
            decl,
            strings: Vec::new(),
            unit: None,
            empty: None,
        }
    }

    /// Values defined so far (each is one 8-byte frame slot natively).
    pub fn value_count(&self) -> usize {
        self.decl.vals.len()
    }

    pub fn ty(&mut self, k: IntKind) -> TyId {
        self.tys.prim(prim_of(k))
    }

    pub fn bool_ty(&mut self) -> TyId {
        self.tys.prim(PrimKind::Bool)
    }

    fn row(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) -> ValId {
        let inst = self.decl.insts.len() as u32;
        let v = self
            .decl
            .push_val(ValRow::new(ty, false, 0, ValDef::Inst(InstId(inst))));
        self.push(op, a, b, c, ty);
        v
    }

    fn push(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) {
        self.decl.push_inst(
            InstRow {
                op,
                a,
                b,
                c,
                ty,
                site: SiteId(0),
            },
            AliasSeed::None,
        );
    }

    /// `bits` are the raw low-width bits (the interpreter's slot form).
    pub fn const_int(&mut self, bits: u64, k: IntKind) -> ValId {
        let v = bits & mask(k.width());
        let ty = self.ty(k);
        self.row(Op::ConstInt, v as u32, (v >> 32) as u32, NO_OPERAND, ty)
    }

    pub fn const_bool(&mut self, b: bool) -> ValId {
        let ty = self.bool_ty();
        self.row(Op::ConstBool, b as u32, NO_OPERAND, NO_OPERAND, ty)
    }

    pub fn bin(&mut self, op: Op, a: ValId, b: ValId, k: IntKind) -> ValId {
        let ty = self.ty(k);
        self.row(op, a.0, b.0, NO_OPERAND, ty)
    }

    pub fn un(&mut self, op: Op, a: ValId, k: IntKind) -> ValId {
        let ty = self.ty(k);
        self.row(op, a.0, NO_OPERAND, NO_OPERAND, ty)
    }

    pub fn icmp(&mut self, pred: CmpPred, a: ValId, b: ValId) -> ValId {
        let ty = self.bool_ty();
        self.row(Op::Icmp(pred), a.0, b.0, NO_OPERAND, ty)
    }

    pub fn conv(&mut self, op: Op, a: ValId, to: IntKind) -> ValId {
        let ty = self.ty(to);
        self.row(op, a.0, NO_OPERAND, NO_OPERAND, ty)
    }

    /// `let` local `root` := `v` (an `Init` on a scalar root place).
    pub fn init(&mut self, root: u32, v: ValId, ty: TyId) {
        let p = self.decl.places.intern(root, &[], ty);
        self.push(Op::Init, p.0, v.0, NO_OPERAND, TY_UNIT);
    }

    pub fn copy_from(&mut self, root: u32, ty: TyId) -> ValId {
        let p = self.decl.places.intern(root, &[], ty);
        self.row(Op::CopyFrom, p.0, NO_OPERAND, NO_OPERAND, ty)
    }

    fn unit(&mut self) -> ValId {
        if let Some(u) = self.unit {
            return u;
        }
        let u = self.row(Op::ConstUnit, NO_OPERAND, NO_OPERAND, NO_OPERAND, TY_UNIT);
        self.unit = Some(u);
        u
    }

    fn intrinsic(&mut self, sym: u32, args: &[ValId]) {
        let convs = vec![Conv::Let; args.len()];
        let range = self.decl.insts.push_operands(args, &convs);
        let call = self.decl.insts.push_call(CallRow {
            callee: Callee::Intrinsic(Symbol(sym)),
            args: range,
        });
        self.push(Op::Intrinsic, call, NO_OPERAND, NO_OPERAND, TY_UNIT);
    }

    pub fn write_uint(&mut self, v: ValId) {
        let u = self.unit();
        self.intrinsic(WRITE_UINT, &[u, v]);
    }

    pub fn write_line(&mut self, text: &[u8]) {
        let id = self.strings.len() as u32;
        self.strings.push((id, text.to_vec()));
        let u = self.unit();
        let st = self.tys.prim(PrimKind::Str);
        let s = self.row(Op::ConstStr, id, NO_OPERAND, NO_OPERAND, st);
        self.intrinsic(WRITE_LINE, &[u, s]);
    }

    /// `write_line("")` through one shared `ConstStr` value.
    pub fn newline(&mut self) {
        let s = match self.empty {
            Some(s) => s,
            None => {
                let id = self.strings.len() as u32;
                self.strings.push((id, Vec::new()));
                let st = self.tys.prim(PrimKind::Str);
                let s = self.row(Op::ConstStr, id, NO_OPERAND, NO_OPERAND, st);
                self.empty = Some(s);
                s
            }
        };
        let u = self.unit();
        self.intrinsic(WRITE_LINE, &[u, s]);
    }

    fn finish(mut self, term: InstRow) -> Candidate {
        let n = self.decl.insts.len() as u32;
        let mut pool = BlockPool::new();
        pool.push(BlockRow {
            first_inst: 0,
            inst_len: n,
            term,
            scope: ScopeId(0),
        });
        self.decl.blocks = pool;
        self.decl.entry = BlockId(0);
        if self.strings.is_empty() {
            self.strings.push((0, Vec::new()));
        }
        let intrinsics = vec![
            (WRITE_LINE, "stdout_write_line".to_string()),
            (WRITE_UINT, "stdout_write_uint".to_string()),
        ];
        Candidate {
            prog: Program {
                fns: vec![ProgFn {
                    name: "main".into(),
                    decl: self.decl,
                    strings: self.strings,
                    intrinsics,
                }],
                entry: 0,
                config: Config::v0_1(),
                names: Default::default(),
            },
            tys: self.tys,
        }
    }

    pub fn ret(self) -> Candidate {
        self.finish(InstRow {
            op: Op::Ret,
            a: NO_OPERAND,
            b: NO_OPERAND,
            c: NO_OPERAND,
            ty: TY_UNIT,
            site: SiteId(0),
        })
    }

    pub fn trap(self, kind: TrapKind) -> Candidate {
        self.finish(InstRow {
            op: Op::Trap,
            a: kind as u32,
            b: NO_OPERAND,
            c: NO_OPERAND,
            ty: TY_UNIT,
            site: SiteId(0),
        })
    }
}

/// The generator's `interesting()` classes made deterministic: zero, one,
/// all-ones (`-1` / `MAX`), signed `MIN`, signed `MAX`, a small value below
/// 16, a value below 1000, and fixed "random" bit patterns — plus the
/// neighbours of every bound, where every stencil's edge lives.
pub fn interesting_values(k: IntKind) -> Vec<u64> {
    let w = k.width();
    let m = mask(w);
    let min_signed = 1u64 << (w - 1);
    let mut v = vec![
        0,
        1,
        2,
        7,
        15,
        999 & m,
        m,
        m - 1,
        min_signed,
        min_signed + 1,
        m >> 1,
        (m >> 1) - 1,
        0x5555_5555_5555_5555 & m,
        0xDEAD_BEEF_CAFE_F00D & m,
        0x8000_0000_0000_0001 & m,
        (1u64 << (w / 2)) & m,
    ];
    v.sort_unstable();
    v.dedup();
    v
}

/// One edge-table program: an operand type, an op, and (for conversions)
/// the target type.
#[derive(Clone, Copy, Debug)]
pub struct EdgeCase {
    pub k: IntKind,
    pub op: Op,
    pub to: Option<IntKind>,
}

impl EdgeCase {
    pub fn name(&self) -> String {
        match self.to {
            Some(t) => format!("{:?} {:?} -> {:?}", self.k, self.op, t),
            None => format!("{:?} {:?}", self.k, self.op),
        }
    }
}

const MODES: [ArithMode; 3] = [ArithMode::Trap, ArithMode::Wrap, ArithMode::Sat];
const PREDS: [CmpPred; 6] = [
    CmpPred::Eq,
    CmpPred::Ne,
    CmpPred::Lt,
    CmpPred::Le,
    CmpPred::Gt,
    CmpPred::Ge,
];

/// Every (type, op, mode) of M2-0's surface (§10): seven binary ops in three
/// modes, `neg` (Wrap everywhere; Trap/Sat on signed types only — owner
/// Q6), the logic ops, six predicates, three conversions to every type.
pub fn edge_cases() -> Vec<EdgeCase> {
    let mut out = Vec::new();
    for k in KINDS {
        for m in MODES {
            for op in [
                Op::Add(m),
                Op::Sub(m),
                Op::Mul(m),
                Op::Div(m),
                Op::Rem(m),
                Op::Shl(m),
                Op::Shr(m),
            ] {
                out.push(EdgeCase { k, op, to: None });
            }
            if m == ArithMode::Wrap || k.signed() {
                out.push(EdgeCase {
                    k,
                    op: Op::Neg(m),
                    to: None,
                });
            }
        }
        for op in [Op::And, Op::Or, Op::Xor, Op::Not] {
            out.push(EdgeCase { k, op, to: None });
        }
        for p in PREDS {
            out.push(EdgeCase {
                k,
                op: Op::Icmp(p),
                to: None,
            });
        }
        for op in [Op::ConvChecked, Op::ConvWrap, Op::ConvSat] {
            for t in KINDS {
                out.push(EdgeCase { k, op, to: Some(t) });
            }
        }
    }
    out
}

fn binop_name(op: Op) -> Option<(&'static str, ArithMode)> {
    Some(match op {
        Op::Add(m) => ("add", m),
        Op::Sub(m) => ("sub", m),
        Op::Mul(m) => ("mul", m),
        Op::Div(m) => ("div", m),
        Op::Rem(m) => ("rem", m),
        Op::Shl(m) => ("shl", m),
        Op::Shr(m) => ("shr", m),
        _ => return None,
    })
}

/// `arith.rs`'s answer for one input: `Ok(raw result bits)` or the trap.
pub fn oracle(case: &EdgeCase, a: u64, b: u64) -> Result<u64, TrapKind> {
    let k = case.k;
    if let Some((name, mode)) = binop_name(case.op) {
        return arith::int_binop(name, mode, a, b, k);
    }
    match case.op {
        Op::Neg(m) => arith::int_neg(m, a, k),
        Op::And => Ok(a & b),
        Op::Or => Ok(a | b),
        Op::Xor => Ok(a ^ b),
        Op::Not => Ok(k.narrow(u128::from(!a))),
        Op::Icmp(p) => Ok(arith::icmp(a, b, k, p) as u64),
        Op::ConvChecked => arith::conv_checked(a, NumKind::Int(k), NumKind::Int(case.to.unwrap())),
        Op::ConvWrap => Ok(arith::conv_wrap(
            a,
            NumKind::Int(k),
            NumKind::Int(case.to.unwrap()),
        )),
        Op::ConvSat => Ok(arith::conv_sat(
            a,
            NumKind::Int(k),
            NumKind::Int(case.to.unwrap()),
        )),
        other => panic!("not an edge-table op: {other:?}"),
    }
}

fn is_unary(op: Op) -> bool {
    matches!(
        op,
        Op::Neg(_) | Op::Not | Op::ConvChecked | Op::ConvWrap | Op::ConvSat
    )
}

/// The operand pairs of `case`: all pairs of the interesting values (the
/// first alone for a unary op); a shift's count additionally ranges over
/// `width - 1` and `width / 2`, the in-range counts at the edge.
pub fn operand_pairs(case: &EdgeCase) -> Vec<(u64, u64)> {
    let vals = interesting_values(case.k);
    if is_unary(case.op) {
        return vals.iter().map(|&a| (a, 0)).collect();
    }
    let mut bs = vals.clone();
    if matches!(case.op, Op::Shl(_) | Op::Shr(_)) {
        let w = u64::from(case.k.width());
        bs.extend([w - 1, w / 2, w - 2]);
        bs.sort_unstable();
        bs.dedup();
    }
    let mut out = Vec::new();
    for &a in &vals {
        for &b in &bs {
            out.push((a, b));
        }
    }
    out
}

/// The edge program for `case` alone over every pair whose `arith.rs`
/// result is not a trap, the stdout `arith.rs` says it must print (see
/// `append_edge_case`: raw bits, then the canonical 64-bit form, one per
/// line, exactly `stdout_write_uint`'s form), and the line count.
pub fn edge_program(case: &EdgeCase) -> (Candidate, Vec<u8>, usize) {
    let mut b = Builder::new();
    let mut want = Vec::new();
    let n = append_edge_case(&mut b, &mut want, case);
    (b.ret(), want, n)
}

/// The type of `case`'s result: `None` for a `bool` (`icmp`).
pub fn result_kind(case: &EdgeCase) -> Option<IntKind> {
    match case.op {
        Op::Icmp(_) => None,
        Op::ConvChecked | Op::ConvWrap | Op::ConvSat => case.to,
        _ => Some(case.k),
    }
}

/// The 64-bit type a value of `k` widens to without changing its value.
pub fn wide(k: IntKind) -> IntKind {
    if k.signed() {
        IntKind::I64
    } else {
        IntKind::U64
    }
}

/// The canonical 64-bit slot pattern of raw bits `r` of type `k` (design
/// E5: sign-extended for signed types, zero-extended for unsigned ones) —
/// what `wrap_as` to the 64-bit type of the same signedness prints.
pub fn canonical(r: u64, k: IntKind) -> u64 {
    if k.signed() {
        k.as_signed(r) as i64 as u64
    } else {
        r
    }
}

/// Lines one pair of `case` prints: its result, and for an integer result
/// its canonical 64-bit form too.
pub fn lines_per_pair(case: &EdgeCase) -> usize {
    if result_kind(case).is_some() { 2 } else { 1 }
}

/// Builds `case`'s operation on `(x, y)` in `b`.
pub fn build_edge_op(b: &mut Builder, case: &EdgeCase, x: u64, y: u64) -> ValId {
    let va = b.const_int(x, case.k);
    if is_unary(case.op) {
        match case.op {
            Op::ConvChecked | Op::ConvWrap | Op::ConvSat => b.conv(case.op, va, case.to.unwrap()),
            _ => b.un(case.op, va, case.k),
        }
    } else {
        let vb = b.const_int(y, case.k);
        match case.op {
            Op::Icmp(p) => b.icmp(p, va, vb),
            _ => b.bin(case.op, va, vb, case.k),
        }
    }
}

/// Appends `case`'s non-trapping pairs to `b` and the output `arith.rs`
/// says they print to `want`; returns the line count. Each pair prints its
/// result's raw bits and then — for an integer result — the result widened
/// with `wrap_as` to the 64-bit type of its signedness, which is the raw
/// 64-bit SLOT natively: a stencil whose low bits are right but whose
/// upper bits are not the canonical extension (E5) is caught here, not
/// only once a later operation consumes the slot.
fn append_edge_case(b: &mut Builder, want: &mut Vec<u8>, case: &EdgeCase) -> usize {
    let mut n = 0;
    for (x, y) in operand_pairs(case) {
        let Ok(r) = oracle(case, x, y) else { continue };
        let res = build_edge_op(b, case, x, y);
        b.write_uint(res);
        b.newline();
        want.extend_from_slice(format!("{r}\n").as_bytes());
        n += 1;
        if let Some(k) = result_kind(case) {
            let w = b.conv(Op::ConvWrap, res, wide(k));
            b.write_uint(w);
            b.newline();
            want.extend_from_slice(format!("{}\n", canonical(r, k)).as_bytes());
            n += 1;
        }
    }
    n
}

/// Values one batched edge program may define: the frame holds 4,096
/// 8-byte slots (`fors_codegen_dev::frame::MAX_FRAME`); the rest is
/// headroom for the shared unit and `""` values.
pub const BATCH_VALUE_BUDGET: usize = 4_000;
/// A `conv_checked` across a sign change reaches its trap site with `tbnz`
/// (+-32 KiB), so a batch holding checked conversions stays well under
/// that in code bytes: ~26 words per pair with the canonical line, 250
/// pairs ~ 26 KiB.
pub const CHECKED_CONV_PAIR_BUDGET: usize = 250;

/// Several edge cases in one program (one native exec costs ~0.35 s of
/// serialised first-exec checking on macOS, so the ~450 cases run as a
/// few dozen programs rather than one each).
pub struct EdgeBatch {
    /// The cases in print order, each with the number of lines it prints.
    pub cases: Vec<(EdgeCase, usize)>,
    pub candidate: Candidate,
    /// The stdout `arith.rs` says the batch prints.
    pub want: Vec<u8>,
}

impl EdgeBatch {
    /// `(case, pair, canonical-line?)` that printed line `k` (0-based), if
    /// any: the pair is the non-trapping pair of the case the line falls
    /// in, and the flag says whether the line was the pair's canonical
    /// 64-bit form rather than its raw result.
    pub fn locate(&self, k: usize) -> Option<(EdgeCase, Option<(u64, u64)>, bool)> {
        let mut base = 0;
        for &(case, n) in &self.cases {
            if k < base + n {
                let per = lines_per_pair(&case);
                let pair = operand_pairs(&case)
                    .into_iter()
                    .filter(|&(x, y)| oracle(&case, x, y).is_ok())
                    .nth((k - base) / per);
                return Some((case, pair, (k - base) % per == 1));
            }
            base += n;
        }
        None
    }
}

/// Every edge case, greedily packed into programs under the budgets above
/// (checked conversions in their own batches). Deterministic.
pub fn edge_batches() -> Vec<EdgeBatch> {
    struct Open {
        b: Builder,
        want: Vec<u8>,
        cases: Vec<(EdgeCase, usize)>,
        pairs: usize,
    }
    fn fresh() -> Open {
        Open {
            b: Builder::new(),
            want: Vec::new(),
            cases: Vec::new(),
            pairs: 0,
        }
    }
    let mut out = Vec::new();
    let mut flush = |o: Open| {
        if !o.cases.is_empty() {
            assert!(o.b.value_count() <= 4_096, "batch overflows the frame");
            out.push(EdgeBatch {
                cases: o.cases,
                candidate: o.b.ret(),
                want: o.want,
            });
        }
    };
    let mut plain = fresh();
    let mut checked = fresh();
    for case in edge_cases() {
        let live = operand_pairs(&case)
            .into_iter()
            .filter(|&(x, y)| oracle(&case, x, y).is_ok())
            .count();
        if case.op == Op::ConvChecked {
            if checked.pairs + live > CHECKED_CONV_PAIR_BUDGET {
                flush(std::mem::replace(&mut checked, fresh()));
            }
            let n = append_edge_case(&mut checked.b, &mut checked.want, &case);
            checked.cases.push((case, n));
            checked.pairs += n;
        } else {
            // Operands, the result, and the widened copy of an integer result.
            let per_pair = if is_unary(case.op) { 2 } else { 3 } + (lines_per_pair(&case) - 1);
            if plain.b.value_count() + live * per_pair + 2 > BATCH_VALUE_BUDGET {
                flush(std::mem::replace(&mut plain, fresh()));
            }
            let n = append_edge_case(&mut plain.b, &mut plain.want, &case);
            plain.cases.push((case, n));
            plain.pairs += n;
        }
    }
    flush(plain);
    flush(checked);
    out
}

/// One program that executes exactly one trapping instance of `case` (the
/// first trapping pair), after printing a marker line — `None` when no
/// pair traps.
pub fn trap_program(case: &EdgeCase) -> Option<(Candidate, TrapKind)> {
    for (x, y) in operand_pairs(case) {
        let Err(kind) = oracle(case, x, y) else {
            continue;
        };
        let mut b = Builder::new();
        b.write_line(b"before");
        let va = b.const_int(x, case.k);
        let res = if is_unary(case.op) {
            match case.op {
                Op::ConvChecked | Op::ConvWrap | Op::ConvSat => {
                    b.conv(case.op, va, case.to.unwrap())
                }
                _ => b.un(case.op, va, case.k),
            }
        } else {
            let vb = b.const_int(y, case.k);
            b.bin(case.op, va, vb, case.k)
        };
        b.write_uint(res);
        b.write_line(b"after");
        return Some((b.ret(), kind));
    }
    None
}
