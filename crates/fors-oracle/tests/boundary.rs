//! F10 verification: ten FMIR programs built BY HAND at the exact boundary
//! of each guard `generate.rs` relies on for "UB-free and trap-free by
//! construction", with every constant pinned to the extreme the generator's
//! `interesting()` can draw (all-ones, `MIN`, `MAX`, 0, 1). Each program is
//! the shape the generator emits (the same mask, `| 1` and `| (m + 1)`
//! idioms, the same counted loops, the same parameter reads) and runs
//! through the differential runner's own [`check`]: the verdict must be
//! `ok` and the printed values must be the arithmetic the modes promise.
//! A trap or a `ub:` here means a guard is weaker than its comment.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::{PrimKind, TY_UNIT, TyId, TyStore};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::{BlockPool, BlockRow};
use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{BlockId, InstId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow};
use fors_fmir::op::{ArithMode, CmpPred, NO_OPERAND, Op};
use fors_fmir::value::{ValDef, ValRow};
use fors_index::interner::Symbol;
use fors_interp::{Config, ProgFn, Program};
use fors_oracle::diff::{Verdict, check};
use fors_oracle::generate::Generated;

const WRITE_LINE: u32 = 1;
const WRITE_UINT: u32 = 2;
const EMPTY_STR: u32 = 0;

#[derive(Clone, Copy)]
struct T {
    id: TyId,
    w: u32,
}

impl T {
    fn mask(self) -> u64 {
        if self.w == 64 {
            u64::MAX
        } else {
            (1u64 << self.w) - 1
        }
    }
    fn min_signed(self) -> u64 {
        1u64 << (self.w - 1)
    }
}

struct Tys {
    i64: T,
    u64: T,
    i32: T,
    u32: T,
    i16: T,
    u16: T,
    u8: T,
    bool_ty: TyId,
    str_ty: TyId,
}

impl Tys {
    fn new(tys: &mut TyStore) -> Tys {
        let mut t = |p, w| T { id: tys.prim(p), w };
        let i64 = t(PrimKind::I64, 64);
        let u64 = t(PrimKind::U64, 64);
        let i32 = t(PrimKind::I32, 32);
        let u32 = t(PrimKind::U32, 32);
        let i16 = t(PrimKind::I16, 16);
        let u16 = t(PrimKind::U16, 16);
        let u8 = t(PrimKind::U8, 8);
        Tys {
            i64,
            u64,
            i32,
            u32,
            i16,
            u16,
            u8,
            bool_ty: tys.prim(PrimKind::Bool),
            str_ty: tys.prim(PrimKind::Str),
        }
    }
}

struct Staged {
    first: u32,
    len: u32,
    term: Option<InstRow>,
}

/// The generator's own block-staging builder, reduced to what the ten
/// programs need.
struct B {
    decl: DeclFmir,
    insts: Vec<InstRow>,
    blocks: Vec<Staged>,
    open: usize,
    params: Vec<ValId>,
    str_ty: TyId,
}

impl B {
    fn new(key: u32, params: &[T], str_ty: TyId) -> B {
        let mut decl = DeclFmir::empty(DeclKeyId(key), FnSigId(key));
        decl.blocks = BlockPool::new();
        let mut vals = Vec::new();
        for (i, p) in params.iter().enumerate() {
            vals.push(decl.push_val(ValRow::new(p.id, false, 0, ValDef::Param(i as u16))));
        }
        B {
            decl,
            insts: Vec::new(),
            blocks: vec![Staged {
                first: 0,
                len: 0,
                term: None,
            }],
            open: 0,
            params: vals,
            str_ty,
        }
    }

    fn emit(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) -> ValId {
        let inst = self.insts.len() as u32;
        let v = self
            .decl
            .push_val(ValRow::new(ty, false, 0, ValDef::Inst(InstId(inst))));
        self.insts.push(InstRow {
            op,
            a,
            b,
            c,
            ty,
            site: SiteId(0),
        });
        self.blocks[self.open].len += 1;
        v
    }

    fn emit_void(&mut self, op: Op, a: u32, b: u32) {
        self.insts.push(InstRow {
            op,
            a,
            b,
            c: NO_OPERAND,
            ty: TY_UNIT,
            site: SiteId(0),
        });
        self.blocks[self.open].len += 1;
    }

    fn k(&mut self, bits: u64, t: T) -> ValId {
        let v = bits & t.mask();
        self.emit(Op::ConstInt, v as u32, (v >> 32) as u32, NO_OPERAND, t.id)
    }

    fn bin(&mut self, op: Op, a: ValId, b: ValId, t: T) -> ValId {
        self.emit(op, a.0, b.0, NO_OPERAND, t.id)
    }

    fn un(&mut self, op: Op, a: ValId, t: T) -> ValId {
        self.emit(op, a.0, NO_OPERAND, NO_OPERAND, t.id)
    }

    fn masked(&mut self, v: ValId, m: u64, t: T) -> ValId {
        let k = self.k(m, t);
        self.bin(Op::And, v, k, t)
    }

    fn place(&mut self, root: u32, t: T) -> u32 {
        self.decl.places.intern(root, &[], t.id).0
    }

    fn init(&mut self, root: u32, t: T, v: ValId) {
        let p = self.place(root, t);
        self.emit_void(Op::Init, p, v.0);
    }

    fn read(&mut self, root: u32, t: T) -> ValId {
        let p = self.place(root, t);
        self.emit(Op::CopyFrom, p, NO_OPERAND, NO_OPERAND, t.id)
    }

    fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(Staged {
            first: 0,
            len: 0,
            term: None,
        });
        id
    }

    fn end_and_open(&mut self, op: Op, a: u32, b: u32, c: u32, next: Option<BlockId>) {
        self.blocks[self.open].term = Some(InstRow {
            op,
            a,
            b,
            c,
            ty: TY_UNIT,
            site: SiteId(0),
        });
        if let Some(n) = next {
            self.open = n.index();
            self.blocks[self.open].first = self.insts.len() as u32;
        }
    }

    fn intrinsic(&mut self, sym: u32, args: &[ValId]) {
        let convs = vec![Conv::Let; args.len()];
        let range = self.decl.insts.push_operands(args, &convs);
        let call = self.decl.insts.push_call(CallRow {
            callee: Callee::Intrinsic(Symbol(sym)),
            args: range,
        });
        self.emit_void(Op::Intrinsic, call, NO_OPERAND);
    }

    /// `write_uint(v)` then `write_line("")`: one line per printed value,
    /// the slot's raw low-width bits as an unsigned decimal.
    fn print(&mut self, v: ValId) {
        let unit = self.emit(Op::ConstUnit, NO_OPERAND, NO_OPERAND, NO_OPERAND, TY_UNIT);
        self.intrinsic(WRITE_UINT, &[unit, v]);
        let s = self.emit(Op::ConstStr, EMPTY_STR, NO_OPERAND, NO_OPERAND, self.str_ty);
        self.intrinsic(WRITE_LINE, &[unit, s]);
    }

    fn call(&mut self, key: u32, args: &[ValId], ret: T) -> ValId {
        let convs = vec![Conv::Let; args.len()];
        let range = self.decl.insts.push_operands(args, &convs);
        let call = self.decl.insts.push_call(CallRow {
            callee: Callee::Direct(DeclKeyId(key)),
            args: range,
        });
        self.emit(Op::CallDirect, call, NO_OPERAND, NO_OPERAND, ret.id)
    }

    fn ret(mut self, v: Option<ValId>) -> DeclFmir {
        self.end_and_open(
            Op::Ret,
            v.map_or(NO_OPERAND, |v| v.0),
            NO_OPERAND,
            NO_OPERAND,
            None,
        );
        for row in std::mem::take(&mut self.insts) {
            self.decl.push_inst(row, AliasSeed::None);
        }
        let mut pool = BlockPool::new();
        for b in &self.blocks {
            pool.push(BlockRow {
                first_inst: b.first,
                inst_len: b.len,
                term: b.term.expect("terminated"),
                scope: ScopeId(0),
            });
        }
        self.decl.blocks = pool;
        self.decl.entry = BlockId(0);
        self.decl
    }
}

fn program(fns: Vec<(String, DeclFmir)>, tys: TyStore) -> Generated {
    let intrinsics = vec![
        (WRITE_LINE, "stdout_write_line".to_string()),
        (WRITE_UINT, "stdout_write_uint".to_string()),
    ];
    let strings = vec![(EMPTY_STR, Vec::new())];
    Generated {
        seed: 0,
        prog: Program {
            fns: fns
                .into_iter()
                .map(|(name, decl)| ProgFn {
                    name,
                    decl,
                    strings: strings.clone(),
                    intrinsics: intrinsics.clone(),
                })
                .collect(),
            entry: 0,
            config: Config::v0_1(),
            names: Default::default(),
        },
        tys,
    }
}

/// Runs one program through the differential runner and returns its stdout.
fn run_ok(name: &str, g: &Generated) -> String {
    let (v, steps) = check(g);
    assert_eq!(v, Verdict::Ok, "{name}: verdict {}", v.class());
    assert!(steps > 0, "{name}: ran");
    let c = fors_oracle::Candidate {
        prog: g.prog.clone(),
        tys: g.tys.clone(),
    };
    match fors_oracle::run_candidate(&c) {
        fors_oracle::RunResult::Record(r) => String::from_utf8(r.stdout).expect("ascii"),
        other => panic!("{name}: {other:?}"),
    }
}

fn single(tys: TyStore, main: DeclFmir) -> Generated {
    program(vec![("main".to_string(), main)], tys)
}

/// 1. Trapping add and sub under the add mask, both operands all-ones (the
///    largest masked value) and the minuend's `| (m + 1)` with a zero base.
#[test]
fn trap_add_and_sub_at_the_mask_extremes() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    for ty in [t.i16, t.u8] {
        let m = 0x3F; // `add_mask()` for widths <= 16
        let ones = b.k(u64::MAX, ty);
        let x = b.masked(ones, m, ty);
        let y = b.masked(ones, m, ty);
        let s = b.bin(Op::Add(ArithMode::Trap), x, y, ty);
        b.print(s); // 126
        let hi = b.k(m + 1, ty);
        let minuend = b.bin(Op::Or, x, hi, ty);
        let d = b.bin(Op::Sub(ArithMode::Trap), minuend, y, ty);
        b.print(d); // 0x7F - 0x3F = 64
    }
    let zero = b.k(0, t.i16);
    let x = b.masked(zero, 0x3F, t.i16);
    let hi = b.k(0x40, t.i16);
    let minuend = b.bin(Op::Or, x, hi, t.i16);
    let ones = b.k(u64::MAX, t.i16);
    let y = b.masked(ones, 0x3F, t.i16);
    let d = b.bin(Op::Sub(ArithMode::Trap), minuend, y, t.i16);
    b.print(d); // 0x40 - 0x3F = 1
    // The 32/64-bit mask: 0x3FFF + 0x3FFF on i32 and u64.
    for ty in [t.i32, t.u64] {
        let ones = b.k(u64::MAX, ty);
        let x = b.masked(ones, 0x3FFF, ty);
        let y = b.masked(ones, 0x3FFF, ty);
        let s = b.bin(Op::Add(ArithMode::Trap), x, y, ty);
        b.print(s); // 32766
    }
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("trap-add-sub", &g),
        "126\n64\n126\n64\n1\n32766\n32766\n"
    );
}

/// 2. Trapping mul at each width's mask maximum.
#[test]
fn trap_mul_at_the_mask_maximum_of_every_width() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    for (ty, m) in [
        (t.u8, 0x7),
        (t.i16, 0x7F),
        (t.u16, 0x7F),
        (t.i32, 0x3FFF),
        (t.i64, 0x3FFF),
    ] {
        let ones = b.k(u64::MAX, ty);
        let x = b.masked(ones, m, ty);
        let y = b.masked(ones, m, ty);
        let p = b.bin(Op::Mul(ArithMode::Trap), x, y, ty);
        b.print(p);
    }
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("trap-mul", &g),
        "49\n16129\n16129\n268402689\n268402689\n"
    );
}

/// 3. Trapping div and rem: dividend masked to `mask >> 1` (so `MAX`), the
///    divisor all-ones `| 1` (so `-1` signed, `MAX` unsigned) and `0 | 1`.
#[test]
fn trap_div_and_rem_with_max_over_minus_one() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    for (ty, op) in [
        (t.i16, Op::Div(ArithMode::Trap)),
        (t.i16, Op::Rem(ArithMode::Trap)),
        (t.u16, Op::Div(ArithMode::Trap)),
        (t.u16, Op::Rem(ArithMode::Trap)),
        (t.i64, Op::Div(ArithMode::Trap)),
    ] {
        let ones = b.k(u64::MAX, ty);
        let one = b.k(1, ty);
        let d = b.bin(Op::Or, ones, one, ty);
        let x = b.masked(ones, ty.mask() >> 1, ty);
        let r = b.bin(op, x, d, ty);
        b.print(r);
    }
    let zero = b.k(0, t.i16);
    let one = b.k(1, t.i16);
    let d = b.bin(Op::Or, zero, one, t.i16);
    let ones = b.k(u64::MAX, t.i16);
    let x = b.masked(ones, 0x7FFF, t.i16);
    let r = b.bin(Op::Div(ArithMode::Trap), x, d, t.i16);
    b.print(r);
    let g = single(store, b.ret(None));
    // 32767 / -1 = -32767 (0x8001); 32767 % -1 = 0; 32767 / 65535 = 0;
    // 32767 % 65535 = 32767; i64 MAX / -1 = -MAX; 32767 / 1.
    assert_eq!(
        run_ok("trap-div-rem", &g),
        "32769\n0\n0\n32767\n9223372036854775809\n32767\n"
    );
}

/// 4. Wrapping div and rem meeting `MIN / -1` (the one case the generator's
///    comment says "wraps by definition") at 16 and 64 bits.
#[test]
fn wrap_div_and_rem_of_min_by_minus_one() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    for ty in [t.i16, t.i64] {
        let min = b.k(ty.min_signed(), ty);
        let m1 = b.k(u64::MAX - 1, ty); // all-ones but the low bit...
        let one = b.k(1, ty);
        let d = b.bin(Op::Or, m1, one, ty); // ...`| 1`: -1
        let q = b.bin(Op::Div(ArithMode::Wrap), min, d, ty);
        b.print(q);
        let r = b.bin(Op::Rem(ArithMode::Wrap), min, d, ty);
        b.print(r);
    }
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("wrap-div-rem", &g),
        "32768\n0\n9223372036854775808\n0\n"
    );
}

/// 5. Saturating div of `MIN / -1` saturates to `MAX`; unsigned sat div is
///    plain division.
#[test]
fn sat_div_of_min_by_minus_one_is_max() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    for ty in [t.i16, t.i32, t.i64] {
        let min = b.k(ty.min_signed(), ty);
        let ones = b.k(u64::MAX, ty);
        let one = b.k(1, ty);
        let d = b.bin(Op::Or, ones, one, ty);
        let q = b.bin(Op::Div(ArithMode::Sat), min, d, ty);
        b.print(q);
    }
    let ones = b.k(u64::MAX, t.u8);
    let zero = b.k(0, t.u8);
    let one = b.k(1, t.u8);
    let d = b.bin(Op::Or, zero, one, t.u8);
    let q = b.bin(Op::Div(ArithMode::Sat), ones, d, t.u8);
    b.print(q);
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("sat-div", &g),
        "32767\n2147483647\n9223372036854775807\n255\n"
    );
}

/// 6. Every shift mode with the count masked to `width - 1` from an
///    all-ones count, on `MIN`, all-ones and 1.
#[test]
fn shifts_by_width_minus_one() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    let count = |b: &mut B, ty: T| {
        let ones = b.k(u64::MAX, ty);
        b.masked(ones, u64::from(ty.w - 1), ty)
    };
    let n = count(&mut b, t.i32);
    let min = b.k(t.i32.min_signed(), t.i32);
    let r = b.bin(Op::Shr(ArithMode::Trap), min, n, t.i32);
    b.print(r); // arithmetic: -1
    let n = count(&mut b, t.u64);
    let ones = b.k(u64::MAX, t.u64);
    let r = b.bin(Op::Shl(ArithMode::Wrap), ones, n, t.u64);
    b.print(r); // 1 << 63
    let n = count(&mut b, t.i16);
    let ones = b.k(u64::MAX, t.i16);
    let r = b.bin(Op::Shl(ArithMode::Sat), ones, n, t.i16);
    b.print(r); // -1 << 15 = MIN, no clamp
    let one = b.k(1, t.i16);
    let r = b.bin(Op::Shl(ArithMode::Sat), one, n, t.i16);
    b.print(r); // 1 << 15 clamps to MAX
    let n = count(&mut b, t.u8);
    let ones = b.k(u64::MAX, t.u8);
    let r = b.bin(Op::Shl(ArithMode::Sat), ones, n, t.u8);
    b.print(r); // clamps to 255
    let r = b.bin(Op::Shr(ArithMode::Wrap), ones, n, t.u8);
    b.print(r); // logical: 1
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("shifts", &g),
        "4294967295\n9223372036854775808\n32768\n32767\n255\n1\n"
    );
}

/// 7. `conv_checked` from a `& 0x7F`-masked source at all-ones and `MIN`,
///    and the total conversions at their extremes.
#[test]
fn conversions_at_the_extremes() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    let conv = |b: &mut B, op: Op, v: ValId, to: T| b.un(op, v, to);
    let ones = b.k(u64::MAX, t.i64);
    let small = b.masked(ones, 0x7F, t.i64);
    let r = conv(&mut b, Op::ConvChecked, small, t.u8);
    b.print(r); // 127
    let ones = b.k(u64::MAX, t.u64);
    let small = b.masked(ones, 0x7F, t.u64);
    let r = conv(&mut b, Op::ConvChecked, small, t.i16);
    b.print(r); // 127
    let min = b.k(t.i16.min_signed(), t.i16);
    let small = b.masked(min, 0x7F, t.i16);
    let r = conv(&mut b, Op::ConvChecked, small, t.u8);
    b.print(r); // 0
    let m1 = b.k(u64::MAX, t.i16);
    let r = conv(&mut b, Op::ConvWrap, m1, t.u8);
    b.print(r); // 255
    let r = conv(&mut b, Op::ConvSat, m1, t.u8);
    b.print(r); // 0
    let umax = b.k(u64::MAX, t.u64);
    let r = conv(&mut b, Op::ConvSat, umax, t.i16);
    b.print(r); // 32767
    let r = conv(&mut b, Op::ConvWrap, umax, t.i32);
    b.print(r); // 0xFFFF_FFFF
    let min = b.k(t.i64.min_signed(), t.i64);
    let r = conv(&mut b, Op::ConvSat, min, t.u8);
    b.print(r); // 0
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("conversions", &g),
        "127\n127\n0\n255\n0\n32767\n4294967295\n0\n"
    );
}

/// 8. `neg` in wrap and sat modes on `MIN` and on an unsigned 1, and `not`
///    on 0 and `MIN` (the F10 narrowing fix).
#[test]
fn neg_and_not_at_min_and_zero() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let mut b = B::new(1000, &[], t.str_ty);
    let min = b.k(t.i32.min_signed(), t.i32);
    let r = b.un(Op::Neg(ArithMode::Wrap), min, t.i32);
    b.print(r); // MIN
    let r = b.un(Op::Neg(ArithMode::Sat), min, t.i32);
    b.print(r); // MAX
    let zero = b.k(0, t.u8);
    let r = b.un(Op::Not, zero, t.u8);
    b.print(r); // 255
    let min = b.k(t.i16.min_signed(), t.i16);
    let r = b.un(Op::Not, min, t.i16);
    b.print(r); // 0x7FFF
    let one = b.k(1, t.u8);
    let r = b.un(Op::Neg(ArithMode::Wrap), one, t.u8);
    b.print(r); // 255
    // (`neg` of an UNSIGNED operand in `sat` mode is F1 `arith.rs`'s
    // `sat_neg`, which delegates to `wrap_neg` and gives 255 too; the
    // generator emits it, it is total, and the spec has no sentence on it.)
    let g = single(store, b.ret(None));
    assert_eq!(
        run_ok("neg-not", &g),
        "2147483648\n2147483647\n255\n32767\n255\n"
    );
}

/// 9. Counted loops exactly as the generator stages them: a 5-trip loop,
///    a 5x5 nest whose inner counter is read after the inner loop exits,
///    and a 0-trip loop whose body never runs; every counter advances by a
///    TRAPPING add.
#[test]
fn counted_loops_at_five_trips_and_zero_trips() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    let u = t.u32;
    let mut b = B::new(1000, &[], t.str_ty);
    // Locals: 0 = accumulator, 1/2/3 = counters, all initialised here.
    let zero = b.k(0, u);
    b.init(0, u, zero);
    b.init(1, u, zero);
    b.init(2, u, zero);
    b.init(3, u, zero);
    // Loop A: 5 trips over counter 1, accumulating into 0.
    let loop_over = |b: &mut B, ctr: u32, trips: u64, body: &mut dyn FnMut(&mut B)| {
        let head = b.new_block();
        let body_b = b.new_block();
        let exit = b.new_block();
        b.end_and_open(Op::Br, head.0, NO_OPERAND, NO_OPERAND, Some(head));
        let i = b.read(ctr, u);
        let n = b.k(trips, u);
        let go = b.emit(Op::Icmp(CmpPred::Lt), i.0, n.0, NO_OPERAND, t.bool_ty);
        b.end_and_open(Op::CondBr, go.0, body_b.0, exit.0, Some(body_b));
        body(b);
        let i = b.read(ctr, u);
        let one = b.k(1, u);
        let next = b.bin(Op::Add(ArithMode::Trap), i, one, u);
        b.init(ctr, u, next);
        b.end_and_open(Op::Br, head.0, NO_OPERAND, NO_OPERAND, Some(exit));
    };
    loop_over(&mut b, 1, 5, &mut |_| {});
    let r = b.read(1, u);
    b.print(r); // 5
    // Loop B: 5 x 5, the inner counter re-initialised per outer trip (as
    // the generator does: the counter is a fresh local of the body block).
    loop_over(&mut b, 2, 5, &mut |b| {
        let zero = b.k(0, u);
        b.init(3, u, zero);
        loop_over(b, 3, 5, &mut |b| {
            let acc = b.read(0, u);
            let one = b.k(1, u);
            let next = b.bin(Op::Add(ArithMode::Trap), acc, one, u);
            b.init(0, u, next);
        });
        // The inner counter is in scope after its loop (initialised in
        // this very block).
        let inner = b.read(3, u);
        let acc = b.read(0, u);
        let next = b.bin(Op::Add(ArithMode::Wrap), acc, inner, u);
        b.init(0, u, next);
    });
    let r = b.read(0, u);
    b.print(r); // 25 + 5 * 5 = 50
    // Loop C: 0 trips.
    let zero = b.k(0, u);
    b.init(1, u, zero);
    loop_over(&mut b, 1, 0, &mut |b| {
        let big = b.k(u64::MAX, u);
        b.init(0, u, big);
    });
    let r = b.read(1, u);
    b.print(r); // 0
    let r = b.read(0, u);
    b.print(r); // still 50
    let g = single(store, b.ret(None));
    assert_eq!(run_ok("loops", &g), "5\n50\n0\n50\n");
}

/// 10. A helper with parameters: the parameter VALUE read directly in the
///     entry block, the parameter PLACE read after a branch (the
///     generator's two parameter paths), at the all-ones and `MAX`
///     arguments, with the result folded by a wrapping add.
#[test]
fn helper_parameters_read_as_values_and_as_places() {
    let mut store = TyStore::new();
    let t = Tys::new(&mut store);
    // h0(a: i16, b: u8) -> i16 { local2 = a; br; local2 + (b as i16) }
    let mut h = B::new(1001, &[t.i16, t.u8], t.str_ty);
    let a = h.params[0];
    h.init(2, t.i16, a);
    let next = h.new_block();
    h.end_and_open(Op::Br, next.0, NO_OPERAND, NO_OPERAND, Some(next));
    let pb = h.read(1, t.u8);
    let wb = h.un(Op::ConvWrap, pb, t.i16);
    let x = h.read(2, t.i16);
    let sum = h.bin(Op::Add(ArithMode::Wrap), x, wb, t.i16);
    let h0 = h.ret(Some(sum));
    let mut b = B::new(1000, &[], t.str_ty);
    let m1 = b.k(u64::MAX, t.i16);
    let c200 = b.k(200, t.u8);
    let r = b.call(1001, &[m1, c200], t.i16);
    b.print(r); // -1 + 200 = 199
    let max = b.k(0x7FFF, t.i16);
    let one = b.k(1, t.u8);
    let r = b.call(1001, &[max, one], t.i16);
    b.print(r); // wraps to MIN
    let ones = b.k(u64::MAX, t.u8);
    let r = b.call(1001, &[max, ones], t.i16);
    b.print(r); // 32767 + 255 = 33022 wraps to -32514 (0x80FE)
    let g = program(
        vec![("main".to_string(), b.ret(None)), ("h0".to_string(), h0)],
        store,
    );
    assert_eq!(run_ok("helper-params", &g), "199\n32768\n33022\n");
}
