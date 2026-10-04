//! The FMIR-level typed random program generator
//! (`compiler-architecture.md` §8: "an IR-level typed random program
//! generator (bounded loops, UB-free by construction, checksum output)").
//!
//! [`generate`] is a pure function of its seed: the same seed yields the
//! same [`Generated`] (FMIR bytes, strings, intrinsic table), so any program
//! a run reports is reproducible from the seed alone.
//!
//! **UB-free AND trap-free by construction.** Every rule below is a
//! property of the emitted code, not of the values it happens to meet:
//!
//! - a value is used only in the block that defines it (or is a parameter,
//!   defined before the entry block); state crosses blocks only through
//!   LOCAL places, and every local is initialised in the entry block before
//!   any branch, so no read is ever uninitialised;
//! - wrapping and saturating arithmetic (`add`/`sub`/`mul`/`neg` in the
//!   `wrap`/`sat` modes) never traps;
//! - a TRAPPING `add`/`sub`/`mul` only ever sees masked operands
//!   (`x & m` with `m` small enough that the result fits the type; a `sub`'s
//!   minuend is `(x & m) | (m + 1)`, so it is always the larger);
//! - every `div`/`rem` divisor is `x | 1` (never zero); a trapping
//!   `div`/`rem`'s dividend is masked non-negative, so `MIN / -1` cannot
//!   occur; a `wrap` one may meet `MIN / -1`, which wraps by definition;
//! - every shift count is `x & (width - 1)`;
//! - a `conv_checked` source is masked to `0..=127`, which every integer
//!   type represents; `conv_wrap`/`conv_sat` are total;
//! - loops are counted: a fresh `u32` counter, `0 ..< n` with `n <= 5`,
//!   incremented by one, nested at most two deep; helper functions call
//!   only lower-numbered helpers, so there is no recursion;
//! - the only effect is `Stdout` (`write_uint` of a `u64` checksum and
//!   `write_line("")`): `main` folds every statement's value into the
//!   checksum with a wrapping multiply-xor and prints it at the end (and at
//!   up to two points before).
//!
//! So a generated program can only `ret`: a trap, a `ub:` report or an
//! interpreter error from one is a generator bug or an interpreter bug, and
//! the differential runner ([`crate::diff`]) triages it as such.

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

use crate::rng::Rng;

/// `write_line`'s intrinsic symbol in every generated function.
const WRITE_LINE: u32 = 1;
/// `write_uint`'s.
const WRITE_UINT: u32 = 2;
/// The one string constant: the empty line `write_line("")` ends a
/// checksum with.
const EMPTY_STR: u32 = 0;
/// `main`'s declaration key; helper `i` is `HELPER_BASE + i`.
const MAIN_KEY: u32 = 1000;
const HELPER_BASE: u32 = 1001;

/// The integer types the generator draws from.
const INT_PRIMS: [PrimKind; 7] = [
    PrimKind::I64,
    PrimKind::U64,
    PrimKind::I32,
    PrimKind::U32,
    PrimKind::I16,
    PrimKind::U16,
    PrimKind::U8,
];

/// The checksum's multiplier (FNV-1a's 64-bit prime).
const MIX_MUL: u64 = 0x0000_0100_0000_01b3;

/// Op families a [`Profile`] can switch off (design
/// `docs/design/m2-dev-backend.md` §5 "`Profile`").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpSet(u32);

impl OpSet {
    /// `neg` in `sat` mode on an UNSIGNED type: the interpreter wraps it
    /// (`arith.rs::sat_neg` delegates to `wrap_neg`); owner Q6 is open, so
    /// the dev backend refuses it by name and the native profile leaves it
    /// out.
    pub const NEG_SAT_UNSIGNED: u32 = 1 << 0;
    pub const ALL: OpSet = OpSet(Self::NEG_SAT_UNSIGNED);

    pub const fn has(self, bits: u32) -> bool {
        self.0 & bits == bits
    }

    pub const fn without(self, bits: u32) -> OpSet {
        OpSet(self.0 & !bits)
    }
}

/// The generator's switches. [`Profile::FULL`] IS [`generate`]: with it,
/// [`generate_with`] draws exactly the random stream `generate` always drew
/// (`generate_default_profile_is_unchanged` pins the bytes of seeds
/// `0..1000` to the pre-`Profile` generator).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Profile {
    /// `if` statements (`CondBr` + join).
    pub branches: bool,
    /// Bounded counted loops.
    pub loops: bool,
    /// Helper functions and `CallDirect`.
    pub helpers: bool,
    /// Aggregate/memory shapes. The generator has none yet (M2-4 adds
    /// them); both settings generate the same programs today.
    pub aggregates: bool,
    /// Float shapes. None yet (M2-6); both settings agree today.
    pub floats: bool,
    pub ops: OpSet,
}

impl Profile {
    /// Today's generator, unchanged.
    pub const FULL: Profile = Profile {
        branches: true,
        loops: true,
        helpers: true,
        aggregates: false,
        floats: false,
        ops: OpSet::ALL,
    };

    /// M2-0's native surface: one function `main`, one block — no `if`, no
    /// loops, no helpers; everything else as [`Profile::FULL`] except
    /// unsigned `sat` `neg` (owner Q6).
    pub const STRAIGHT_LINE: Profile = Profile {
        branches: false,
        loops: false,
        helpers: false,
        aggregates: false,
        floats: false,
        ops: OpSet::ALL.without(OpSet::NEG_SAT_UNSIGNED),
    };
}

/// A generated program and the type store its ids point into.
pub struct Generated {
    pub seed: u64,
    pub prog: Program,
    pub tys: TyStore,
}

impl Generated {
    /// Instructions (rows plus terminators) over every function.
    pub fn instruction_count(&self) -> usize {
        self.prog
            .fns
            .iter()
            .map(|f| f.decl.insts.len() + f.decl.blocks.len())
            .sum()
    }
}

#[derive(Clone, Copy)]
struct IntTy {
    id: TyId,
    width: u32,
    signed: bool,
}

impl IntTy {
    /// All-ones over the width, as canonical slot bits.
    fn mask(self) -> u64 {
        if self.width == 64 {
            u64::MAX
        } else {
            (1u64 << self.width) - 1
        }
    }
    /// The operand mask under which a trapping add/sub of two masked
    /// values cannot overflow (`2m + 1` fits the positive range).
    fn add_mask(self) -> u64 {
        if self.width <= 16 { 0x3F } else { 0x3FFF }
    }
    /// The operand mask under which a trapping mul cannot overflow.
    fn mul_mask(self) -> u64 {
        match self.width {
            8 => 0x7,
            16 => 0x7F,
            _ => 0x3FFF,
        }
    }
}

struct Types {
    ints: Vec<IntTy>,
    bool_ty: TyId,
    str_ty: TyId,
    u32_ty: IntTy,
    u64_ty: IntTy,
}

impl Types {
    fn new(tys: &mut TyStore) -> Types {
        let ints: Vec<IntTy> = INT_PRIMS
            .iter()
            .map(|&p| IntTy {
                id: tys.prim(p),
                width: match p {
                    PrimKind::I64 | PrimKind::U64 => 64,
                    PrimKind::I32 | PrimKind::U32 => 32,
                    PrimKind::I16 | PrimKind::U16 => 16,
                    _ => 8,
                },
                signed: matches!(p, PrimKind::I64 | PrimKind::I32 | PrimKind::I16),
            })
            .collect();
        let find = |p: PrimKind, tys: &mut TyStore| {
            let id = tys.prim(p);
            *ints.iter().find(|t| t.id == id).expect("listed int type")
        };
        let u32_ty = find(PrimKind::U32, tys);
        let u64_ty = find(PrimKind::U64, tys);
        Types {
            bool_ty: tys.prim(PrimKind::Bool),
            str_ty: tys.prim(PrimKind::Str),
            ints,
            u32_ty,
            u64_ty,
        }
    }
}

/// A helper's signature, as the caller sees it.
#[derive(Clone)]
struct HelperSig {
    key: DeclKeyId,
    params: Vec<IntTy>,
    ret: IntTy,
}

/// One block under construction.
struct Staged {
    first: u32,
    len: u32,
    term: Option<InstRow>,
}

/// Builds one function's [`DeclFmir`].
struct FnGen<'a> {
    t: &'a Types,
    p: &'a Profile,
    rng: &'a mut Rng,
    decl: DeclFmir,
    insts: Vec<InstRow>,
    blocks: Vec<Staged>,
    open: usize,
    /// Parameter values (defined before the entry block).
    params: Vec<(ValId, IntTy)>,
    /// Local places in scope: `(root, type, assignable)`. The checksum is
    /// `locals[0]`; a loop counter is readable but never assignable (an
    /// assignment could reset it and unbound the loop). A local created in
    /// a nested region (a branch, a loop body) leaves scope with it, so no
    /// later block can read a place one path never initialised.
    locals: Vec<(u32, IntTy, bool)>,
    next_root: u32,
    helpers: &'a [HelperSig],
    loop_depth: u32,
    prints_left: u32,
    budget: u32,
}

impl<'a> FnGen<'a> {
    fn new(
        t: &'a Types,
        p: &'a Profile,
        rng: &'a mut Rng,
        key: DeclKeyId,
        params: &[IntTy],
        helpers: &'a [HelperSig],
        prints: u32,
    ) -> FnGen<'a> {
        let mut decl = DeclFmir::empty(key, FnSigId(key.0));
        decl.blocks = BlockPool::new();
        let mut vals = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let v = decl.push_val(ValRow::new(p.id, false, 0, ValDef::Param(i as u16)));
            vals.push((v, *p));
        }
        FnGen {
            t,
            p,
            rng,
            decl,
            insts: Vec::new(),
            blocks: vec![Staged {
                first: 0,
                len: 0,
                term: None,
            }],
            open: 0,
            params: vals,
            locals: Vec::new(),
            next_root: params.len() as u32,
            helpers,
            loop_depth: 0,
            prints_left: prints,
            budget: 0,
        }
    }

    // -- emission ------------------------------------------------------------

    fn emit(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) -> ValId {
        let inst = self.insts.len() as u32;
        let v = self
            .decl
            .push_val(ValRow::new(ty, false, 0, ValDef::Inst(InstId(inst))));
        self.push_row(op, a, b, c, ty);
        v
    }

    fn emit_void(&mut self, op: Op, a: u32, b: u32) {
        self.push_row(op, a, b, NO_OPERAND, TY_UNIT);
    }

    fn push_row(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) {
        self.insts.push(InstRow {
            op,
            a,
            b,
            c,
            ty,
            site: SiteId(0),
        });
        self.blocks[self.open].len += 1;
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

    /// Ends the open block with `term` and opens `next` (which must be
    /// fresh and empty).
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

    fn const_bits(&mut self, bits: u64, t: IntTy) -> ValId {
        let v = bits & t.mask();
        self.emit(Op::ConstInt, v as u32, (v >> 32) as u32, NO_OPERAND, t.id)
    }

    fn bin(&mut self, op: Op, a: ValId, b: ValId, t: IntTy) -> ValId {
        self.emit(op, a.0, b.0, NO_OPERAND, t.id)
    }

    fn masked(&mut self, v: ValId, m: u64, t: IntTy) -> ValId {
        let k = self.const_bits(m, t);
        self.bin(Op::And, v, k, t)
    }

    fn read_local(&mut self, i: usize) -> ValId {
        let (root, t, _) = self.locals[i];
        let p = self.decl.places.intern(root, &[], t.id);
        self.emit(Op::CopyFrom, p.0, NO_OPERAND, NO_OPERAND, t.id)
    }

    fn write_local(&mut self, i: usize, v: ValId) {
        let (root, t, _) = self.locals[i];
        let p = self.decl.places.intern(root, &[], t.id);
        self.emit_void(Op::Init, p.0, v.0);
    }

    fn new_local(&mut self, t: IntTy, init: ValId, assignable: bool) -> usize {
        let root = self.next_root;
        self.next_root += 1;
        self.locals.push((root, t, assignable));
        let i = self.locals.len() - 1;
        self.write_local(i, init);
        i
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

    fn pick_int(&mut self) -> IntTy {
        let i = self.rng.below(self.t.ints.len() as u64) as usize;
        self.t.ints[i]
    }

    // -- expressions -----------------------------------------------------------

    fn interesting(&mut self, t: IntTy) -> u64 {
        let m = t.mask();
        let min_signed = if t.signed { 1u64 << (t.width - 1) } else { 0 };
        match self.rng.below(10) {
            0 => 0,
            1 => 1,
            2 => m,          // -1 for signed, MAX for unsigned
            3 => min_signed, // MIN for signed, 0 for unsigned
            4 => m >> 1,     // MAX for signed
            5 => self.rng.below(16),
            6 => self.rng.below(1000),
            _ => self.rng.next_u64(),
        }
    }

    fn leaf(&mut self, t: IntTy) -> ValId {
        let same_locals: Vec<usize> = (0..self.locals.len())
            .filter(|&i| self.locals[i].1.id == t.id)
            .collect();
        let same_params: Vec<ValId> = self
            .params
            .iter()
            .filter(|(_, p)| p.id == t.id)
            .map(|(v, _)| *v)
            .collect();
        match self.rng.below(6) {
            0 | 1 if !same_locals.is_empty() => {
                let i = same_locals[self.rng.below(same_locals.len() as u64) as usize];
                self.read_local(i)
            }
            2 if !same_params.is_empty() && self.open == 0 => {
                // A parameter VALUE is defined before the entry block; it is
                // used directly only there (it dominates everything, but the
                // rule "values stay in their block" keeps the generator
                // trivially right). Elsewhere params are read as locals.
                same_params[self.rng.below(same_params.len() as u64) as usize]
            }
            2 if !same_params.is_empty() => {
                // A parameter is root `ordinal`: reading its PLACE is legal
                // in every block.
                let k = self.rng.below(same_params.len() as u64) as usize;
                let ord = self
                    .params
                    .iter()
                    .position(|(v, _)| *v == same_params[k])
                    .unwrap_or(0) as u32;
                let p = self.decl.places.intern(ord, &[], t.id);
                self.emit(Op::CopyFrom, p.0, NO_OPERAND, NO_OPERAND, t.id)
            }
            3 if !self.locals.is_empty() => {
                // A conversion from another local's type.
                let i = self.rng.below(self.locals.len() as u64) as usize;
                let src = self.read_local(i);
                let st = self.locals[i].1;
                self.convert(src, st, t)
            }
            _ => {
                let bits = self.interesting(t);
                self.const_bits(bits, t)
            }
        }
    }

    fn convert(&mut self, v: ValId, from: IntTy, to: IntTy) -> ValId {
        match self.rng.below(3) {
            0 => self.emit(Op::ConvWrap, v.0, NO_OPERAND, NO_OPERAND, to.id),
            1 => self.emit(Op::ConvSat, v.0, NO_OPERAND, NO_OPERAND, to.id),
            _ => {
                let small = self.masked(v, 0x7F, from);
                self.emit(Op::ConvChecked, small.0, NO_OPERAND, NO_OPERAND, to.id)
            }
        }
    }

    fn expr(&mut self, t: IntTy, depth: u32) -> ValId {
        if depth == 0 || self.rng.below(4) == 0 {
            return self.leaf(t);
        }
        let a = self.expr(t, depth - 1);
        let b = self.expr(t, depth - 1);
        match self.rng.below(19) {
            0 => self.bin(Op::Add(ArithMode::Wrap), a, b, t),
            1 => self.bin(Op::Sub(ArithMode::Wrap), a, b, t),
            2 => self.bin(Op::Mul(ArithMode::Wrap), a, b, t),
            3 => self.bin(Op::Add(ArithMode::Sat), a, b, t),
            4 => self.bin(Op::Sub(ArithMode::Sat), a, b, t),
            5 => self.bin(Op::Mul(ArithMode::Sat), a, b, t),
            6 => {
                let m = t.add_mask();
                let x = self.masked(a, m, t);
                let y = self.masked(b, m, t);
                self.bin(Op::Add(ArithMode::Trap), x, y, t)
            }
            7 => {
                let m = t.add_mask();
                let x = self.masked(a, m, t);
                let hi = self.const_bits(m + 1, t);
                let x = self.bin(Op::Or, x, hi, t);
                let y = self.masked(b, m, t);
                self.bin(Op::Sub(ArithMode::Trap), x, y, t)
            }
            8 => {
                let m = t.mul_mask();
                let x = self.masked(a, m, t);
                let y = self.masked(b, m, t);
                self.bin(Op::Mul(ArithMode::Trap), x, y, t)
            }
            9 | 10 => {
                let one = self.const_bits(1, t);
                let d = self.bin(Op::Or, b, one, t);
                let op = if self.rng.below(2) == 0 {
                    Op::Div(ArithMode::Wrap)
                } else {
                    Op::Rem(ArithMode::Wrap)
                };
                self.bin(op, a, d, t)
            }
            11 => {
                let one = self.const_bits(1, t);
                let d = self.bin(Op::Or, b, one, t);
                let x = self.masked(a, t.mask() >> 1, t);
                let op = if self.rng.below(2) == 0 {
                    Op::Div(ArithMode::Trap)
                } else {
                    Op::Rem(ArithMode::Trap)
                };
                self.bin(op, x, d, t)
            }
            12 | 13 => {
                let n = self.masked(b, u64::from(t.width - 1), t);
                let op = match self.rng.below(4) {
                    0 => Op::Shl(ArithMode::Wrap),
                    1 => Op::Shl(ArithMode::Sat),
                    2 => Op::Shr(ArithMode::Wrap),
                    _ => Op::Shr(ArithMode::Trap),
                };
                self.bin(op, a, n, t)
            }
            14 => self.bin(Op::And, a, b, t),
            15 => self.bin(Op::Or, a, b, t),
            16 => self.bin(Op::Xor, a, b, t),
            17 => {
                let op = match self.rng.below(3) {
                    0 => Op::Neg(ArithMode::Wrap),
                    1 if !t.signed && !self.p.ops.has(OpSet::NEG_SAT_UNSIGNED) => {
                        Op::Neg(ArithMode::Wrap)
                    }
                    1 => Op::Neg(ArithMode::Sat),
                    _ => Op::Not,
                };
                self.emit(op, a.0, NO_OPERAND, NO_OPERAND, t.id)
            }
            _ => {
                // A saturating division: `MIN / -1` saturates to `MAX`.
                let one = self.const_bits(1, t);
                let d = self.bin(Op::Or, b, one, t);
                self.bin(Op::Div(ArithMode::Sat), a, d, t)
            }
        }
    }

    fn pred(&mut self) -> CmpPred {
        match self.rng.below(6) {
            0 => CmpPred::Eq,
            1 => CmpPred::Ne,
            2 => CmpPred::Lt,
            3 => CmpPred::Le,
            4 => CmpPred::Gt,
            _ => CmpPred::Ge,
        }
    }

    fn cond(&mut self) -> ValId {
        let t = self.pick_int();
        let a = self.expr(t, 2);
        let b = self.expr(t, 1);
        let pred = self.pred();
        self.emit(Op::Icmp(pred), a.0, b.0, NO_OPERAND, self.t.bool_ty)
    }

    // -- statements --------------------------------------------------------------

    /// `cs = cs * MIX_MUL ^ (v as u64)`, the checksum fold.
    fn mix(&mut self, v: ValId, t: IntTy) {
        let u64t = self.t.u64_ty;
        let w = if t.id == u64t.id {
            v
        } else {
            self.emit(Op::ConvWrap, v.0, NO_OPERAND, NO_OPERAND, u64t.id)
        };
        let cs = self.read_local(0);
        let k = self.const_bits(MIX_MUL, u64t);
        let m = self.bin(Op::Mul(ArithMode::Wrap), cs, k, u64t);
        let x = self.bin(Op::Xor, m, w, u64t);
        self.write_local(0, x);
    }

    fn print_checksum(&mut self) {
        let unit = self.emit(Op::ConstUnit, NO_OPERAND, NO_OPERAND, NO_OPERAND, TY_UNIT);
        let cs = self.read_local(0);
        self.intrinsic(WRITE_UINT, &[unit, cs]);
        let s = self.emit(
            Op::ConstStr,
            EMPTY_STR,
            NO_OPERAND,
            NO_OPERAND,
            self.t.str_ty,
        );
        self.intrinsic(WRITE_LINE, &[unit, s]);
    }

    fn stmts(&mut self, depth: u32) {
        let n = 1 + self.rng.below(4);
        for _ in 0..n {
            if self.budget == 0 {
                return;
            }
            self.budget -= 1;
            self.stmt(depth);
        }
    }

    fn stmt(&mut self, depth: u32) {
        match self.rng.below(10) {
            0..=2 => {
                let targets: Vec<usize> = (0..self.locals.len())
                    .filter(|&i| self.locals[i].2)
                    .collect();
                let i = targets[self.rng.below(targets.len() as u64) as usize];
                let t = self.locals[i].1;
                let v = self.expr(t, 3);
                self.write_local(i, v);
            }
            3 | 4 => {
                let t = self.pick_int();
                let v = self.expr(t, 3);
                self.mix(v, t);
            }
            5 if depth > 0 && self.p.branches => self.if_stmt(depth),
            6 if depth > 0 && self.loop_depth < 2 && self.p.loops => self.loop_stmt(depth),
            7 if !self.helpers.is_empty() => self.call_stmt(),
            8 if self.prints_left > 0 => {
                self.prints_left -= 1;
                self.print_checksum();
            }
            _ => {
                let i = self.rng.below(self.locals.len() as u64) as usize;
                let t = self.locals[i].1;
                let v = self.read_local(i);
                self.mix(v, t);
            }
        }
    }

    fn if_stmt(&mut self, depth: u32) {
        let c = self.cond();
        let then_b = self.new_block();
        let else_b = self.new_block();
        let join = self.new_block();
        let scope = self.locals.len();
        self.end_and_open(Op::CondBr, c.0, then_b.0, else_b.0, Some(then_b));
        self.stmts(depth - 1);
        self.locals.truncate(scope);
        self.end_and_open(Op::Br, join.0, NO_OPERAND, NO_OPERAND, Some(else_b));
        if self.rng.below(2) == 0 {
            self.stmts(depth - 1);
        }
        self.locals.truncate(scope);
        self.end_and_open(Op::Br, join.0, NO_OPERAND, NO_OPERAND, Some(join));
    }

    fn loop_stmt(&mut self, depth: u32) {
        let u32t = self.t.u32_ty;
        let trips = self.rng.below(6);
        let zero = self.const_bits(0, u32t);
        let ctr = self.new_local(u32t, zero, false);
        let scope = self.locals.len();
        let head = self.new_block();
        let body = self.new_block();
        let exit = self.new_block();
        self.end_and_open(Op::Br, head.0, NO_OPERAND, NO_OPERAND, Some(head));
        let i = self.read_local(ctr);
        let n = self.const_bits(trips, u32t);
        let go = self.emit(Op::Icmp(CmpPred::Lt), i.0, n.0, NO_OPERAND, self.t.bool_ty);
        self.end_and_open(Op::CondBr, go.0, body.0, exit.0, Some(body));
        self.loop_depth += 1;
        self.stmts(depth - 1);
        self.loop_depth -= 1;
        self.locals.truncate(scope);
        // The counter itself feeds the checksum, so the trip count is
        // observable.
        let i = self.read_local(ctr);
        self.mix(i, u32t);
        let i = self.read_local(ctr);
        let one = self.const_bits(1, u32t);
        let next = self.bin(Op::Add(ArithMode::Trap), i, one, u32t);
        self.write_local(ctr, next);
        self.end_and_open(Op::Br, head.0, NO_OPERAND, NO_OPERAND, Some(exit));
    }

    fn call_stmt(&mut self) {
        let h = self.helpers[self.rng.below(self.helpers.len() as u64) as usize].clone();
        let mut args = Vec::new();
        for p in &h.params {
            args.push(self.expr(*p, 2));
        }
        let convs = vec![Conv::Let; args.len()];
        let range = self.decl.insts.push_operands(&args, &convs);
        let call = self.decl.insts.push_call(CallRow {
            callee: Callee::Direct(h.key),
            args: range,
        });
        let r = self.emit(Op::CallDirect, call, NO_OPERAND, NO_OPERAND, h.ret.id);
        self.mix(r, h.ret);
    }

    fn finish(mut self) -> DeclFmir {
        assert!(
            self.blocks.iter().all(|b| b.term.is_some()),
            "every generated block is terminated"
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

/// The program [`generate`] builds for `seed`, before it is wrapped.
fn gen_fn(
    t: &Types,
    p: &Profile,
    rng: &mut Rng,
    key: DeclKeyId,
    params: &[IntTy],
    ret: Option<IntTy>,
    helpers: &[HelperSig],
) -> DeclFmir {
    let prints = if ret.is_none() { 2 } else { 0 };
    let mut g = FnGen::new(t, p, rng, key, params, helpers, prints);
    // Statement budget: `main` is the larger body (it is what runs), a
    // helper a smaller one (it may run inside `main`'s loops).
    g.budget = if ret.is_none() {
        10 + g.rng.below(25) as u32
    } else {
        4 + g.rng.below(10) as u32
    };
    // Locals, all initialised in the entry block: the checksum first.
    let u64t = t.u64_ty;
    let seed_bits = g.rng.next_u64();
    let cs0 = g.const_bits(seed_bits, u64t);
    g.new_local(u64t, cs0, true);
    let n_locals = 1 + g.rng.below(5);
    for _ in 0..n_locals {
        let ty = g.pick_int();
        let v = g.leaf(ty);
        g.new_local(ty, v, true);
    }
    // The body: top-level statements until the budget is spent (nested
    // bodies draw from the same budget).
    while g.budget > 0 {
        g.budget -= 1;
        g.stmt(3);
    }
    match ret {
        None => {
            g.print_checksum();
            g.end_and_open(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND, None);
        }
        Some(rt) => {
            let cs = g.read_local(0);
            let v = if rt.id == u64t.id {
                cs
            } else {
                g.emit(Op::ConvWrap, cs.0, NO_OPERAND, NO_OPERAND, rt.id)
            };
            g.end_and_open(Op::Ret, v.0, NO_OPERAND, NO_OPERAND, None);
        }
    }
    g.finish()
}

/// Generates the program for `seed`: `main` plus up to three helpers.
pub fn generate(seed: u64) -> Generated {
    generate_with(seed, &Profile::FULL)
}

/// Generates the program for `seed` under profile `p`.
pub fn generate_with(seed: u64, p: &Profile) -> Generated {
    let mut rng = Rng::new(seed);
    let mut tys = TyStore::new();
    let t = Types::new(&mut tys);
    // The draw is made under every profile, so FULL's stream is unchanged.
    let n_helpers = rng.below(4) as u32;
    let n_helpers = if p.helpers { n_helpers } else { 0 };
    let mut sigs: Vec<HelperSig> = Vec::new();
    let mut fns: Vec<ProgFn> = Vec::new();
    let intrinsics = vec![
        (WRITE_LINE, "stdout_write_line".to_string()),
        (WRITE_UINT, "stdout_write_uint".to_string()),
    ];
    let strings = vec![(EMPTY_STR, Vec::new())];
    for i in 0..n_helpers {
        let np = 1 + rng.below(3);
        let params: Vec<IntTy> = (0..np)
            .map(|_| t.ints[rng.below(t.ints.len() as u64) as usize])
            .collect();
        let ret = t.ints[rng.below(t.ints.len() as u64) as usize];
        let key = DeclKeyId(HELPER_BASE + i);
        // Helper `i` may call helpers `0..i` only: no recursion.
        let decl = gen_fn(&t, p, &mut rng, key, &params, Some(ret), &sigs);
        sigs.push(HelperSig { key, params, ret });
        fns.push(ProgFn {
            name: format!("h{i}"),
            decl,
            strings: strings.clone(),
            intrinsics: intrinsics.clone(),
        });
    }
    let main = gen_fn(&t, p, &mut rng, DeclKeyId(MAIN_KEY), &[], None, &sigs);
    fns.insert(
        0,
        ProgFn {
            name: "main".into(),
            decl: main,
            strings,
            intrinsics,
        },
    );
    Generated {
        seed,
        prog: Program {
            fns,
            entry: 0,
            config: Config::v0_1(),
            names: Default::default(),
        },
        tys,
    }
}
