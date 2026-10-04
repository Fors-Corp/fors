//! The integer stencils (§9 ch03 R2/R4): one per (op, mode, type), each
//! mirroring the corresponding `trap_*`/`wrap_*`/`sat_*`/`conv_*` function of
//! `fors-interp/src/arith.rs` — the semantic oracle, not this file. The
//! edge table (`edge_table_matches_arith_rs`) and the generator differential
//! check every stencil against it natively.
//!
//! Representation (E5): every value lives in its 8-byte slot in CANONICAL
//! EXTENDED form — sign-extended to 64 bits for signed types, zero-extended
//! for unsigned ones (`bool` is 0/1). So a narrow (<= 32-bit) operation is
//! computed EXACTLY in 64 bits (no narrow op on canonical operands can
//! overflow 64 bits — the one exception, `u32 * u32`, still fits as an
//! unsigned 64-bit value), then:
//!
//! - `trap` checks the exact result fits: `cmp x12, w12, {s,u}xt{b,h,w}`;
//! - `wrap` re-canonicalises the low bits;
//! - `sat` clamps the exact result to the type's bounds.
//!
//! 64-bit operations use the flag-setting forms (`adds`/`subs`/`negs`, `V`
//! for signed, `C` for unsigned) or `smulh`/`umulh`. Registers: `x10` = a,
//! `x11` = b, `x12` = result, `x13..x15` temporaries (fors-abi's scratch
//! set); a trap branches to the site's `brk` in the cold tail.

use fors_asm::Reg;
use fors_asm::inst::{Inst, PairIndex};
use fors_asm::operand::{
    Cond, ExtendKind, LogicalImm, RegExtend, RegShift, SImm7Scaled, ShiftKind, Uimm12Lsl,
};
use fors_oir::{CmpPred, LowTy, TrapKind};

use super::{Field, RtSym, Seq};

/// An integer type (the stencil key's width/sign).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntTy {
    pub const ALL: [IntTy; 8] = [
        IntTy::I8,
        IntTy::I16,
        IntTy::I32,
        IntTy::I64,
        IntTy::U8,
        IntTy::U16,
        IntTy::U32,
        IntTy::U64,
    ];

    pub fn of(t: LowTy) -> Option<IntTy> {
        Some(match t {
            LowTy::I8 => IntTy::I8,
            LowTy::I16 => IntTy::I16,
            LowTy::I32 => IntTy::I32,
            LowTy::I64 => IntTy::I64,
            LowTy::U8 => IntTy::U8,
            LowTy::U16 => IntTy::U16,
            LowTy::U32 => IntTy::U32,
            LowTy::U64 => IntTy::U64,
            _ => return None,
        })
    }

    pub fn width(self) -> u32 {
        match self {
            IntTy::I8 | IntTy::U8 => 8,
            IntTy::I16 | IntTy::U16 => 16,
            IntTy::I32 | IntTy::U32 => 32,
            IntTy::I64 | IntTy::U64 => 64,
        }
    }

    pub fn signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
    }

    pub fn narrow(self) -> bool {
        self.width() < 64
    }

    /// Inclusive bounds as canonical 64-bit patterns.
    pub fn lo(self) -> u64 {
        if self.signed() {
            (-(1i128 << (self.width() - 1))) as i64 as u64
        } else {
            0
        }
    }

    pub fn hi(self) -> u64 {
        let w = self.width();
        if self.signed() {
            ((1u128 << (w - 1)) - 1) as u64
        } else if w == 64 {
            u64::MAX
        } else {
            (1u64 << w) - 1
        }
    }

    /// The extend that re-reads the low `width` bits (`None` for 64-bit).
    fn ext(self) -> Option<ExtendKind> {
        Some(match self {
            IntTy::I8 => ExtendKind::Sxtb,
            IntTy::I16 => ExtendKind::Sxth,
            IntTy::I32 => ExtendKind::Sxtw,
            IntTy::U8 => ExtendKind::Uxtb,
            IntTy::U16 => ExtendKind::Uxth,
            IntTy::U32 => ExtendKind::Uxtw,
            IntTy::I64 | IntTy::U64 => return None,
        })
    }

    /// The raw-bits (zero) extension of a canonical value: what
    /// `stdout_write_uint` and a shift count read (the interpreter's slot
    /// holds the low `width` bits zero-extended).
    pub fn raw_ext(self) -> RawExt {
        match self {
            IntTy::I8 => RawExt::B,
            IntTy::I16 => RawExt::H,
            IntTy::I32 => RawExt::W,
            _ => RawExt::None,
        }
    }
}

/// Zero-extension from the low 8/16/32 bits (identity for unsigned and
/// 64-bit types, whose canonical form already is the raw bits).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum RawExt {
    None,
    B,
    H,
    W,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ArMode {
    Trap,
    Wrap,
    Sat,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ShiftOp {
    Shl,
    Shr,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LogicOp {
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum ConvOp {
    Checked,
    Wrap,
    Sat,
}

/// `icmp`'s predicate as a key component.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Pred {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Pred {
    pub const ALL: [Pred; 6] = [Pred::Eq, Pred::Ne, Pred::Lt, Pred::Le, Pred::Gt, Pred::Ge];

    pub fn of(p: CmpPred) -> Pred {
        match p {
            CmpPred::Eq => Pred::Eq,
            CmpPred::Ne => Pred::Ne,
            CmpPred::Lt => Pred::Lt,
            CmpPred::Le => Pred::Le,
            CmpPred::Gt => Pred::Gt,
            CmpPred::Ge => Pred::Ge,
        }
    }

    fn cond(self, signed: bool) -> Cond {
        match (self, signed) {
            (Pred::Eq, _) => Cond::EQ,
            (Pred::Ne, _) => Cond::NE,
            (Pred::Lt, true) => Cond::LT,
            (Pred::Le, true) => Cond::LE,
            (Pred::Gt, true) => Cond::GT,
            (Pred::Ge, true) => Cond::GE,
            (Pred::Lt, false) => Cond::CC,
            (Pred::Le, false) => Cond::LS,
            (Pred::Gt, false) => Cond::HI,
            (Pred::Ge, false) => Cond::CS,
        }
    }
}

/// Every stencil of the dev tier (M2-0's scalar surface).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Key {
    /// `x12 := imm[0] | imm[1] << 16 | imm[2] << 32 | imm[3] << 48`;
    /// stored to `dst`.
    Const,
    /// `dst := a` (a slot load or a slot store).
    Copy,
    Bin {
        op: BinOp,
        mode: ArMode,
        ty: IntTy,
    },
    Shift {
        op: ShiftOp,
        mode: ArMode,
        ty: IntTy,
        count: RawExt,
    },
    Neg {
        mode: ArMode,
        ty: IntTy,
    },
    Logic {
        op: LogicOp,
    },
    Not {
        ty: IntTy,
    },
    NotBool,
    Icmp {
        pred: Pred,
        signed: bool,
    },
    Conv {
        op: ConvOp,
        from: IntTy,
        to: IntTy,
    },
    /// `_fors_rt_write_uint(zext(a))`.
    WriteUint {
        ext: RawExt,
    },
    /// `_fors_rt_write_line(&lit, imm[0] | imm[1] << 16)`.
    WriteLine,
    /// `stp x29, x30, [sp, #-16]!; mov x29, sp; movz x10, #imm[0];
    /// sub sp, sp, x10` — frame size in `imm[0]`.
    Prologue,
    /// `mov sp, x29; ldp x29, x30, [sp], #16; ret`.
    Epilogue,
    /// The explicit `trap` terminator: `b` to its site.
    TrapJump {
        kind: u8,
    },
    /// A trap site in the cold tail: `brk #(TRAP_BRK_BASE + kind)`.
    Brk {
        kind: u8,
    },
}

/// Every key, in table order.
pub fn all_keys() -> Vec<Key> {
    let modes = [ArMode::Trap, ArMode::Wrap, ArMode::Sat];
    let mut k = vec![
        Key::Const,
        Key::Copy,
        Key::NotBool,
        Key::WriteLine,
        Key::Prologue,
        Key::Epilogue,
    ];
    for ty in IntTy::ALL {
        for mode in modes {
            for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem] {
                k.push(Key::Bin { op, mode, ty });
            }
            for op in [ShiftOp::Shl, ShiftOp::Shr] {
                for count in [RawExt::None, RawExt::B, RawExt::H, RawExt::W] {
                    k.push(Key::Shift {
                        op,
                        mode,
                        ty,
                        count,
                    });
                }
            }
            // Owner Q6: no Trap/Sat `neg` on an unsigned type.
            if ty.signed() || mode == ArMode::Wrap {
                k.push(Key::Neg { mode, ty });
            }
        }
        k.push(Key::Not { ty });
        for to in IntTy::ALL {
            for op in [ConvOp::Checked, ConvOp::Wrap, ConvOp::Sat] {
                k.push(Key::Conv { op, from: ty, to });
            }
        }
    }
    for op in [LogicOp::And, LogicOp::Or, LogicOp::Xor] {
        k.push(Key::Logic { op });
    }
    for pred in Pred::ALL {
        for signed in [true, false] {
            k.push(Key::Icmp { pred, signed });
        }
    }
    for ext in [RawExt::None, RawExt::B, RawExt::H, RawExt::W] {
        k.push(Key::WriteUint { ext });
    }
    for kind in 0..fors_abi::TRAP_KIND_COUNT as u8 {
        k.push(Key::TrapJump { kind });
        k.push(Key::Brk { kind });
    }
    k
}

// -- registers ---------------------------------------------------------------

const A: u8 = 10;
const B: u8 = 11;
const R: u8 = 12;
const T1: u8 = 13;
const T2: u8 = 14;
const T3: u8 = 15;

fn x(n: u8) -> Reg {
    Reg::x(n)
}

fn w(n: u8) -> Reg {
    Reg::w(n)
}

fn none() -> RegShift {
    RegShift::none()
}

fn trap_kind(k: u8) -> TrapKind {
    TrapKind::from_u32(u32::from(k)).expect("one of the eight kinds")
}

// -- helpers -------------------------------------------------------------------

/// `rd := value` with a fixed (hole-free) `movz`/`movn` + `movk` sequence.
fn mov_imm(s: &mut Seq<'_>, rd: u8, value: u64) {
    let halves: [u16; 4] = std::array::from_fn(|i| (value >> (16 * i)) as u16);
    let zeros = halves.iter().filter(|&&h| h == 0).count();
    let ones = halves.iter().filter(|&&h| h == 0xFFFF).count();
    if ones > zeros {
        // movn for the first non-0xFFFF half (or #0 if all are 0xFFFF).
        let first = halves.iter().position(|&h| h != 0xFFFF).unwrap_or(0);
        s.i(Inst::movn(x(rd), !halves[first], (16 * first) as u8));
        for (i, &h) in halves.iter().enumerate() {
            if i != first && h != 0xFFFF {
                s.i(Inst::movk(x(rd), h, (16 * i) as u8));
            }
        }
    } else {
        let first = halves.iter().position(|&h| h != 0).unwrap_or(0);
        s.i(Inst::movz(x(rd), halves[first], (16 * first) as u8));
        for (i, &h) in halves.iter().enumerate() {
            if i != first && h != 0 {
                s.i(Inst::movk(x(rd), h, (16 * i) as u8));
            }
        }
    }
}

/// `rd := canonical_ty(low bits of rn)`.
fn canon(s: &mut Seq<'_>, rd: u8, rn: u8, ty: IntTy) {
    match ty {
        IntTy::I8 => s.i(Inst::sxtb(x(rd), x(rn))),
        IntTy::I16 => s.i(Inst::sxth(x(rd), x(rn))),
        IntTy::I32 => s.i(Inst::sxtw(x(rd), w(rn))),
        IntTy::U8 => s.i(Inst::uxtb(w(rd), w(rn))),
        IntTy::U16 => s.i(Inst::uxth(w(rd), w(rn))),
        IntTy::U32 => s.i(Inst::mov_reg(w(rd), w(rn))),
        IntTy::I64 | IntTy::U64 => {
            if rd != rn {
                s.i(Inst::mov_reg(x(rd), x(rn)));
            }
        }
    }
}

/// Raw-bits zero extension of `rn` into `rd`.
fn raw(s: &mut Seq<'_>, rd: u8, rn: u8, e: RawExt) {
    match e {
        RawExt::B => s.i(Inst::uxtb(w(rd), w(rn))),
        RawExt::H => s.i(Inst::uxth(w(rd), w(rn))),
        RawExt::W => s.i(Inst::mov_reg(w(rd), w(rn))),
        RawExt::None => {
            if rd != rn {
                s.i(Inst::mov_reg(x(rd), x(rn)));
            }
        }
    }
}

/// Narrow types: trap `kind` unless `x<r>` is the canonical form of its
/// own low bits, i.e. the exact result fits the type.
fn fits_or_trap(s: &mut Seq<'_>, r: u8, ty: IntTy, kind: TrapKind) {
    let e = ty.ext().expect("narrow type");
    s.i(RegExtend::new(e, 0).and_then(|e| Inst::cmp_extended(x(r), w(r), e)));
    s.trap_if(Cond::NE, kind);
}

/// Clamp signed `x12` to `[lo, hi]` of `ty` (signed comparisons).
fn clamp_signed(s: &mut Seq<'_>, ty: IntTy) {
    mov_imm(s, T1, ty.hi());
    s.i(Inst::cmp_shifted(x(R), x(T1), none()));
    s.i(Inst::csel(x(R), x(T1), x(R), Cond::GT));
    mov_imm(s, T1, ty.lo());
    s.i(Inst::cmp_shifted(x(R), x(T1), none()));
    s.i(Inst::csel(x(R), x(T1), x(R), Cond::LT));
}

/// Clamp `x12` (an exact non-negative value) to `hi` (unsigned compare).
fn clamp_hi_unsigned(s: &mut Seq<'_>, hi: u64) {
    mov_imm(s, T1, hi);
    s.i(Inst::cmp_shifted(x(R), x(T1), none()));
    s.i(Inst::csel(x(R), x(T1), x(R), Cond::HI));
}

/// Clamp `x12` (an exact signed value) at zero from below.
fn clamp_zero(s: &mut Seq<'_>) {
    s.i(Uimm12Lsl::new(0).and_then(|i| Inst::cmp_imm(x(R), i)));
    s.i(Inst::csel(x(R), Reg::xzr(), x(R), Cond::LT));
}

/// `x<rd> := (sign of x<from> < 0) ? i64::MIN : i64::MAX`.
fn sat_by_sign(s: &mut Seq<'_>, rd: u8, from: u8) {
    s.i(Inst::asr_imm(x(rd), x(from), 63));
    s.i(LogicalImm::new(i64::MAX as u64, true).and_then(|m| Inst::eor_imm(x(rd), x(rd), m)));
}

fn load_ab(s: &mut Seq<'_>) {
    s.ldr_slot(A, Field::SlotA);
    s.ldr_slot(B, Field::SlotB);
}

fn store_r(s: &mut Seq<'_>) {
    s.str_slot(R, Field::SlotDst);
}

/// The 64-bit signed `MIN / -1` (and `MIN % -1`) detector: falls through
/// to the next instruction only when `b == -1 && a == MIN` holds, after
/// which the flags are `V` set; `skip` words ahead is where the
/// non-overflow path resumes.
fn min_by_minus_one(s: &mut Seq<'_>, skip_to_after_vs: i64) {
    s.i(Uimm12Lsl::new(1).and_then(|i| Inst::cmn_imm(x(B), i)));
    // b != -1: skip the `negs` and the V test.
    s.b_cond_local(Cond::NE, skip_to_after_vs);
    // V := (a == MIN): `0 - MIN` is the only negation that overflows.
    s.i(Inst::negs(Reg::xzr(), x(A), none()));
}

// -- bodies --------------------------------------------------------------------

/// Emits stencil `key`'s body into `s`.
pub fn body(key: Key, s: &mut Seq<'_>) {
    match key {
        Key::Const => {
            s.movz_imm(x(R), 0, 0);
            s.movk_imm(x(R), 1, 16);
            s.movk_imm(x(R), 2, 32);
            s.movk_imm(x(R), 3, 48);
            store_r(s);
        }
        Key::Copy => {
            s.ldr_slot(A, Field::SlotA);
            s.str_slot(A, Field::SlotDst);
        }
        Key::Bin { op, mode, ty } => {
            load_ab(s);
            bin(s, op, mode, ty);
            store_r(s);
        }
        Key::Shift {
            op,
            mode,
            ty,
            count,
        } => {
            load_ab(s);
            // The count is the raw low bits of `b` (arith.rs reads the slot
            // bits); `count >= width` traps `shift` in every mode.
            raw(s, T1, B, count);
            s.i(Uimm12Lsl::new(u64::from(ty.width())).and_then(|i| Inst::cmp_imm(x(T1), i)));
            s.trap_if(Cond::CS, TrapKind::Shift);
            shift(s, op, mode, ty);
            store_r(s);
        }
        Key::Neg { mode, ty } => {
            s.ldr_slot(A, Field::SlotA);
            neg(s, mode, ty);
            store_r(s);
        }
        Key::Logic { op } => {
            load_ab(s);
            let r = match op {
                LogicOp::And => Inst::and_shifted(x(R), x(A), x(B), none()),
                LogicOp::Or => Inst::orr_shifted(x(R), x(A), x(B), none()),
                LogicOp::Xor => Inst::eor_shifted(x(R), x(A), x(B), none()),
            };
            s.i(r);
            store_r(s);
        }
        Key::Not { ty } => {
            s.ldr_slot(A, Field::SlotA);
            s.i(Inst::mvn(x(R), x(A), none()));
            if !ty.signed() {
                canon(s, R, R, ty);
            }
            store_r(s);
        }
        Key::NotBool => {
            s.ldr_slot(A, Field::SlotA);
            s.i(LogicalImm::new(1, true).and_then(|m| Inst::eor_imm(x(R), x(A), m)));
            store_r(s);
        }
        Key::Icmp { pred, signed } => {
            load_ab(s);
            s.i(Inst::cmp_shifted(x(A), x(B), none()));
            s.i(Inst::cset(x(R), pred.cond(signed)));
            store_r(s);
        }
        Key::Conv { op, from, to } => {
            s.ldr_slot(A, Field::SlotA);
            conv(s, op, from, to);
            store_r(s);
        }
        Key::WriteUint { ext } => {
            s.ldr_slot(0, Field::SlotA);
            raw(s, 0, 0, ext);
            s.bl(RtSym::WriteUint);
        }
        Key::WriteLine => {
            s.adr_lit(x(0));
            s.movz_imm(x(1), 0, 0);
            s.movk_imm(x(1), 1, 16);
            s.bl(RtSym::WriteLine);
        }
        Key::Prologue => {
            s.i(SImm7Scaled::new(-16, 8)
                .and_then(|o| Inst::stp(x(29), x(30), Reg::sp(), o, PairIndex::PreIndex)));
            s.i(Inst::mov_sp(x(29), Reg::sp()));
            s.movz_imm(x(A), 0, 0);
            s.i(RegExtend::new(ExtendKind::Uxtx, 0)
                .and_then(|e| Inst::sub_extended(Reg::sp(), Reg::sp(), x(A), e)));
        }
        Key::Epilogue => {
            s.i(Inst::mov_sp(Reg::sp(), x(29)));
            s.i(SImm7Scaled::new(16, 8)
                .and_then(|o| Inst::ldp(x(29), x(30), Reg::sp(), o, PairIndex::PostIndex)));
            s.i(Inst::ret(x(30)));
        }
        Key::TrapJump { kind } => s.trap_always(trap_kind(kind)),
        Key::Brk { kind } => {
            let imm = fors_abi::brk_imm(u16::from(kind)).expect("eight kinds");
            s.fixed(Inst::brk(imm));
        }
    }
}

fn bin(s: &mut Seq<'_>, op: BinOp, mode: ArMode, ty: IntTy) {
    let signed = ty.signed();
    match op {
        BinOp::Add | BinOp::Sub => {
            let add = op == BinOp::Add;
            if ty.narrow() {
                s.i(if add {
                    Inst::add_shifted(x(R), x(A), x(B), none())
                } else {
                    Inst::sub_shifted(x(R), x(A), x(B), none())
                });
                match mode {
                    ArMode::Wrap => canon(s, R, R, ty),
                    ArMode::Trap => fits_or_trap(s, R, ty, TrapKind::Overflow),
                    ArMode::Sat if signed => clamp_signed(s, ty),
                    ArMode::Sat if add => clamp_hi_unsigned(s, ty.hi()),
                    ArMode::Sat => clamp_zero(s),
                }
                return;
            }
            match mode {
                ArMode::Wrap => s.i(if add {
                    Inst::add_shifted(x(R), x(A), x(B), none())
                } else {
                    Inst::sub_shifted(x(R), x(A), x(B), none())
                }),
                ArMode::Trap | ArMode::Sat => {
                    s.i(if add {
                        Inst::adds_shifted(x(R), x(A), x(B), none())
                    } else {
                        Inst::subs_shifted(x(R), x(A), x(B), none())
                    });
                    match (mode, signed, add) {
                        (ArMode::Trap, true, _) => s.trap_if(Cond::VS, TrapKind::Overflow),
                        (ArMode::Trap, false, true) => s.trap_if(Cond::CS, TrapKind::Overflow),
                        (ArMode::Trap, false, false) => s.trap_if(Cond::CC, TrapKind::Overflow),
                        (_, true, _) => {
                            // Signed overflow saturates toward a's sign.
                            sat_by_sign(s, T1, A);
                            s.i(Inst::csel(x(R), x(T1), x(R), Cond::VS));
                        }
                        (_, false, true) => {
                            s.i(Inst::csinv(x(R), x(R), Reg::xzr(), Cond::CC));
                        }
                        (_, false, false) => {
                            s.i(Inst::csel(x(R), x(R), Reg::xzr(), Cond::CS));
                        }
                    }
                }
            }
        }
        BinOp::Mul => {
            if ty.narrow() {
                s.i(Inst::mul(x(R), x(A), x(B)));
                match mode {
                    ArMode::Wrap => canon(s, R, R, ty),
                    ArMode::Trap => fits_or_trap(s, R, ty, TrapKind::Overflow),
                    ArMode::Sat if signed => clamp_signed(s, ty),
                    ArMode::Sat => clamp_hi_unsigned(s, ty.hi()),
                }
                return;
            }
            match (mode, signed) {
                (ArMode::Wrap, _) => s.i(Inst::mul(x(R), x(A), x(B))),
                (ArMode::Trap, true) => {
                    s.i(Inst::mul(x(R), x(A), x(B)));
                    s.i(Inst::smulh(x(T1), x(A), x(B)));
                    s.i(RegShift::new(ShiftKind::Asr, 63, true)
                        .and_then(|sh| Inst::cmp_shifted(x(T1), x(R), sh)));
                    s.trap_if(Cond::NE, TrapKind::Overflow);
                }
                (ArMode::Trap, false) => {
                    s.i(Inst::umulh(x(T1), x(A), x(B)));
                    s.trap_cbnz(x(T1), TrapKind::Overflow);
                    s.i(Inst::mul(x(R), x(A), x(B)));
                }
                (ArMode::Sat, true) => {
                    s.i(Inst::mul(x(R), x(A), x(B)));
                    s.i(Inst::smulh(x(T1), x(A), x(B)));
                    s.i(RegShift::new(ShiftKind::Asr, 63, true)
                        .and_then(|sh| Inst::cmp_shifted(x(T1), x(R), sh)));
                    // Overflow saturates toward the sign of the true product.
                    s.i(Inst::eor_shifted(x(T2), x(A), x(B), none()));
                    sat_by_sign(s, T2, T2);
                    s.i(Inst::csel(x(R), x(R), x(T2), Cond::EQ));
                }
                (ArMode::Sat, false) => {
                    s.i(Inst::umulh(x(T1), x(A), x(B)));
                    s.i(Inst::mul(x(R), x(A), x(B)));
                    s.i(Uimm12Lsl::new(0).and_then(|i| Inst::cmp_imm(x(T1), i)));
                    s.i(Inst::csinv(x(R), x(R), Reg::xzr(), Cond::EQ));
                }
            }
        }
        BinOp::Div | BinOp::Rem => {
            // `div-zero` in every mode (arith.rs: only representability is
            // mode-dependent).
            s.trap_cbz(x(B), TrapKind::DivZero);
            let div = op == BinOp::Div;
            if !signed {
                if div {
                    s.i(Inst::udiv(x(R), x(A), x(B)));
                } else {
                    s.i(Inst::udiv(x(T1), x(A), x(B)));
                    s.i(Inst::msub(x(R), x(T1), x(B), x(A)));
                }
                return;
            }
            if ty.narrow() {
                // Exact in 64 bits: MIN / -1 = 2^(w-1), MIN % -1 = 0.
                if div {
                    s.i(Inst::sdiv(x(R), x(A), x(B)));
                    match mode {
                        ArMode::Trap => fits_or_trap(s, R, ty, TrapKind::Overflow),
                        ArMode::Wrap => canon(s, R, R, ty),
                        ArMode::Sat => clamp_signed(s, ty),
                    }
                } else {
                    s.i(Inst::sdiv(x(T1), x(A), x(B)));
                    if mode == ArMode::Trap {
                        // `MIN % -1` traps `overflow` (Q4): exactly when the
                        // quotient does not fit.
                        fits_or_trap(s, T1, ty, TrapKind::Overflow);
                    }
                    s.i(Inst::msub(x(R), x(T1), x(B), x(A)));
                }
                return;
            }
            // 64-bit signed: the hardware gives MIN / -1 = MIN (wrap) and
            // MIN % -1 = 0, so only Trap (both) and Sat div (MAX) need the
            // detector.
            match (mode, div) {
                (ArMode::Trap, _) => {
                    // [cmn][b.ne +3][negs][b.vs trap] then the division.
                    min_by_minus_one(s, 3);
                    s.trap_if(Cond::VS, TrapKind::Overflow);
                    if div {
                        s.i(Inst::sdiv(x(R), x(A), x(B)));
                    } else {
                        s.i(Inst::sdiv(x(T1), x(A), x(B)));
                        s.i(Inst::msub(x(R), x(T1), x(B), x(A)));
                    }
                }
                (ArMode::Sat, true) => {
                    s.i(Inst::sdiv(x(R), x(A), x(B)));
                    // [cmn][b.ne +4][negs][b.vc +2][movn MAX]
                    min_by_minus_one(s, 4);
                    s.b_cond_local(Cond::VC, 2);
                    mov_imm(s, R, i64::MAX as u64);
                }
                (_, true) => s.i(Inst::sdiv(x(R), x(A), x(B))),
                (_, false) => {
                    s.i(Inst::sdiv(x(T1), x(A), x(B)));
                    s.i(Inst::msub(x(R), x(T1), x(B), x(A)));
                }
            }
        }
    }
}

/// After the count check: `x13` holds the (in-range) count.
fn shift(s: &mut Seq<'_>, op: ShiftOp, mode: ArMode, ty: IntTy) {
    let signed = ty.signed();
    match (op, mode) {
        (ShiftOp::Shr, _) => {
            // Canonical operands make the 64-bit shift exact and canonical.
            s.i(if signed {
                Inst::asrv(x(R), x(A), x(T1))
            } else {
                Inst::lsrv(x(R), x(A), x(T1))
            });
        }
        (ShiftOp::Shl, ArMode::Trap | ArMode::Wrap) => {
            // arith.rs `trap_shl`: only the count traps; the bits wrap.
            s.i(Inst::lslv(x(R), x(A), x(T1)));
            canon(s, R, R, ty);
        }
        (ShiftOp::Shl, ArMode::Sat) => {
            s.i(Inst::lslv(x(R), x(A), x(T1)));
            if ty.narrow() {
                // |a| < 2^32 and count < 32: the 64-bit shift is exact.
                if signed {
                    clamp_signed(s, ty);
                } else {
                    clamp_hi_unsigned(s, ty.hi());
                }
            } else if signed {
                // Exact iff shifting back recovers a; else saturate by sign.
                s.i(Inst::asrv(x(T2), x(R), x(T1)));
                s.i(Inst::cmp_shifted(x(T2), x(A), none()));
                sat_by_sign(s, T3, A);
                s.i(Inst::csel(x(R), x(R), x(T3), Cond::EQ));
            } else {
                s.i(Inst::lsrv(x(T2), x(R), x(T1)));
                s.i(Inst::cmp_shifted(x(T2), x(A), none()));
                s.i(Inst::csinv(x(R), x(R), Reg::xzr(), Cond::EQ));
            }
        }
    }
}

fn neg(s: &mut Seq<'_>, mode: ArMode, ty: IntTy) {
    if ty.narrow() {
        s.i(Inst::neg(x(R), x(A), none()));
        match mode {
            ArMode::Wrap => canon(s, R, R, ty),
            ArMode::Trap => fits_or_trap(s, R, ty, TrapKind::Overflow),
            ArMode::Sat => clamp_signed(s, ty),
        }
        return;
    }
    match mode {
        ArMode::Wrap => s.i(Inst::neg(x(R), x(A), none())),
        ArMode::Trap => {
            s.i(Inst::negs(x(R), x(A), none()));
            s.trap_if(Cond::VS, TrapKind::Overflow);
        }
        ArMode::Sat => {
            // -MIN overflows to MIN; its complement is MAX.
            s.i(Inst::negs(x(R), x(A), none()));
            s.i(Inst::csinv(x(R), x(R), x(R), Cond::VC));
        }
    }
}

fn conv(s: &mut Seq<'_>, op: ConvOp, from: IntTy, to: IntTy) {
    match op {
        ConvOp::Wrap => canon(s, R, A, to),
        ConvOp::Checked => {
            // The value is exactly representable iff its canonical image in
            // `to` is itself, AND (across a sign change) it is not >= 2^63
            // as an unsigned source / negative as a signed source.
            canon(s, R, A, to);
            s.i(Inst::cmp_shifted(x(R), x(A), none()));
            s.trap_if(Cond::NE, TrapKind::CheckedConversion);
            if from.signed() != to.signed() {
                s.trap_tbnz(x(A), 63, TrapKind::CheckedConversion);
            }
        }
        ConvOp::Sat => match (from.signed(), to.signed()) {
            (true, true) => {
                s.i(Inst::mov_reg(x(R), x(A)));
                clamp_signed(s, to);
            }
            (false, false) => {
                s.i(Inst::mov_reg(x(R), x(A)));
                clamp_hi_unsigned(s, to.hi());
            }
            (true, false) => {
                s.i(Inst::mov_reg(x(R), x(A)));
                clamp_zero(s);
                clamp_hi_unsigned(s, to.hi());
            }
            (false, true) => {
                s.i(Inst::mov_reg(x(R), x(A)));
                clamp_hi_unsigned(s, to.hi());
            }
        },
    }
}
