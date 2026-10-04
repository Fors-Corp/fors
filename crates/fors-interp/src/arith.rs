//! Integer and float semantics (design §5.5, §5.6).
//!
//! Every trapping op is computed in 128-bit host width and range-checked
//! against the operand type's bounds, then narrowed. `wrap_*` is
//! two's-complement truncation; `sat_*` clamps; `unchecked_*` wraps (the
//! Miri-mode `ub: unchecked-overflow` report is F6's; F1 just wraps).
//!
//! Owner decisions applied here (design §11.1 Q4, [HOLE-8]/[HOLE-9]):
//! - `MIN / -1` and `MIN % -1` trap `overflow` (representability, not a zero
//!   divisor). `MIN % -1` is mathematically 0, but the design groups both
//!   forms under [HOLE-8] and recommends `overflow` for the pair.
//! - The shift-count condition is exactly `count >= width` (the count is
//!   `u32` by language rule). A wider or signed count is a compile error,
//!   so no other runtime shape exists.
//!
//! Host-word-size discipline (design §5.1): no program-visible value flows
//! through the host word size. This file uses only fixed-width integers.
//! `frem` is implemented in-crate by exact integer long division (design
//! §5.5): invoking a fused multiply-add, the host remainder routine, or
//! the `%` operator on floats anywhere in this crate would make the oracle
//! depend on the host libm / fused ops and is banned (see
//! `no_fma_or_libm_float_rem`).

use fors_fir::ty::PrimKind;
use fors_fmir::op::{ArithMode, CmpPred, TrapKind};

/// A trapping-arithmetic operand type: the eight fixed-width integer types.
/// `Isize`/`Usize` map to their 64-bit equivalents: v0.1's only targets are
/// 64-bit (design §5.1), and `Target` carries no other width.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntKind {
    pub fn from_prim(p: PrimKind) -> Option<IntKind> {
        Some(match p {
            PrimKind::I8 => IntKind::I8,
            PrimKind::I16 => IntKind::I16,
            PrimKind::I32 => IntKind::I32,
            PrimKind::I64 | PrimKind::Isize => IntKind::I64,
            PrimKind::U8 => IntKind::U8,
            PrimKind::U16 => IntKind::U16,
            PrimKind::U32 => IntKind::U32,
            PrimKind::U64 | PrimKind::Usize => IntKind::U64,
            _ => return None,
        })
    }

    /// Bit width of the type.
    pub fn width(self) -> u32 {
        match self {
            IntKind::I8 | IntKind::U8 => 8,
            IntKind::I16 | IntKind::U16 => 16,
            IntKind::I32 | IntKind::U32 => 32,
            IntKind::I64 | IntKind::U64 => 64,
        }
    }

    pub fn signed(self) -> bool {
        match self {
            IntKind::I8 | IntKind::I16 | IntKind::I32 | IntKind::I64 => true,
            IntKind::U8 | IntKind::U16 | IntKind::U32 | IntKind::U64 => false,
        }
    }

    /// Inclusive `(min, max)` as `i128` (every 64-bit bound fits).
    pub fn bounds(self) -> (i128, i128) {
        let w = self.width();
        if self.signed() {
            (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
        } else {
            (0, (1i128 << w) - 1)
        }
    }

    /// The operand bits as a signed `i128` (sign-extended for signed kinds).
    pub fn as_signed(self, bits: u64) -> i128 {
        let w = self.width();
        if w == 64 {
            (bits as i64) as i128
        } else {
            let v = bits & ((1u64 << w) - 1);
            (((v << (64 - w)) as i64) >> (64 - w)) as i128
        }
    }

    /// The operand bits as an unsigned `u128` (masked to width).
    pub fn as_unsigned(self, bits: u64) -> u128 {
        let w = self.width();
        if w == 64 {
            bits as u128
        } else {
            (bits & ((1u64 << w) - 1)) as u128
        }
    }

    /// Narrow a masked value back to the 64-bit slot form (zero-extended for
    /// unsigned, two's-complement low bits for signed: the slot always
    /// carries the raw low `width` bits).
    pub fn narrow(self, masked: u128) -> u64 {
        let w = self.width();
        if w == 64 {
            masked as u64
        } else {
            (masked & ((1u128 << w) - 1)) as u64
        }
    }
}

/// A float operand type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FloatKind {
    F32,
    F64,
}

impl FloatKind {
    pub fn from_prim(p: PrimKind) -> Option<FloatKind> {
        Some(match p {
            PrimKind::F32 => FloatKind::F32,
            PrimKind::F64 => FloatKind::F64,
            _ => return None,
        })
    }

    pub fn bits(self, v: f64) -> u64 {
        match self {
            FloatKind::F32 => (v as f32).to_bits() as u64,
            FloatKind::F64 => v.to_bits(),
        }
    }

    pub fn from_bits(self, bits: u64) -> f64 {
        match self {
            FloatKind::F32 => f32::from_bits(bits as u32) as f64,
            FloatKind::F64 => f64::from_bits(bits),
        }
    }
}

/// A numeric type: integer or float.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NumKind {
    Int(IntKind),
    Float(FloatKind),
}

impl NumKind {
    pub fn from_prim(p: PrimKind) -> Option<NumKind> {
        if let Some(k) = IntKind::from_prim(p) {
            Some(NumKind::Int(k))
        } else {
            FloatKind::from_prim(p).map(NumKind::Float)
        }
    }
}

/// Canonical quiet NaN (design §5.6(5)): sign 0, exponent all ones, quiet
/// bit set, payload zero. Every NaN-producing op yields exactly this, so
/// byte comparison of outputs is total across targets.
pub const CANONICAL_F64_NAN: u64 = 0x7FF8_0000_0000_0000;
pub const CANONICAL_F32_NAN: u32 = 0x7FC0_0000;

fn canon_f64(v: f64) -> u64 {
    if v.is_nan() {
        CANONICAL_F64_NAN
    } else {
        v.to_bits()
    }
}

fn canon_f32(v: f32) -> u64 {
    if v.is_nan() {
        CANONICAL_F32_NAN as u64
    } else {
        v.to_bits() as u64
    }
}

/// Truncating binary integer op in trapping mode.
pub fn trap_binop(
    op: fn(i128, i128) -> Option<i128>,
    uop: fn(u128, u128) -> Option<u128>,
    a: u64,
    b: u64,
    k: IntKind,
) -> Result<u64, TrapKind> {
    if k.signed() {
        let (lo, hi) = k.bounds();
        let r = op(k.as_signed(a), k.as_signed(b)).ok_or(TrapKind::Overflow)?;
        if r < lo || r > hi {
            return Err(TrapKind::Overflow);
        }
        let w = k.width();
        Ok(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        let (_, hi) = k.bounds();
        let r = uop(k.as_unsigned(a), k.as_unsigned(b)).ok_or(TrapKind::Overflow)?;
        // Compare in `u128`: a `u64 * u64` product can reach `2^128 - 2^65 +
        // 1`, and `r as i128` turns every product `>= 2^127` NEGATIVE, which
        // let `(2^63 + 1) * u64::MAX` through untrapped (found by M2-0's
        // native edge table, `docs/design/m2-dev-backend.md` R5 triage:
        // ch03 R2 says it traps).
        if r > hi as u128 {
            return Err(TrapKind::Overflow);
        }
        Ok(k.narrow(r))
    }
}

pub fn trap_add(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    trap_binop(i128::checked_add, u128::checked_add, a, b, k)
}

pub fn trap_sub(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    trap_binop(i128::checked_sub, u128::checked_sub, a, b, k)
}

pub fn trap_mul(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    trap_binop(i128::checked_mul, u128::checked_mul, a, b, k)
}

/// Signed/unsigned division. `0` divisor traps `div-zero`; `MIN / -1` traps
/// `overflow` (design §11.1 Q4).
pub fn trap_div(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        let (lo, _) = k.bounds();
        if x == lo && y == -1 {
            return Err(TrapKind::Overflow);
        }
        let r = x / y;
        let w = k.width();
        Ok(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        let x = k.as_unsigned(a);
        let y = k.as_unsigned(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        Ok(k.narrow(x / y))
    }
}

/// Remainder. `0` divisor traps `div-zero`; `MIN % -1` traps `overflow`
/// (design [HOLE-8]: grouped with `MIN / -1` under the `overflow`
/// recommendation).
pub fn trap_rem(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        let (lo, _) = k.bounds();
        if x == lo && y == -1 {
            return Err(TrapKind::Overflow);
        }
        let r = x % y;
        let w = k.width();
        Ok(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        let x = k.as_unsigned(a);
        let y = k.as_unsigned(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        Ok(k.narrow(x % y))
    }
}

/// Shifts. The ONLY runtime condition is `count >= width` (design §11.1 Q4):
/// the count is read as the raw `u64` bit pattern, so a wrapped-around
/// signed count still traps exactly when its pattern is out of range.
pub fn trap_shl(a: u64, count: u64, k: IntKind) -> Result<u64, TrapKind> {
    let w = k.width();
    if count >= w as u64 {
        return Err(TrapKind::Shift);
    }
    let v = k.as_unsigned(a);
    Ok(k.narrow((v << count) & mask128(w)))
}

/// Right shift: arithmetic for signed kinds, logical for unsigned.
pub fn trap_shr(a: u64, count: u64, k: IntKind) -> Result<u64, TrapKind> {
    let w = k.width();
    if count >= w as u64 {
        return Err(TrapKind::Shift);
    }
    if k.signed() {
        let x = k.as_signed(a);
        Ok(k.narrow(((x >> count) as u128) & mask128(w)))
    } else {
        Ok(k.narrow(k.as_unsigned(a) >> count))
    }
}

fn mask128(w: u32) -> u128 {
    if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
}

/// Negation. Signed `MIN` traps `overflow`; unsigned negation always fits.
pub fn trap_neg(a: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let (lo, hi) = k.bounds();
        let x = k.as_signed(a);
        if x == lo {
            return Err(TrapKind::Overflow);
        }
        let r = -x;
        debug_assert!(r >= lo && r <= hi);
        let w = k.width();
        Ok(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        let w = k.width();
        Ok(k.narrow((0u128.wrapping_sub(k.as_unsigned(a))) & mask128(w)))
    }
}

fn wrap_binop(op: fn(u128, u128) -> u128, a: u64, b: u64, k: IntKind) -> u64 {
    let w = k.width();
    k.narrow(op(k.as_unsigned(a) & mask128(w), k.as_unsigned(b) & mask128(w)) & mask128(w))
}

pub fn wrap_add(a: u64, b: u64, k: IntKind) -> u64 {
    wrap_binop(u128::wrapping_add, a, b, k)
}

pub fn wrap_sub(a: u64, b: u64, k: IntKind) -> u64 {
    wrap_binop(u128::wrapping_sub, a, b, k)
}

pub fn wrap_mul(a: u64, b: u64, k: IntKind) -> u64 {
    wrap_binop(u128::wrapping_mul, a, b, k)
}

/// Wrapping division/remainder: the two overflow cases (`MIN / -1`,
/// `MIN % -1`) yield the wrapped value instead of trapping.
pub fn wrap_div(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        let (lo, _) = k.bounds();
        if x == lo && y == -1 {
            return Ok(k.narrow(lo as u128 & mask128(k.width())));
        }
        let r = x / y;
        let w = k.width();
        Ok(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        trap_div(a, b, k)
    }
}

pub fn wrap_rem(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        let (lo, _) = k.bounds();
        if x == lo && y == -1 {
            return Ok(0);
        }
        let r = x % y;
        let w = k.width();
        Ok(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        trap_rem(a, b, k)
    }
}

/// Wrapping shifts: only a zero divisor traps; an excessive count still
/// traps `shift` (the count rule is mode-independent — only the
/// representability check is mode-dependent).
pub fn wrap_shl(a: u64, count: u64, k: IntKind) -> Result<u64, TrapKind> {
    trap_shl(a, count, k)
}

pub fn wrap_shr(a: u64, count: u64, k: IntKind) -> Result<u64, TrapKind> {
    trap_shr(a, count, k)
}

pub fn wrap_neg(a: u64, k: IntKind) -> u64 {
    if k.signed() {
        let w = k.width();
        k.narrow((0i128.wrapping_sub(k.as_signed(a)) as u128) & mask128(w))
    } else {
        trap_neg(a, k).unwrap_or(0)
    }
}

fn sat_clamp(v: i128, k: IntKind) -> u64 {
    let (lo, hi) = k.bounds();
    let c = v.clamp(lo, hi);
    let w = k.width();
    if w == 64 {
        c as u64
    } else {
        (c as u64) & ((1u64 << w) - 1)
    }
}

pub fn sat_add(a: u64, b: u64, k: IntKind) -> u64 {
    if k.signed() {
        sat_clamp(k.as_signed(a).saturating_add(k.as_signed(b)), k)
    } else {
        // Saturate against the TYPE's max, not the host's: a `u128`
        // saturation followed by narrowing would wrap (the `u64::MAX + 1`
        // case).
        let m = mask128(k.width());
        k.narrow(k.as_unsigned(a).saturating_add(k.as_unsigned(b)).min(m))
    }
}

pub fn sat_sub(a: u64, b: u64, k: IntKind) -> u64 {
    if k.signed() {
        sat_clamp(k.as_signed(a).saturating_sub(k.as_signed(b)), k)
    } else {
        k.narrow(k.as_unsigned(a).saturating_sub(k.as_unsigned(b)))
    }
}

pub fn sat_mul(a: u64, b: u64, k: IntKind) -> u64 {
    if k.signed() {
        sat_clamp(k.as_signed(a).saturating_mul(k.as_signed(b)), k)
    } else {
        let m = mask128(k.width());
        k.narrow(k.as_unsigned(a).saturating_mul(k.as_unsigned(b)).min(m))
    }
}

pub fn sat_div(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        let (lo, _) = k.bounds();
        if x == lo && y == -1 {
            let (_, hi) = k.bounds();
            return Ok(sat_clamp(hi + 1, k));
        }
        Ok(sat_clamp(x / y, k))
    } else {
        trap_div(a, b, k)
    }
}

pub fn sat_rem(a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        if y == 0 {
            return Err(TrapKind::DivZero);
        }
        let (lo, _) = k.bounds();
        if x == lo && y == -1 {
            return Ok(0);
        }
        Ok(sat_clamp(x % y, k))
    } else {
        trap_rem(a, b, k)
    }
}

/// Saturating left shift: the count rule is the same as every shift's
/// (`count >= width` traps, design §11.1 Q4), and the TRUE result
/// `a × 2^count` is clamped to the type's bounds (design §5.5: "`sat_*`
/// clamps to the type's bounds"), so `7i32.sat_shl(31)` is `i32::MAX` and
/// `128u8.sat_shl(1)` is `255` — never the wrapped low bits. The true
/// result fits the host width: `|a| < 2^64` and `count < 64`.
pub fn sat_shl(a: u64, count: u64, k: IntKind) -> Result<u64, TrapKind> {
    let w = k.width();
    if count >= w as u64 {
        return Err(TrapKind::Shift);
    }
    if k.signed() {
        Ok(sat_clamp(k.as_signed(a) << count, k))
    } else {
        let (_, hi) = k.bounds();
        let v = k.as_unsigned(a) << count;
        Ok(k.narrow(v.min(hi as u128)))
    }
}

pub fn sat_shr(a: u64, count: u64, k: IntKind) -> Result<u64, TrapKind> {
    trap_shr(a, count, k)
}

pub fn sat_neg(a: u64, k: IntKind) -> u64 {
    if k.signed() {
        sat_clamp(0i128 - k.as_signed(a), k)
    } else {
        wrap_neg(a, k)
    }
}

/// Dispatches one integer binary op by mode. `div-zero` and `shift` trap in
/// every mode (only representability is mode-dependent); division by zero
/// and an excessive shift count are not representability questions.
pub fn int_binop(op: &str, mode: ArithMode, a: u64, b: u64, k: IntKind) -> Result<u64, TrapKind> {
    match (op, mode) {
        ("add", ArithMode::Trap) => trap_add(a, b, k),
        ("add", ArithMode::Wrap) | ("add", ArithMode::Unchecked) => Ok(wrap_add(a, b, k)),
        ("add", ArithMode::Sat) => Ok(sat_add(a, b, k)),
        ("sub", ArithMode::Trap) => trap_sub(a, b, k),
        ("sub", ArithMode::Wrap) | ("sub", ArithMode::Unchecked) => Ok(wrap_sub(a, b, k)),
        ("sub", ArithMode::Sat) => Ok(sat_sub(a, b, k)),
        ("mul", ArithMode::Trap) => trap_mul(a, b, k),
        ("mul", ArithMode::Wrap) | ("mul", ArithMode::Unchecked) => Ok(wrap_mul(a, b, k)),
        ("mul", ArithMode::Sat) => Ok(sat_mul(a, b, k)),
        ("div", ArithMode::Trap) => trap_div(a, b, k),
        ("div", ArithMode::Wrap) | ("div", ArithMode::Unchecked) => wrap_div(a, b, k),
        ("div", ArithMode::Sat) => sat_div(a, b, k),
        ("rem", ArithMode::Trap) => trap_rem(a, b, k),
        ("rem", ArithMode::Wrap) | ("rem", ArithMode::Unchecked) => wrap_rem(a, b, k),
        ("rem", ArithMode::Sat) => sat_rem(a, b, k),
        ("shl", ArithMode::Sat) => sat_shl(a, b, k),
        ("shl", _) => trap_shl(a, b, k),
        ("shr", _) => trap_shr(a, b, k),
        _ => Err(TrapKind::Overflow),
    }
}

/// Dispatches one integer unary op by mode.
pub fn int_neg(mode: ArithMode, a: u64, k: IntKind) -> Result<u64, TrapKind> {
    match mode {
        ArithMode::Trap => trap_neg(a, k),
        ArithMode::Wrap | ArithMode::Unchecked => Ok(wrap_neg(a, k)),
        ArithMode::Sat => Ok(sat_neg(a, k)),
    }
}

/// Integer comparison. Signed kinds compare two's-complement; unsigned
/// kinds compare zero-extended.
pub fn icmp(a: u64, b: u64, k: IntKind, pred: CmpPred) -> bool {
    if k.signed() {
        let x = k.as_signed(a);
        let y = k.as_signed(b);
        match pred {
            CmpPred::Eq => x == y,
            CmpPred::Ne => x != y,
            CmpPred::Lt => x < y,
            CmpPred::Le => x <= y,
            CmpPred::Gt => x > y,
            CmpPred::Ge => x >= y,
        }
    } else {
        let x = k.as_unsigned(a);
        let y = k.as_unsigned(b);
        match pred {
            CmpPred::Eq => x == y,
            CmpPred::Ne => x != y,
            CmpPred::Lt => x < y,
            CmpPred::Le => x <= y,
            CmpPred::Gt => x > y,
            CmpPred::Ge => x >= y,
        }
    }
}

/// Float comparison: ordered semantics — any ordered predicate on a NaN
/// operand is false, `Ne` is true. (NaN inputs reaching here are already
/// canonical: every op canonicalises.)
pub fn fcmp(a: f64, b: f64, pred: CmpPred) -> bool {
    match pred {
        CmpPred::Eq => a == b,
        CmpPred::Ne => a != b,
        CmpPred::Lt => a < b,
        CmpPred::Le => a <= b,
        CmpPred::Gt => a > b,
        CmpPred::Ge => a >= b,
    }
}

/// Strict float arithmetic (design §5.6): no fused ops, canonical NaN out.
pub fn fadd(a: f64, b: f64, k: FloatKind) -> u64 {
    match k {
        FloatKind::F32 => canon_f32((a as f32) + (b as f32)),
        FloatKind::F64 => canon_f64(a + b),
    }
}

pub fn fsub(a: f64, b: f64, k: FloatKind) -> u64 {
    match k {
        FloatKind::F32 => canon_f32((a as f32) - (b as f32)),
        FloatKind::F64 => canon_f64(a - b),
    }
}

pub fn fmul(a: f64, b: f64, k: FloatKind) -> u64 {
    match k {
        FloatKind::F32 => canon_f32((a as f32) * (b as f32)),
        FloatKind::F64 => canon_f64(a * b),
    }
}

pub fn fdiv(a: f64, b: f64, k: FloatKind) -> u64 {
    match k {
        FloatKind::F32 => canon_f32((a as f32) / (b as f32)),
        FloatKind::F64 => canon_f64(a / b),
    }
}

pub fn fneg(a: f64, k: FloatKind) -> u64 {
    match k {
        FloatKind::F32 => canon_f32(-(a as f32)),
        FloatKind::F64 => canon_f64(-a),
    }
}

/// Exact remainder, implemented in-crate (design §5.5): binary long division
/// on the integer mantissas, so no rounding mode is involved anywhere and
/// the result is bit-exact by construction. Special cases follow the C
/// remainder function: NaN in → canonical NaN; zero divisor → canonical
/// NaN; infinite dividend → canonical NaN; infinite divisor with finite
/// dividend → the dividend; zero dividend → signed zero preserved.
pub fn frem_f64(a: f64, b: f64) -> u64 {
    if a.is_nan() || b.is_nan() {
        return CANONICAL_F64_NAN;
    }
    if b == 0.0 {
        return CANONICAL_F64_NAN;
    }
    if a.is_infinite() {
        return CANONICAL_F64_NAN;
    }
    if b.is_infinite() {
        return a.to_bits();
    }
    if a == 0.0 {
        return a.to_bits();
    }
    frem_soft(
        decompose_f64(a),
        decompose_f64(b),
        a.is_sign_negative(),
        52,
        11,
        1023,
        -1022,
    )
}

/// `f32` remainder: the same exact long division on 24-bit mantissas.
pub fn frem_f32(a: f32, b: f32) -> u64 {
    if a.is_nan() || b.is_nan() {
        return CANONICAL_F32_NAN as u64;
    }
    if b == 0.0 {
        return CANONICAL_F32_NAN as u64;
    }
    if a.is_infinite() {
        return CANONICAL_F32_NAN as u64;
    }
    if b.is_infinite() {
        return (a.to_bits()) as u64;
    }
    if a == 0.0 {
        return (a.to_bits()) as u64;
    }
    frem_soft(
        decompose_f32(a),
        decompose_f32(b),
        a.is_sign_negative(),
        23,
        8,
        127,
        -126,
    )
}

/// A finite nonzero float as `(mantissa, exp)` with value `mantissa × 2^exp`
/// (`mantissa < 2^(man_bits+1)`, possibly denormal).
fn decompose_f64(v: f64) -> (u64, i32) {
    let bits = v.to_bits();
    let field = ((bits >> 52) & 0x7FF) as i32;
    let man = bits & 0xF_FFFF_FFFF_FFFF;
    if field == 0 {
        (man, -1074)
    } else {
        (man | 0x10_0000_0000_0000, field - 1023 - 52)
    }
}

fn decompose_f32(v: f32) -> (u64, i32) {
    let bits = v.to_bits();
    let field = ((bits >> 23) & 0xFF) as i32;
    let man = (bits & 0x7F_FFFF) as u64;
    if field == 0 {
        (man, -149)
    } else {
        (man | 0x80_0000, field - 127 - 23)
    }
}

/// Exact remainder of `ma × 2^ea` modulo `mb × 2^eb`, returned as the bit
/// pattern of a float with a `man_bits`-wide mantissa.
///
/// Both mantissas fit in 53 bits, but the exponent gap can span ~2100, so
/// no fixed-width shift can align them. Instead the remainder is computed
/// at the scale of the finer operand by modular arithmetic, all in `u128`
/// (every factor is below `2^53`, so every product is below `2^106`):
///
/// - `ea ≥ eb`: factor out `2^eb`; the cofactor reduces by `powmod`.
/// - `ea < eb`: the scaled divisor either exceeds the dividend (remainder
///   is the dividend) or fits in 53 bits (direct `%`).
///
/// Nothing ever rounds: the inputs are integers and so is every step.
fn frem_soft(
    (ma, ea): (u64, i32),
    (mb, eb): (u64, i32),
    neg: bool,
    man_bits: u32,
    exp_bits: u32,
    bias: i32,
    emin: i32,
) -> u64 {
    /// `2^e mod m` for `m < 2^53` by binary exponentiation.
    fn powmod(mut e: i32, m: u128) -> u128 {
        let mut base = 2u128 % m;
        let mut acc = 1u128 % m;
        while e > 0 {
            if e & 1 == 1 {
                acc = (acc * base) % m;
            }
            base = (base * base) % m;
            e >>= 1;
        }
        acc
    }
    // `(units, exp)`: the remainder is `units × 2^exp`, `units < 2^53`.
    let (units, exp): (u64, i32) = if ea >= eb {
        let m = mb as u128;
        let r = ((ma as u128 % m) * powmod(ea - eb, m) % m) as u64;
        (r, eb)
    } else if (eb - ea) >= 64 || (mb as u128) << (eb - ea) as u32 > ma as u128 {
        (ma, ea)
    } else {
        let divisor = ((mb as u128) << (eb - ea) as u32) as u64;
        (ma % divisor, ea)
    };
    let sign = (neg as u64) << (man_bits + exp_bits);
    if units == 0 {
        return sign;
    }
    /// Position of the leading bit (`0`-indexed); the argument is nonzero.
    fn lead(x: u64) -> u32 {
        63 - x.leading_zeros()
    }
    // The result value is `units × 2^exp` with `units < 2^53`.
    let exp_true = exp + lead(units) as i32;
    if exp_true >= emin {
        // Normal: strip the leading bit, align the mantissa.
        let field = (exp_true + bias) as u64;
        let mant = (units ^ (1u64 << lead(units))) << (man_bits - lead(units));
        sign | (field << man_bits) | mant
    } else {
        // Subnormal: units of the least subnormal (`2^(emin-man_bits)`)
        // — exact, since the value is below the normal range, and the
        // shift is at most `man_bits` for the same reason.
        let shift = (exp - emin + man_bits as i32) as u32;
        debug_assert!(shift <= man_bits);
        sign | (units << shift)
    }
}

/// Checked conversion (ch03 R6): the exact-representability test.
/// - int → int: the value must lie in the target's bounds.
/// - int → float: always representable (rounding is not lossiness here).
/// - float → int: the value must already be integral AND in range —
///   `3.9 as i32` is *not* exactly representable (that spelling is
///   `trunc_as`, not `as`).
/// - float → float: narrowing traps only when a finite input overflows to
///   infinite; widening always succeeds.
pub fn conv_checked(src_bits: u64, from: NumKind, to: NumKind) -> Result<u64, TrapKind> {
    match (from, to) {
        (NumKind::Int(fk), NumKind::Int(tk)) => {
            let v = if fk.signed() {
                fk.as_signed(src_bits)
            } else {
                fk.as_unsigned(src_bits) as i128
            };
            let (lo, hi) = tk.bounds();
            if v < lo || v > hi {
                return Err(TrapKind::CheckedConversion);
            }
            let w = tk.width();
            Ok(if w == 64 {
                v as u64
            } else {
                (v as u64) & ((1u64 << w) - 1)
            })
        }
        (NumKind::Int(fk), NumKind::Float(tk)) => {
            let v = if fk.signed() {
                fk.as_signed(src_bits) as f64
            } else {
                fk.as_unsigned(src_bits) as f64
            };
            Ok(tk.bits(v))
        }
        (NumKind::Float(fk), NumKind::Int(tk)) => {
            let v = fk.from_bits(src_bits);
            if v.is_nan() || v.is_infinite() {
                return Err(TrapKind::CheckedConversion);
            }
            if v.trunc() != v {
                return Err(TrapKind::CheckedConversion);
            }
            float_bits_in_int_range(v, tk).ok_or(TrapKind::CheckedConversion)
        }
        (NumKind::Float(fk), NumKind::Float(tk)) => {
            let v = fk.from_bits(src_bits);
            match (fk, tk) {
                (FloatKind::F64, FloatKind::F32) => {
                    // ch03 Rule 6: `as` traps unless the value is EXACTLY
                    // representable. Round-tripping through `f32` is that
                    // test for every finite value (`0.1f64 as f32` loses
                    // bits and traps; `0.5` does not), and it also catches
                    // a finite value that overflows to infinity. NaN is
                    // the one value with no "exact" image: it converts to
                    // the canonical `f32` NaN rather than trapping.
                    let r = v as f32;
                    if !v.is_nan() && f64::from(r) != v {
                        return Err(TrapKind::CheckedConversion);
                    }
                    Ok(canon_f32(r))
                }
                _ => Ok(tk.bits(v)),
            }
        }
    }
}

fn float_bits_in_int_range(v: f64, tk: IntKind) -> Option<u64> {
    let w = tk.width();
    if tk.signed() {
        // `lo_f` is exact (a power of two); `hi_f` is the first
        // non-representable value above the max (also exact).
        let lo_f = -(2.0f64.powi(w as i32 - 1));
        let hi_f = 2.0f64.powi(w as i32 - 1);
        if v < lo_f || v >= hi_f {
            return None;
        }
        let r = v as i128;
        Some(if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        })
    } else {
        let hi_f = 2.0f64.powi(w as i32);
        if v < 0.0 || v >= hi_f {
            // `-0.5` truncates to `0`, which IS representable — but the
            // checked form tests the source value, not its truncation.
            // Negative non-integral values already failed above; an
            // integral negative value fails here.
            return None;
        }
        let r = v as u128;
        Some(tk.narrow(r))
    }
}

/// Wrapping conversion: two's-complement truncation for int → int;
/// float → int truncates toward zero with C-like wrap on overflow (the
/// `wrap_as` spelling).
pub fn conv_wrap(src_bits: u64, from: NumKind, to: NumKind) -> u64 {
    match (from, to) {
        (NumKind::Int(fk), NumKind::Int(tk)) => {
            // Two's-complement truncation of the source VALUE modulo
            // `2^w`: a signed source is sign-extended first, so a
            // negative value widened (`(-1i8).wrap_as[i32]()` is `-1`,
            // `(-1i32).wrap_as[u64]()` is `2^64 - 1`) keeps its value's
            // residue, exactly as narrowing keeps the low bits.
            let w = tk.width();
            let v: u128 = if fk.signed() {
                fk.as_signed(src_bits) as u128
            } else {
                fk.as_unsigned(src_bits)
            };
            tk.narrow(v & mask128(w))
        }
        (NumKind::Int(fk), NumKind::Float(tk)) => {
            let v = if fk.signed() {
                fk.as_signed(src_bits) as f64
            } else {
                fk.as_unsigned(src_bits) as f64
            };
            tk.bits(v)
        }
        (NumKind::Float(fk), NumKind::Int(tk)) => trunc_float_to_int(fk.from_bits(src_bits), tk),
        (NumKind::Float(fk), NumKind::Float(tk)) => {
            let v = fk.from_bits(src_bits);
            match (fk, tk) {
                (FloatKind::F64, FloatKind::F32) => canon_f32(v as f32),
                _ => tk.bits(v),
            }
        }
    }
}

/// Truncating conversion (`trunc_as`): int → int wraps; float → int
/// truncates toward zero with Rust-`as` saturation on overflow (NaN → 0,
/// ±infinity and out-of-range → the nearer bound). In-range behaviour is
/// identical to `wrap_as`; only the overflow edge differs.
pub fn conv_trunc(src_bits: u64, from: NumKind, to: NumKind) -> u64 {
    match (from, to) {
        (NumKind::Float(fk), NumKind::Int(tk)) => sat_float_to_int(fk.from_bits(src_bits), tk),
        _ => conv_wrap(src_bits, from, to),
    }
}

/// Saturating conversion (`sat_as`): int → int clamps; float → int clamps
/// with Rust-`as` saturation.
pub fn conv_sat(src_bits: u64, from: NumKind, to: NumKind) -> u64 {
    match (from, to) {
        (NumKind::Int(fk), NumKind::Int(tk)) => {
            let v = if fk.signed() {
                fk.as_signed(src_bits)
            } else {
                fk.as_unsigned(src_bits) as i128
            };
            sat_clamp(v, tk)
        }
        (NumKind::Float(fk), NumKind::Int(tk)) => sat_float_to_int(fk.from_bits(src_bits), tk),
        _ => conv_wrap(src_bits, from, to),
    }
}

/// C-like float → int truncation toward zero, wrapping modulo 2^w. The
/// wrap is computed through the exact in-crate [`frem_f64`] (never the
/// `%` operator, which is banned in this crate): `t mod m` lands in
/// `(-m, m)`, then the sign is folded into `[0, m)`.
fn trunc_float_to_int(v: f64, tk: IntKind) -> u64 {
    if v.is_nan() {
        return 0;
    }
    let w = tk.width();
    let t = v.trunc();
    let m = 2.0f64.powi(w as i32);
    let r = f64::from_bits(frem_f64(t, m));
    let folded = if r < 0.0 { r + m } else { r };
    tk.narrow(folded as u128)
}

/// Rust-`as` float → int saturation: NaN → 0, infinite/out-of-range → the
/// nearer bound, otherwise truncation toward zero.
fn sat_float_to_int(v: f64, tk: IntKind) -> u64 {
    if v.is_nan() {
        return 0;
    }
    let (lo, hi) = tk.bounds();
    let t = v.trunc();
    if t <= lo as f64 {
        return sat_clamp(lo, tk);
    }
    // `hi as f64` rounds UP to the first non-representable value for
    // widths ≥ 53, which is exactly the strict-`>=` edge we want; for
    // narrow widths it is exact and `t == hi` must still saturate rather
    // than fall through to the cast.
    if t >= hi as f64 {
        return sat_clamp(hi, tk);
    }
    let w = tk.width();
    if tk.signed() {
        let r = t as i128;
        if w == 64 {
            r as u64
        } else {
            (r as u64) & ((1u64 << w) - 1)
        }
    } else if t < 0.0 {
        0
    } else {
        tk.narrow(t as u128)
    }
}
