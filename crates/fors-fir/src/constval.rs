//! Comptime values for const arguments and const patterns (design §4.1,
//! `constval.rs`; spec ch09 R13, ch04 R11-R14): integers, `bool`, `Str`
//! literals, and the *trapping* operators over them.
//!
//! Trapping is the whole point. ch09 R13 requires a const argument to be a
//! closed constant expression "required to fit the parameter's type", and R59
//! forbids any error that could surface only after instantiation — so every
//! operator here returns `None` on overflow, on division or remainder by zero,
//! and on a type mismatch, and the caller turns that `None` into a diagnostic
//! at the declaration. Nothing wraps, nothing saturates, nothing panics.

use fors_index::interner::Symbol;

use crate::ty::PrimKind;

/// One comptime value. `i128` is the widest lane an `i64`/`u64` operand needs
/// for its intermediate results even though ch09 R3 has no 128-bit *type*:
/// `u64::MAX * 2` must be representable long enough to be recognised as not
/// fitting, which is exactly what [`fits`] then rejects.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstValue {
    I(i128),
    B(bool),
    S(Symbol),
}

impl ConstValue {
    pub fn as_int(self) -> Option<i128> {
        match self {
            ConstValue::I(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_bool(self) -> Option<bool> {
        match self {
            ConstValue::B(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_sym(self) -> Option<Symbol> {
        match self {
            ConstValue::S(v) => Some(v),
            _ => None,
        }
    }
}

/// The inclusive range of `p`, or `None` when `p` is not a const-parameter type
/// (ch09 R13: "that type MUST be an integer type or `bool`").
pub fn range_of(p: PrimKind) -> Option<(i128, i128)> {
    let r = match p {
        PrimKind::I8 => (i8::MIN as i128, i8::MAX as i128),
        PrimKind::I16 => (i16::MIN as i128, i16::MAX as i128),
        PrimKind::I32 => (i32::MIN as i128, i32::MAX as i128),
        PrimKind::I64 => (i64::MIN as i128, i64::MAX as i128),
        PrimKind::U8 => (0, u8::MAX as i128),
        PrimKind::U16 => (0, u16::MAX as i128),
        PrimKind::U32 => (0, u32::MAX as i128),
        PrimKind::U64 => (0, u64::MAX as i128),
        // MARC: `isize`/`usize` are the target pointer width (R3) and the
        // target is not known to this crate. 64-bit is assumed, which is the
        // only width the project targets today (aarch64/x86-64); when a 32-bit
        // target lands, this needs the target word size threaded in, and a
        // const argument that fits on one target and not another becomes a
        // per-target diagnostic rather than a signature-level one.
        PrimKind::Isize => (i64::MIN as i128, i64::MAX as i128),
        PrimKind::Usize => (0, u64::MAX as i128),
        _ => return None,
    };
    Some(r)
}

/// Whether `v` fits `p` (R13's "required to fit the parameter's type").
/// `bool` accepts only a [`ConstValue::B`]; `Str` only a [`ConstValue::S`].
pub fn fits(v: ConstValue, p: PrimKind) -> bool {
    match (v, p) {
        (ConstValue::B(_), PrimKind::Bool) => true,
        (ConstValue::S(_), PrimKind::Str) => true,
        (ConstValue::I(n), _) => match range_of(p) {
            Some((lo, hi)) => n >= lo && n <= hi,
            None => false,
        },
        _ => false,
    }
}

macro_rules! int_op {
    ($name:ident, $checked:ident) => {
        pub fn $name(a: ConstValue, b: ConstValue) -> Option<ConstValue> {
            Some(ConstValue::I(a.as_int()?.$checked(b.as_int()?)?))
        }
    };
}

int_op!(add, checked_add);
int_op!(sub, checked_sub);
int_op!(mul, checked_mul);
int_op!(div, checked_div);
int_op!(rem, checked_rem);

pub fn neg(a: ConstValue) -> Option<ConstValue> {
    Some(ConstValue::I(a.as_int()?.checked_neg()?))
}

pub fn bitand(a: ConstValue, b: ConstValue) -> Option<ConstValue> {
    match (a, b) {
        (ConstValue::B(x), ConstValue::B(y)) => Some(ConstValue::B(x && y)),
        _ => Some(ConstValue::I(a.as_int()? & b.as_int()?)),
    }
}

pub fn bitor(a: ConstValue, b: ConstValue) -> Option<ConstValue> {
    match (a, b) {
        (ConstValue::B(x), ConstValue::B(y)) => Some(ConstValue::B(x || y)),
        _ => Some(ConstValue::I(a.as_int()? | b.as_int()?)),
    }
}

pub fn bitxor(a: ConstValue, b: ConstValue) -> Option<ConstValue> {
    match (a, b) {
        (ConstValue::B(x), ConstValue::B(y)) => Some(ConstValue::B(x != y)),
        _ => Some(ConstValue::I(a.as_int()? ^ b.as_int()?)),
    }
}

pub fn not(a: ConstValue) -> Option<ConstValue> {
    match a {
        ConstValue::B(x) => Some(ConstValue::B(!x)),
        ConstValue::I(n) => Some(ConstValue::I(!n)),
        ConstValue::S(_) => None,
    }
}

/// Shifts trap on a negative or out-of-lane shift amount rather than masking
/// it, because a masked shift is a silently different value.
pub fn shl(a: ConstValue, b: ConstValue) -> Option<ConstValue> {
    let n = a.as_int()?;
    let s = u32::try_from(b.as_int()?).ok()?;
    Some(ConstValue::I(n.checked_shl(s)?))
}

pub fn shr(a: ConstValue, b: ConstValue) -> Option<ConstValue> {
    let n = a.as_int()?;
    let s = u32::try_from(b.as_int()?).ok()?;
    Some(ConstValue::I(n.checked_shr(s)?))
}

/// Structural equality. `None` when the two values are of different shapes,
/// which is a type error at the comparison, not `false`.
pub fn eq(a: ConstValue, b: ConstValue) -> Option<bool> {
    match (a, b) {
        (ConstValue::I(x), ConstValue::I(y)) => Some(x == y),
        (ConstValue::B(x), ConstValue::B(y)) => Some(x == y),
        (ConstValue::S(x), ConstValue::S(y)) => Some(x == y),
        _ => None,
    }
}

pub fn lt(a: ConstValue, b: ConstValue) -> Option<bool> {
    Some(a.as_int()? < b.as_int()?)
}

pub fn le(a: ConstValue, b: ConstValue) -> Option<bool> {
    Some(a.as_int()? <= b.as_int()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_traps_instead_of_wrapping() {
        assert_eq!(add(ConstValue::I(1), ConstValue::I(2)), Some(ConstValue::I(3)));
        assert_eq!(add(ConstValue::I(i128::MAX), ConstValue::I(1)), None);
        assert_eq!(div(ConstValue::I(1), ConstValue::I(0)), None);
        assert_eq!(rem(ConstValue::I(1), ConstValue::I(0)), None);
        assert_eq!(neg(ConstValue::I(i128::MIN)), None);
        assert_eq!(shl(ConstValue::I(1), ConstValue::I(-1)), None);
        assert_eq!(shl(ConstValue::I(1), ConstValue::I(4)), Some(ConstValue::I(16)));
    }

    #[test]
    fn fits_is_per_primitive() {
        assert!(fits(ConstValue::I(255), PrimKind::U8));
        assert!(!fits(ConstValue::I(256), PrimKind::U8));
        assert!(!fits(ConstValue::I(-1), PrimKind::U8));
        assert!(fits(ConstValue::I(-128), PrimKind::I8));
        assert!(fits(ConstValue::B(true), PrimKind::Bool));
        assert!(!fits(ConstValue::B(true), PrimKind::U8));
        // R13: a const parameter's type must be an integer type or bool.
        assert!(!fits(ConstValue::I(0), PrimKind::F32));
        assert_eq!(range_of(PrimKind::Str), None);
    }

    #[test]
    fn mixed_shapes_are_errors_not_false() {
        assert_eq!(eq(ConstValue::I(0), ConstValue::B(false)), None);
        assert_eq!(eq(ConstValue::B(false), ConstValue::B(false)), Some(true));
        assert_eq!(lt(ConstValue::B(false), ConstValue::B(true)), None);
    }
}
