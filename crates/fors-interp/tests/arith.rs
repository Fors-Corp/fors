//! Integer, conversion and float-semantics tests (design §5.5, §5.6).
//!
//! The `frem` reference table was generated once from the platform `fmod`
//! (512 pairs: edge cases plus random mantissas across the full exponent
//! range) and is checked in: `frem_matches_reference_table` pins the
//! in-crate implementation bit-for-bit. NaN expectations are normalised to
//! the canonical NaN (design §5.6(5)): payloads are not compared.

use fors_fir::ty::PrimKind;
use fors_fmir::op::{ArithMode, CmpPred, TrapKind};
use fors_interp::arith::{
    CANONICAL_F32_NAN, CANONICAL_F64_NAN, FloatKind, IntKind, NumKind, conv_checked, conv_sat,
    conv_trunc, conv_wrap, fcmp, frem_f32, frem_f64, icmp, int_binop, int_neg,
};

fn ik(p: PrimKind) -> IntKind {
    IntKind::from_prim(p).unwrap()
}

fn nk(p: PrimKind) -> NumKind {
    NumKind::from_prim(p).unwrap()
}

#[test]
fn trap_add_overflow_all_widths() {
    assert_eq!(
        int_binop("add", ArithMode::Trap, 127, 1, ik(PrimKind::I8)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("add", ArithMode::Trap, 0x7FFF_FFFF, 1, ik(PrimKind::I32)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop(
            "add",
            ArithMode::Trap,
            0x7FFF_FFFF_FFFF_FFFF,
            1,
            ik(PrimKind::I64)
        ),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("add", ArithMode::Trap, 0xFF, 1, ik(PrimKind::U8)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("add", ArithMode::Trap, u64::MAX, 1, ik(PrimKind::U64)),
        Err(TrapKind::Overflow)
    );
    // ... but the same sums fit wider types.
    assert_eq!(
        int_binop("add", ArithMode::Trap, 127, 1, ik(PrimKind::I16)),
        Ok(128)
    );
    assert_eq!(
        int_binop("add", ArithMode::Trap, 0xFF, 1, ik(PrimKind::U16)),
        Ok(0x100)
    );
}

#[test]
fn trap_sub_mul_overflow() {
    assert_eq!(
        int_binop("sub", ArithMode::Trap, 0x80, 1, ik(PrimKind::I8)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("sub", ArithMode::Trap, 0, 1, ik(PrimKind::U32)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("mul", ArithMode::Trap, 0x7FFF_FFFF, 2, ik(PrimKind::I32)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("mul", ArithMode::Trap, 6, 7, ik(PrimKind::I32)),
        Ok(42)
    );
}

#[test]
fn div_zero_traps_in_every_mode() {
    for mode in [
        ArithMode::Trap,
        ArithMode::Wrap,
        ArithMode::Sat,
        ArithMode::Unchecked,
    ] {
        assert_eq!(
            int_binop("div", mode, 10, 0, ik(PrimKind::I32)),
            Err(TrapKind::DivZero)
        );
        assert_eq!(
            int_binop("rem", mode, 10, 0, ik(PrimKind::I32)),
            Err(TrapKind::DivZero)
        );
    }
}

#[test]
fn min_div_neg1_and_min_rem_neg1_trap_overflow() {
    // Design §11.1 Q4 ([HOLE-8]): representability, not a zero divisor.
    let min32 = 0x8000_0000u64;
    let neg1_32 = 0xFFFF_FFFFu64;
    assert_eq!(
        int_binop("div", ArithMode::Trap, min32, neg1_32, ik(PrimKind::I32)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("rem", ArithMode::Trap, min32, neg1_32, ik(PrimKind::I32)),
        Err(TrapKind::Overflow)
    );
    let min64 = 0x8000_0000_0000_0000u64;
    assert_eq!(
        int_binop("div", ArithMode::Trap, min64, u64::MAX, ik(PrimKind::I64)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(
        int_binop("rem", ArithMode::Trap, min64, u64::MAX, ik(PrimKind::I64)),
        Err(TrapKind::Overflow)
    );
    // Wrapping mode yields the wrapped value instead.
    assert_eq!(
        int_binop("div", ArithMode::Wrap, min64, u64::MAX, ik(PrimKind::I64)),
        Ok(min64)
    );
    assert_eq!(
        int_binop("rem", ArithMode::Wrap, min64, u64::MAX, ik(PrimKind::I64)),
        Ok(0)
    );
}

#[test]
fn shift_count_rule_is_count_ge_width() {
    // Design §11.1 Q4 ([HOLE-9]): exactly `count >= width`, in every mode.
    for mode in [
        ArithMode::Trap,
        ArithMode::Wrap,
        ArithMode::Sat,
        ArithMode::Unchecked,
    ] {
        assert_eq!(
            int_binop("shl", mode, 1, 8, ik(PrimKind::U8)),
            Err(TrapKind::Shift)
        );
        assert_eq!(int_binop("shl", mode, 1, 7, ik(PrimKind::U8)), Ok(0x80));
        assert_eq!(
            int_binop("shr", mode, 0x80, 8, ik(PrimKind::I8)),
            Err(TrapKind::Shift)
        );
        assert_eq!(
            int_binop("shl", mode, 1, 32, ik(PrimKind::I32)),
            Err(TrapKind::Shift)
        );
        // A count of `width - 1` passes the count rule in every mode; what
        // the RESULT is then depends on the mode: `1 << 31` is `2^31`,
        // out of `i32`'s range, so `sat_` clamps it to `i32::MAX` (design
        // §5.5) while the others keep the low bits (`i32::MIN`).
        assert_eq!(
            int_binop("shl", mode, 1, 31, ik(PrimKind::I32)),
            Ok(if mode == ArithMode::Sat {
                0x7FFF_FFFF
            } else {
                0x8000_0000
            })
        );
    }
    // Arithmetic vs logical right shift follows signedness.
    assert_eq!(
        int_binop("shr", ArithMode::Trap, 0x80, 1, ik(PrimKind::I8)),
        Ok(0xC0)
    );
    assert_eq!(
        int_binop("shr", ArithMode::Trap, 0x80, 1, ik(PrimKind::U8)),
        Ok(0x40)
    );
    // A wrapped-around signed count still traps: -1 as u8 is 255.
    assert_eq!(
        int_binop("shl", ArithMode::Trap, 1, 0xFF, ik(PrimKind::U8)),
        Err(TrapKind::Shift)
    );
}

#[test]
fn neg_traps_on_min_only() {
    assert_eq!(
        int_neg(ArithMode::Trap, 0x80, ik(PrimKind::I8)),
        Err(TrapKind::Overflow)
    );
    assert_eq!(int_neg(ArithMode::Trap, 5, ik(PrimKind::I8)), Ok(0xFB));
    assert_eq!(int_neg(ArithMode::Wrap, 0x80, ik(PrimKind::I8)), Ok(0x80));
    assert_eq!(int_neg(ArithMode::Sat, 0x80, ik(PrimKind::I8)), Ok(0x7F));
}

#[test]
fn wrap_and_sat_modes() {
    assert_eq!(
        int_binop("add", ArithMode::Wrap, 0x7FFF_FFFF, 1, ik(PrimKind::I32)),
        Ok(0x8000_0000)
    );
    assert_eq!(
        int_binop("add", ArithMode::Sat, 0x7FFF_FFFF, 1, ik(PrimKind::I32)),
        Ok(0x7FFF_FFFF)
    );
    assert_eq!(
        int_binop(
            "add",
            ArithMode::Sat,
            0x8000_0000,
            0xFFFF_FFFF,
            ik(PrimKind::I32)
        ),
        Ok(0x8000_0000)
    );
    assert_eq!(
        int_binop("add", ArithMode::Sat, u64::MAX, 1, ik(PrimKind::U64)),
        Ok(u64::MAX)
    );
    assert_eq!(
        int_binop("sub", ArithMode::Sat, 0, 1, ik(PrimKind::U8)),
        Ok(0)
    );
    assert_eq!(
        int_binop("mul", ArithMode::Sat, 200, 200, ik(PrimKind::U8)),
        Ok(255)
    );
    assert_eq!(
        int_binop("mul", ArithMode::Wrap, 200, 200, ik(PrimKind::U8)),
        Ok((200u16 * 200 % 256) as u64)
    );
    assert_eq!(
        int_binop(
            "add",
            ArithMode::Unchecked,
            0x7FFF_FFFF,
            1,
            ik(PrimKind::I32)
        ),
        Ok(0x8000_0000)
    );
}

#[test]
fn checked_conv_exact_accepted_lossy_trapped() {
    // `44u32 as u8`: exact.
    assert_eq!(
        conv_checked(44, nk(PrimKind::U32), nk(PrimKind::U8)),
        Ok(44)
    );
    // `300u32 as u8`: not exactly representable.
    assert_eq!(
        conv_checked(300, nk(PrimKind::U32), nk(PrimKind::U8)),
        Err(TrapKind::CheckedConversion)
    );
    // Signed edges.
    assert_eq!(
        conv_checked(0xFF, nk(PrimKind::U8), nk(PrimKind::I8)),
        Err(TrapKind::CheckedConversion)
    );
    assert_eq!(
        conv_checked(0x7F, nk(PrimKind::U8), nk(PrimKind::I8)),
        Ok(0x7F)
    );
    // Widening is always exact.
    assert_eq!(
        conv_checked(0xFF, nk(PrimKind::U8), nk(PrimKind::U32)),
        Ok(0xFF)
    );
    assert_eq!(
        conv_checked(0xFFFF_FFFF_FFFF_FFFF, nk(PrimKind::I64), nk(PrimKind::I64)),
        Ok(u64::MAX)
    );
}

#[test]
fn wrap_sat_trunc_convs() {
    // `300u32 wrap as u8` == 44.
    assert_eq!(conv_wrap(300, nk(PrimKind::U32), nk(PrimKind::U8)), 44);
    // `300i32 sat as u8` == 255.
    assert_eq!(conv_sat(300, nk(PrimKind::I32), nk(PrimKind::U8)), 255);
    assert_eq!(
        conv_sat(0xFFFF_FFFF_FFFF_FF00, nk(PrimKind::I64), nk(PrimKind::I8)),
        0x80
    );
    // `3.9f64 trunc as i32` == 3.
    let f = 3.9f64.to_bits();
    assert_eq!(conv_trunc(f, nk(PrimKind::F64), nk(PrimKind::I32)), 3);
    assert_eq!(conv_wrap(f, nk(PrimKind::F64), nk(PrimKind::I32)), 3);
    // Negative float truncates toward zero.
    let g = (-3.9f64).to_bits();
    assert_eq!(
        conv_trunc(g, nk(PrimKind::F64), nk(PrimKind::I32)),
        0xFFFF_FFFD
    );
    // Checked float conversion requires an integral in-range value.
    assert_eq!(
        conv_checked(f, nk(PrimKind::F64), nk(PrimKind::I32)),
        Err(TrapKind::CheckedConversion)
    );
    assert_eq!(
        conv_checked(3.0f64.to_bits(), nk(PrimKind::F64), nk(PrimKind::I32)),
        Ok(3)
    );
    assert_eq!(
        conv_checked(f64::NAN.to_bits(), nk(PrimKind::F64), nk(PrimKind::I32)),
        Err(TrapKind::CheckedConversion)
    );
    assert_eq!(
        conv_checked(
            f64::INFINITY.to_bits(),
            nk(PrimKind::F64),
            nk(PrimKind::I32)
        ),
        Err(TrapKind::CheckedConversion)
    );
    // int -> float always converts.
    assert_eq!(
        conv_checked(5, nk(PrimKind::I32), nk(PrimKind::F64)),
        Ok(5.0f64.to_bits())
    );
}

#[test]
fn icmp_respects_signedness() {
    // 0xFF is -1 as i8, 255 as u8.
    assert!(icmp(0xFF, 0, ik(PrimKind::I8), CmpPred::Lt));
    assert!(!icmp(0xFF, 0, ik(PrimKind::U8), CmpPred::Lt));
    assert!(icmp(0xFF, 0, ik(PrimKind::U8), CmpPred::Gt));
    assert!(icmp(42, 42, ik(PrimKind::I64), CmpPred::Eq));
    assert!(icmp(42, 43, ik(PrimKind::I64), CmpPred::Ne));
    assert!(icmp(u64::MAX, 0, ik(PrimKind::U64), CmpPred::Ge));
}

#[test]
fn fcmp_nan_is_unordered() {
    let nan = f64::from_bits(CANONICAL_F64_NAN);
    assert!(!fcmp(nan, 1.0, CmpPred::Eq));
    assert!(fcmp(nan, 1.0, CmpPred::Ne));
    assert!(!fcmp(nan, 1.0, CmpPred::Lt));
    assert!(!fcmp(1.0, nan, CmpPred::Le));
    assert!(fcmp(1.0, 2.0, CmpPred::Lt));
    assert!(fcmp(2.0, 2.0, CmpPred::Le));
}

#[test]
fn nan_results_are_canonical() {
    use fors_interp::arith::{fadd, fdiv, fmul, fneg, fsub};
    let nan = f64::from_bits(CANONICAL_F64_NAN);
    assert_eq!(fadd(nan, 1.0, FloatKind::F64), CANONICAL_F64_NAN);
    assert_eq!(fsub(1.0, nan, FloatKind::F64), CANONICAL_F64_NAN);
    assert_eq!(fmul(nan, nan, FloatKind::F64), CANONICAL_F64_NAN);
    assert_eq!(fdiv(0.0, 0.0, FloatKind::F64), CANONICAL_F64_NAN);
    assert_eq!(fneg(nan, FloatKind::F64), CANONICAL_F64_NAN);
    assert_eq!(frem_f64(nan, 1.0), CANONICAL_F64_NAN);
    assert_eq!(frem_f64(1.0, 0.0), CANONICAL_F64_NAN);
    // A non-canonical payload in never survives: f32 path widens through it.
    let dirty = f64::from_bits(0x7FF8_0000_0000_0001);
    assert_eq!(fadd(dirty, 0.0, FloatKind::F64), CANONICAL_F64_NAN);
    assert_eq!(frem_f32(f32::NAN, 1.0), CANONICAL_F32_NAN as u64);
}

#[test]
fn float_default_no_fma() {
    // Corpus `float-default-no-fma-run-ok`: unfused a*b+c, never the fused
    // value. Computed here through the same strict ops the interpreter uses.
    use fors_interp::arith::{fadd, fmul};
    let a = 1.6394267984578836f64;
    let b = 1.025010755222667f64;
    let c = -1.6804301008195948f64;
    let m = f64::from_bits(fmul(a, b, FloatKind::F64));
    let r = f64::from_bits(fadd(m, c, FloatKind::F64));
    assert_eq!(r.to_bits(), (-2.220446049250313e-16f64).to_bits());
    assert_ne!(r.to_bits(), (-2.9511114736925357e-16f64).to_bits());
}

/// The checked-in reference table: 512 `(a, b, fmod(a, b))` bit triples
/// generated once from the platform `fmod`. NaN expectations normalise to
/// the canonical NaN (payloads are not compared, per design §5.6(5)).
const FREM_TABLE: [(u64, u64, u64); 512] = [
    (0x0000000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x0000000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x0000000000000000, 0x000fd1d7d505cd02, 0x0000000000000000),
    (0x0000000000000000, 0x01a56e1fc2f8f359, 0x0000000000000000),
    (0x0000000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x3ff0000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x3ff8000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x4000000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x400f333333333333, 0x0000000000000000),
    (0x0000000000000000, 0x4016000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x401d000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x4059000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x7e37e43c8800759c, 0x0000000000000000),
    (0x0000000000000000, 0x7fefffffffffffff, 0x0000000000000000),
    (0x0000000000000000, 0x7ff0000000000000, 0x0000000000000000),
    (0x0000000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x0000000000000000, 0xbff0000000000000, 0x0000000000000000),
    (0x0000000000000000, 0xfff0000000000000, 0x0000000000000000),
    (0x0000000000000001, 0x0000000000000000, 0x7ff8000000000000),
    (0x0000000000000001, 0x0000000000000001, 0x0000000000000000),
    (0x0000000000000001, 0x000fd1d7d505cd02, 0x0000000000000001),
    (0x0000000000000001, 0x01a56e1fc2f8f359, 0x0000000000000001),
    (0x0000000000000001, 0x3fe0000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x3ff0000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x3ff8000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x4000000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x400f333333333333, 0x0000000000000001),
    (0x0000000000000001, 0x4016000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x401d000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x4059000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x7e37e43c8800759c, 0x0000000000000001),
    (0x0000000000000001, 0x7fefffffffffffff, 0x0000000000000001),
    (0x0000000000000001, 0x7ff0000000000000, 0x0000000000000001),
    (0x0000000000000001, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x0000000000000001, 0xbff0000000000000, 0x0000000000000001),
    (0x0000000000000001, 0xfff0000000000000, 0x0000000000000001),
    (0x0000000000000020, 0xd4512099906548c4, 0x0000000000000020),
    (0x0000000000002608, 0x5ab091d4ff8873e4, 0x0000000000002608),
    (0x0000000000008cee, 0x6a5202907a913035, 0x0000000000008cee),
    (0x00000000005e1b3a, 0x81d0caffa3e30e36, 0x00000000005e1b3a),
    (0x0000000000666371, 0x07b03b94a8097b82, 0x0000000000666371),
    (0x00000007cd00b2bb, 0xf6ca14c89e55e53a, 0x00000007cd00b2bb),
    (0x0001894b487bd5f0, 0xfddc17a166f2d497, 0x0001894b487bd5f0),
    (0x000b6a0aa3b578da, 0xb47271f2939e9e08, 0x000b6a0aa3b578da),
    (0x000fd1d7d505cd02, 0x0000000000000000, 0x7ff8000000000000),
    (0x000fd1d7d505cd02, 0x0000000000000001, 0x0000000000000000),
    (0x000fd1d7d505cd02, 0x000fd1d7d505cd02, 0x0000000000000000),
    (0x000fd1d7d505cd02, 0x01a56e1fc2f8f359, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x3fe0000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x3ff0000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x3ff8000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x4000000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x400f333333333333, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x4016000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x401d000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x4059000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x7e37e43c8800759c, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x7fefffffffffffff, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x7ff0000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x000fd1d7d505cd02, 0xbff0000000000000, 0x000fd1d7d505cd02),
    (0x000fd1d7d505cd02, 0xfff0000000000000, 0x000fd1d7d505cd02),
    (0x00aff0d0a3e6ad1f, 0xd0f934523a64e97e, 0x00aff0d0a3e6ad1f),
    (0x011f88805fb9eabc, 0x82af6fa16a66aeec, 0x011f88805fb9eabc),
    (0x014b3ad7266811fd, 0x2a92378a1704c03b, 0x014b3ad7266811fd),
    (0x0188a87df396c779, 0x92662cf64ccbee30, 0x0188a87df396c779),
    (0x019bedc159babc20, 0x4035a629220b7a67, 0x019bedc159babc20),
    (0x01a56e1fc2f8f359, 0x0000000000000000, 0x7ff8000000000000),
    (0x01a56e1fc2f8f359, 0x0000000000000001, 0x0000000000000000),
    (0x01a56e1fc2f8f359, 0x000fd1d7d505cd02, 0x000730d67754795e),
    (0x01a56e1fc2f8f359, 0x01a56e1fc2f8f359, 0x0000000000000000),
    (0x01a56e1fc2f8f359, 0x3fe0000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x3ff0000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x3ff8000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x4000000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x400f333333333333, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x4016000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x401d000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x4059000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x7e37e43c8800759c, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x7fefffffffffffff, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x7ff0000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x01a56e1fc2f8f359, 0xbff0000000000000, 0x01a56e1fc2f8f359),
    (0x01a56e1fc2f8f359, 0xfff0000000000000, 0x01a56e1fc2f8f359),
    (0x01ead15bdc35166d, 0x2c49b0f00f854383, 0x01ead15bdc35166d),
    (0x02428a2626798036, 0x96d001bed61cc3fc, 0x02428a2626798036),
    (0x029a4552835e95b1, 0x22cf679402f46c94, 0x029a4552835e95b1),
    (0x033032cb72d671f3, 0xa4e572c48c0ee1a4, 0x033032cb72d671f3),
    (0x03e8b3c567032025, 0x8e3118582aec8d65, 0x03e8b3c567032025),
    (0x0446637f38fa3383, 0xed6df70b5bd80731, 0x0446637f38fa3383),
    (0x05d7516f2a044170, 0x8ce276becfa0a73e, 0x05d7516f2a044170),
    (0x0603e78e6fe0c3a2, 0x8ac5c9a592e06ff6, 0x0603e78e6fe0c3a2),
    (0x06cae475e0ec4848, 0xd3aa3a7c10b807f5, 0x06cae475e0ec4848),
    (0x07c07b221d596ced, 0xe3efc134e3451557, 0x07c07b221d596ced),
    (0x08214482afa86831, 0x5acaf21dcbaac19e, 0x08214482afa86831),
    (0x087e9283c8d07516, 0xbbb3cd5e2a806827, 0x087e9283c8d07516),
    (0x08de9b1ff4dc90b9, 0x7f1d8aa69866e255, 0x08de9b1ff4dc90b9),
    (0x0907bf40dd0af673, 0x844ec8c197dc9f5d, 0x044a418e9fbba2ef),
    (0x0a4bd2332671d9e8, 0x6d4c5f7e2580cd9e, 0x0a4bd2332671d9e8),
    (0x0a7a7ac45b14fd09, 0x3c44a1e12d3c587d, 0x0a7a7ac45b14fd09),
    (0x0b1fbbda846d289b, 0x9deb207afda733d1, 0x0b1fbbda846d289b),
    (0x0bfcfc6fec70540b, 0xf9e233117b36a13b, 0x0bfcfc6fec70540b),
    (0x0c372f4deda050d0, 0x9bd137b222d12193, 0x0c372f4deda050d0),
    (0x0ce832c39f5f0a9b, 0x1f183426d81e8e37, 0x0ce832c39f5f0a9b),
    (0x0cf42380cfd04d94, 0xb851c00057d9e227, 0x0cf42380cfd04d94),
    (0x0d771185d5861740, 0x00002362ad94c0b9, 0x000020fc1b15414e),
    (0x0daf8fb1023c9755, 0xdb6596057c2fa813, 0x0daf8fb1023c9755),
    (0x0e65c1ddcdbb6baf, 0xeb7114d9429860c3, 0x0e65c1ddcdbb6baf),
    (0x0eec799dc1c3f649, 0xab005cb00ab3859b, 0x0eec799dc1c3f649),
    (0x0f1c13ee70ba2cb1, 0xc72dec075a6fd545, 0x0f1c13ee70ba2cb1),
    (0x0f3d26103429516a, 0xaa1d25fbb2c18c97, 0x0f3d26103429516a),
    (0x0f5bbf36149a627c, 0x8a0bfb15ec9a996c, 0x09f8baa0a4541350),
    (0x0f5f1a0397727e9f, 0xddd70f228befd5fb, 0x0f5f1a0397727e9f),
    (0x106d0edc7016297c, 0x8f07b53facd5e48f, 0x0ef28e576ac53190),
    (0x107bdc31af7e4d2a, 0x229e57f54f169068, 0x107bdc31af7e4d2a),
    (0x111e3bd479560132, 0x80b8a4cdd176146a, 0x00b234176d621cc6),
    (0x114e05c6a1cc53a0, 0x69d6f62d8ff3c5f3, 0x114e05c6a1cc53a0),
    (0x12d75047d4e1ceed, 0x90523c60a4c6bbda, 0x1026e1fa1d28c5c0),
    (0x1307b28a1e245d16, 0x766a70a1217d6e17, 0x1307b28a1e245d16),
    (0x13d2f06106558dd4, 0x303e9edab7c80b8f, 0x13d2f06106558dd4),
    (0x14211fe0e10fee6b, 0x99013ca56bba1ccf, 0x14211fe0e10fee6b),
    (0x1487918e8b83d319, 0xc3cb4adec07491ee, 0x1487918e8b83d319),
    (0x15245f8815757316, 0x4e0604fa51416ed7, 0x15245f8815757316),
    (0x15a717332cfbba17, 0x58b0f0c75d6ee98b, 0x15a717332cfbba17),
    (0x16fc6d303fa1edcb, 0x452549d4467af0d7, 0x16fc6d303fa1edcb),
    (0x174d4048836ccb02, 0xae37ca34ccc34b92, 0x174d4048836ccb02),
    (0x1796736bec7fac98, 0x57b6bf3cd2de465d, 0x1796736bec7fac98),
    (0x179dc115d070a065, 0xab21176d08609612, 0x179dc115d070a065),
    (0x17b9216378336067, 0xbe3febd0110520fe, 0x17b9216378336067),
    (0x18cf1d158558d8ef, 0x0555015dbe384c9f, 0x053b307a41ba0e78),
    (0x18dbd607aed2b2d1, 0x8ed9ed24e73b60e9, 0x0eca6aab653f5566),
    (0x18e139973ff4e098, 0x412d44a7fd02b73e, 0x18e139973ff4e098),
    (0x19a06aa17e2e33c5, 0x3d59b9dd914a5356, 0x19a06aa17e2e33c5),
    (0x1a19b5a4337bcd09, 0xdeb77f6b5978964d, 0x1a19b5a4337bcd09),
    (0x1a7f61872756b8e2, 0x4523f58afe82d244, 0x1a7f61872756b8e2),
    (0x1b2f59214c740ad9, 0x194333021e7ab210, 0x1937b77280b1a020),
    (0x1c1a73a7d98a1329, 0xee63061817245d1d, 0x1c1a73a7d98a1329),
    (0x1d4efae1b22fe06f, 0x894971e8646ed9c9, 0x0943d5a3bf39754f),
    (0x1d6343c1878a87c1, 0x56743b2b6c545a8b, 0x1d6343c1878a87c1),
    (0x1dcf9f2439f795c0, 0x18c78be7ba70bc1f, 0x18c1ea0c93bd03e5),
    (0x1e4b19c0462d4f62, 0x0c20a63df40e0890, 0x0c19939ee657ef40),
    (0x1e9ff76643308e0c, 0x8ac922cb29c587db, 0x0a8f80fc3db90720),
    (0x1ebf9e8559996504, 0x42dea70e36ed2cde, 0x1ebf9e8559996504),
    (0x1f14397269c0c096, 0x44054dca14811409, 0x1f14397269c0c096),
    (0x1f6ce2c195490ac4, 0x9ff7a537892be128, 0x1f6ce2c195490ac4),
    (0x203df6add4a82c58, 0xc12c9350c582682a, 0x203df6add4a82c58),
    (0x2070fa726a20fced, 0xacb16d12a9b5fcde, 0x2070fa726a20fced),
    (0x2072f56ff7c5986b, 0x14ebf818f1e58a80, 0x14e774788f8ddf80),
    (0x2087a298f077b348, 0x05a489038e8ced07, 0x058fda431a9d664c),
    (0x20e3eed2626a3d6a, 0x10df43d41705d672, 0x10aac7a1e806f130),
    (0x21934820dd001d12, 0xe69c4d575702a414, 0x21934820dd001d12),
    (0x21bcc6a3214a1243, 0xda05c28758d1ac01, 0x21bcc6a3214a1243),
    (0x223c1e05a3d4a36e, 0xaa6816fe7cd09ab0, 0x223c1e05a3d4a36e),
    (0x233eb59a4c25c9dd, 0x618221fd59bca3be, 0x233eb59a4c25c9dd),
    (0x2417bafcc631e188, 0xe05aac1cd926eaae, 0x2417bafcc631e188),
    (0x243d09fd1175ed24, 0xeb82da739de4edc2, 0x243d09fd1175ed24),
    (0x246e670635f78e45, 0x75d20eaf687764ee, 0x246e670635f78e45),
    (0x2477bddf245554b8, 0x707dea72a189f0d6, 0x2477bddf245554b8),
    (0x24f3c71d787ba3d0, 0xbc4ae4b61371ee3c, 0x24f3c71d787ba3d0),
    (0x256f3434520c0a1f, 0x01f844951bc35207, 0x01f2057697233de9),
    (0x265ed948f129a301, 0x0af4f66a99948cb7, 0x0ae0e5e5ddf2258e),
    (0x27388e9bd499ba62, 0x3f8b4473bd36b719, 0x27388e9bd499ba62),
    (0x27a3597691ebd482, 0x133985b168ef8e4f, 0x131e40deed8dec98),
    (0x27c6bff597792b0a, 0x3ec3176c9cfe08be, 0x27c6bff597792b0a),
    (0x27f637d90f7cded5, 0xe9cff89787be4e05, 0x27f637d90f7cded5),
    (0x284b216b82d02e36, 0xb8fedd79801cde02, 0x284b216b82d02e36),
    (0x2878525075d3a600, 0x727494e5da592ff8, 0x2878525075d3a600),
    (0x291ad5771dbb2a82, 0x642f21b1f461048c, 0x291ad5771dbb2a82),
    (0x29228946d1661070, 0x73d169245170325d, 0x29228946d1661070),
    (0x2952330e51c2fea6, 0x535fd9d4a2d203fa, 0x2952330e51c2fea6),
    (0x295ec2d7cdee3249, 0xaef5374c906f2914, 0x295ec2d7cdee3249),
    (0x29b8efe4a055071f, 0xa0d4583c43734223, 0x20c291852d870cda),
    (0x2adac99379562137, 0x87960dcb29c8991c, 0x07500a227de1a900),
    (0x2ae254693ad82ce0, 0xed4628f37b11a5c7, 0x2ae254693ad82ce0),
    (0x2b4ce126bc04d277, 0xa5bd4011b15d95e3, 0x25b43d0797aabc70),
    (0x2c4318ac14cdebd2, 0x21ed158db0f31027, 0x217913c5d5274800),
    (0x2ce404790bd97e00, 0x03cbead5b53653da, 0x03775ce4458e1d40),
    (0x2d0cee79b9bccd64, 0x70e22fa8cfbb9ed9, 0x2d0cee79b9bccd64),
    (0x2d38de2c7cef2b30, 0x575ed2054a4349c1, 0x2d38de2c7cef2b30),
    (0x2db2f583edc00740, 0xabe14fc364083c3e, 0x2bcdc3622b869a70),
    (0x2e0469847c2e3576, 0xb20aa6b62edd1195, 0x2e0469847c2e3576),
    (0x2e0890d98995dd03, 0xa5b501764c25de71, 0x259f4726c2716824),
    (0x2e0d61c3f52b44d8, 0x059c9e7b1780c681, 0x059a71ab2778977b),
    (0x2f1c96dd571ef3f9, 0x09748eed23a4f4e5, 0x097359a941c9e265),
    (0x2fb5acfe23f6d8e0, 0x00000fa638cfb036, 0x00000698e83cda30),
    (0x2fcbba86c0ab5fb7, 0xdf1eb567c747b80c, 0x2fcbba86c0ab5fb7),
    (0x2ff19abdde6ddf9b, 0x6914deacc854f96d, 0x2ff19abdde6ddf9b),
    (0x30edf1d4261d41d4, 0xab9ce76ba4a4f828, 0x2b9245e20359de60),
    (0x313b7d4cd4e556a4, 0xabe4638757ca7053, 0x2ba75577bf1761a0),
    (0x314373a6987f0b14, 0x3179102b9f520d36, 0x314373a6987f0b14),
    (0x320582313d753545, 0x7534d8a4a6e4098c, 0x320582313d753545),
    (0x32c0b38e2e285a0b, 0x63beae5b4ab97e33, 0x32c0b38e2e285a0b),
    (0x33be833678c2eb13, 0xa34577ba257d12ee, 0x2342f9b9102a16b6),
    (0x34860b9a7f2bee5d, 0x7c142d5b2eb0a5d1, 0x34860b9a7f2bee5d),
    (0x34e4fba6d591fae2, 0xaa2694468f0329d8, 0x29f18b5dfd132d80),
    (0x3509d78084049787, 0x6b482c152797ed87, 0x3509d78084049787),
    (0x3568b38e7b694184, 0xf35841b0b68297c0, 0x3568b38e7b694184),
    (0x35974e20c5e9551c, 0xa9d809e3bf2b813e, 0x29c6358bee2554a4),
    (0x3673ef5775eea1c4, 0xd733dc6a0f65cad3, 0x3673ef5775eea1c4),
    (0x36824365693e0e82, 0xa06579ccbe711ce7, 0x205a0c80473331b0),
    (0x36ba2161646d9d68, 0x5208674de8ec04be, 0x36ba2161646d9d68),
    (0x388d8b155f190774, 0x6025d5d71d34bf56, 0x388d8b155f190774),
    (0x3899f4ce9289d138, 0x5da20505406d34a7, 0x3899f4ce9289d138),
    (0x390940cb9d51312b, 0x708329a694cc5310, 0x390940cb9d51312b),
    (0x390e216a09aed673, 0xf04aae1920ae3b3e, 0x390e216a09aed673),
    (0x3956c040ac0c28f5, 0x3814726a8ea6b14e, 0x37bf168b2c0c2f00),
    (0x396031b7470b614b, 0xd463f1d2f5cd0451, 0x396031b7470b614b),
    (0x397aceb1eee8a56d, 0xbe37a6fe9281a130, 0x397aceb1eee8a56d),
    (0x3a2d5f7efc0bb64e, 0x0000000016230f86, 0x0000000008de05ec),
    (0x3a59be11b69ef713, 0x5206dfbaca2b9d09, 0x3a59be11b69ef713),
    (0x3a8b3a960975549d, 0x23ebd6049592312e, 0x23e193cc9ae63486),
    (0x3ad88d5731501c8f, 0xc3bae2f42cd4a392, 0x3ad88d5731501c8f),
    (0x3b607947c6518499, 0x110ed52a714ba755, 0x10e64a62ea5c6bc8),
    (0x3bcc3ca5a9be6e54, 0x8dd18b03f87ce304, 0x0dbb7ff7da36f180),
    (0x3bf3f3560d238491, 0x5dcb2c54e2e37897, 0x3bf3f3560d238491),
    (0x3cc92839bdb5e9c3, 0x19cccada6567fe1b, 0x19ca8b71991ea1d3),
    (0x3d1911ad4c4e6081, 0x3c92ed2a81c51934, 0x3c59e02766021240),
    (0x3d264f42ba3a4ded, 0x012e0dfac304ff71, 0x0114cd19675e182c),
    (0x3dbf7793d7732897, 0x2d432cd860309a78, 0x2d2ae5fcb755c600),
    (0x3e730047ef92364a, 0x371675b0df943d6c, 0x371332405fda0a9c),
    (0x3ec0f03aa2e04aea, 0x62830d4be3783557, 0x3ec0f03aa2e04aea),
    (0x3f48c158a8bde0cb, 0xd1887456cf1770c2, 0x3f48c158a8bde0cb),
    (0x3f6af745e5a7505d, 0xfc748e0cb7a718b5, 0x3f6af745e5a7505d),
    (0x3f7ec77927c80b94, 0x92ceb14acd786cb6, 0x12b6f1b076b7b3fc),
    (0x3fe0000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x3fe0000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x3fe0000000000000, 0x000fd1d7d505cd02, 0x000f6839c33a87c8),
    (0x3fe0000000000000, 0x01a56e1fc2f8f359, 0x01933550b9c24a66),
    (0x3fe0000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x3fe0000000000000, 0x3ff0000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x3ff8000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x4000000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x400f333333333333, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x4016000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x401d000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x4059000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x7e37e43c8800759c, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x7fefffffffffffff, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x7ff0000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x3fe0000000000000, 0xbff0000000000000, 0x3fe0000000000000),
    (0x3fe0000000000000, 0xfff0000000000000, 0x3fe0000000000000),
    (0x3ff0000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x3ff0000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x3ff0000000000000, 0x000fd1d7d505cd02, 0x000efe9bb16f428e),
    (0x3ff0000000000000, 0x01a56e1fc2f8f359, 0x01a33550b9c24a66),
    (0x3ff0000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x3ff0000000000000, 0x3ff0000000000000, 0x0000000000000000),
    (0x3ff0000000000000, 0x3ff8000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x4000000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x400f333333333333, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x4016000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x401d000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x4059000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7e37e43c8800759c, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7fefffffffffffff, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff0000000000000, 0x3ff0000000000000),
    (0x3ff0000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x3ff0000000000000, 0xbff0000000000000, 0x0000000000000000),
    (0x3ff0000000000000, 0xfff0000000000000, 0x3ff0000000000000),
    (0x3ff8000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x3ff8000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x3ff8000000000000, 0x000fd1d7d505cd02, 0x000e94fd9fa3fd54),
    (0x3ff8000000000000, 0x01a56e1fc2f8f359, 0x018d87654ea9f100),
    (0x3ff8000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x3ff8000000000000, 0x3ff0000000000000, 0x3fe0000000000000),
    (0x3ff8000000000000, 0x3ff8000000000000, 0x0000000000000000),
    (0x3ff8000000000000, 0x4000000000000000, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x400f333333333333, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x4016000000000000, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x401d000000000000, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x4059000000000000, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x7e37e43c8800759c, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x7fefffffffffffff, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x7ff0000000000000, 0x3ff8000000000000),
    (0x3ff8000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x3ff8000000000000, 0xbff0000000000000, 0x3fe0000000000000),
    (0x3ff8000000000000, 0xfff0000000000000, 0x3ff8000000000000),
    (0x4000000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x4000000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x4000000000000000, 0x000fd1d7d505cd02, 0x000e2b5f8dd8b81a),
    (0x4000000000000000, 0x01a56e1fc2f8f359, 0x01a0fc81b08ba173),
    (0x4000000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x4000000000000000, 0x3ff0000000000000, 0x0000000000000000),
    (0x4000000000000000, 0x3ff8000000000000, 0x3fe0000000000000),
    (0x4000000000000000, 0x4000000000000000, 0x0000000000000000),
    (0x4000000000000000, 0x400f333333333333, 0x4000000000000000),
    (0x4000000000000000, 0x4016000000000000, 0x4000000000000000),
    (0x4000000000000000, 0x401d000000000000, 0x4000000000000000),
    (0x4000000000000000, 0x4059000000000000, 0x4000000000000000),
    (0x4000000000000000, 0x7e37e43c8800759c, 0x4000000000000000),
    (0x4000000000000000, 0x7fefffffffffffff, 0x4000000000000000),
    (0x4000000000000000, 0x7ff0000000000000, 0x4000000000000000),
    (0x4000000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x4000000000000000, 0xbff0000000000000, 0x0000000000000000),
    (0x4000000000000000, 0xfff0000000000000, 0x4000000000000000),
    (0x400f333333333333, 0x0000000000000000, 0x7ff8000000000000),
    (0x400f333333333333, 0x0000000000000001, 0x0000000000000000),
    (0x400f333333333333, 0x000fd1d7d505cd02, 0x000ccc962a4ab16c),
    (0x400f333333333333, 0x01a56e1fc2f8f359, 0x01a05ee1f55154ff),
    (0x400f333333333333, 0x3fe0000000000000, 0x3fd9999999999998),
    (0x400f333333333333, 0x3ff0000000000000, 0x3feccccccccccccc),
    (0x400f333333333333, 0x3ff8000000000000, 0x3feccccccccccccc),
    (0x400f333333333333, 0x4000000000000000, 0x3ffe666666666666),
    (0x400f333333333333, 0x400f333333333333, 0x0000000000000000),
    (0x400f333333333333, 0x4016000000000000, 0x400f333333333333),
    (0x400f333333333333, 0x401d000000000000, 0x400f333333333333),
    (0x400f333333333333, 0x4059000000000000, 0x400f333333333333),
    (0x400f333333333333, 0x7e37e43c8800759c, 0x400f333333333333),
    (0x400f333333333333, 0x7fefffffffffffff, 0x400f333333333333),
    (0x400f333333333333, 0x7ff0000000000000, 0x400f333333333333),
    (0x400f333333333333, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x400f333333333333, 0xbff0000000000000, 0x3feccccccccccccc),
    (0x400f333333333333, 0xfff0000000000000, 0x400f333333333333),
    (0x4016000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x4016000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x4016000000000000, 0x000fd1d7d505cd02, 0x000b480d1149d384),
    (0x4016000000000000, 0x01a56e1fc2f8f359, 0x01a3ecbcf1c8cbcd),
    (0x4016000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x4016000000000000, 0x3ff0000000000000, 0x3fe0000000000000),
    (0x4016000000000000, 0x3ff8000000000000, 0x3ff0000000000000),
    (0x4016000000000000, 0x4000000000000000, 0x3ff8000000000000),
    (0x4016000000000000, 0x400f333333333333, 0x3ff999999999999a),
    (0x4016000000000000, 0x4016000000000000, 0x0000000000000000),
    (0x4016000000000000, 0x401d000000000000, 0x4016000000000000),
    (0x4016000000000000, 0x4059000000000000, 0x4016000000000000),
    (0x4016000000000000, 0x7e37e43c8800759c, 0x4016000000000000),
    (0x4016000000000000, 0x7fefffffffffffff, 0x4016000000000000),
    (0x4016000000000000, 0x7ff0000000000000, 0x4016000000000000),
    (0x4016000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x4016000000000000, 0xbff0000000000000, 0x3fe0000000000000),
    (0x4016000000000000, 0xfff0000000000000, 0x4016000000000000),
    (0x401d000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x401d000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x401d000000000000, 0x000fd1d7d505cd02, 0x0001ed77e87f7ab8),
    (0x401d000000000000, 0x01a56e1fc2f8f359, 0x01a564da926760fa),
    (0x401d000000000000, 0x3fe0000000000000, 0x3fd0000000000000),
    (0x401d000000000000, 0x3ff0000000000000, 0x3fd0000000000000),
    (0x401d000000000000, 0x3ff8000000000000, 0x3ff4000000000000),
    (0x401d000000000000, 0x4000000000000000, 0x3ff4000000000000),
    (0x401d000000000000, 0x400f333333333333, 0x400acccccccccccd),
    (0x401d000000000000, 0x4016000000000000, 0x3ffc000000000000),
    (0x401d000000000000, 0x401d000000000000, 0x0000000000000000),
    (0x401d000000000000, 0x4059000000000000, 0x401d000000000000),
    (0x401d000000000000, 0x7e37e43c8800759c, 0x401d000000000000),
    (0x401d000000000000, 0x7fefffffffffffff, 0x401d000000000000),
    (0x401d000000000000, 0x7ff0000000000000, 0x401d000000000000),
    (0x401d000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x401d000000000000, 0xbff0000000000000, 0x3fd0000000000000),
    (0x401d000000000000, 0xfff0000000000000, 0x401d000000000000),
    (0x403c6e0d7a86ae2f, 0x466357a7f1bf7be7, 0x403c6e0d7a86ae2f),
    (0x4059000000000000, 0x0000000000000000, 0x7ff8000000000000),
    (0x4059000000000000, 0x0000000000000001, 0x0000000000000000),
    (0x4059000000000000, 0x000fd1d7d505cd02, 0x000c67911754b8bc),
    (0x4059000000000000, 0x01a56e1fc2f8f359, 0x019b14fb8eb0ebce),
    (0x4059000000000000, 0x3fe0000000000000, 0x0000000000000000),
    (0x4059000000000000, 0x3ff0000000000000, 0x0000000000000000),
    (0x4059000000000000, 0x3ff8000000000000, 0x3ff0000000000000),
    (0x4059000000000000, 0x4000000000000000, 0x0000000000000000),
    (0x4059000000000000, 0x400f333333333333, 0x4004000000000005),
    (0x4059000000000000, 0x4016000000000000, 0x3ff0000000000000),
    (0x4059000000000000, 0x401d000000000000, 0x4017000000000000),
    (0x4059000000000000, 0x4059000000000000, 0x0000000000000000),
    (0x4059000000000000, 0x7e37e43c8800759c, 0x4059000000000000),
    (0x4059000000000000, 0x7fefffffffffffff, 0x4059000000000000),
    (0x4059000000000000, 0x7ff0000000000000, 0x4059000000000000),
    (0x4059000000000000, 0x7ff8000000000000, 0x7ff8000000000000),
    (0x4059000000000000, 0xbff0000000000000, 0x0000000000000000),
    (0x4059000000000000, 0xfff0000000000000, 0x4059000000000000),
    (0x409bc888efab36e6, 0x3cf8a89dc3031158, 0x3cd996d25e3a1f40),
    (0x40df360d30ff30a8, 0xc593a2b0b384b68d, 0x40df360d30ff30a8),
    (0x411bfcddfb655d84, 0x2db18e38ef893b6a, 0x2d725ac88cf625a0),
    (0x415d62303ed83a87, 0x858ff08c1cdef2cc, 0x0585235d359816b8),
    (0x415dfeea9668275e, 0x128f39f0a20465eb, 0x12857df84960f406),
    (0x4204ca13cae7ca90, 0x000000000b9afd77, 0x0000000004bf15bd),
    (0x4231bc903111e1a3, 0xda4e56ee3f2787a1, 0x4231bc903111e1a3),
    (0x4382adb0626b7870, 0x026ea8af944713cb, 0x026c00467bdae1f4),
    (0x43ae3e0ca4d8caa8, 0x2949e384c739b71c, 0x2940061bf8c20e24),
    (0x441745b5016146c8, 0x611e39a446ac31d1, 0x441745b5016146c8),
    (0x4421cc0ab5b0a8f8, 0x87fea643204efd99, 0x07d5beeff7538dc0),
    (0x447bb9cfe6138381, 0x3c5aff5b875d7d46, 0x3c319b91f3627620),
    (0x44bce7ed6a2f0bd0, 0x2af3935e319f7689, 0x2aeff61f371f3700),
    (0x4502630b7506d06d, 0x02e6fff1154d1a61, 0x02d2934cae6720d0),
    (0x4555b2e5e825abc4, 0xfe5ca7d4e2a70b74, 0x4555b2e5e825abc4),
    (0x457855cd6f12c014, 0x592bb8fc3d2677ee, 0x457855cd6f12c014),
    (0x457a705041ccf78c, 0x85f9fa25ac56900d, 0x05d2e07c2e467e40),
    (0x457bb31f69ee6539, 0x54a23bd49c4871df, 0x457bb31f69ee6539),
    (0x45da63c88147f840, 0xd9e9939f004c8f0e, 0x45da63c88147f840),
    (0x466de71f9f97736d, 0x601187f35af162c1, 0x466de71f9f97736d),
    (0x47134b0aabd37809, 0xa57f711ec117f9a6, 0x254209c0c54324b0),
    (0x474081af90e0d912, 0xd6f3a3d606fa4f60, 0x474081af90e0d912),
    (0x477be00c073e8027, 0xe2928f41c1aef85c, 0x477be00c073e8027),
    (0x47bbb17dae4da758, 0x93d3e314d9c88691, 0x1393b5a5492ffab0),
    (0x47ea921fe23fa984, 0x4f53f9b77bb0a86d, 0x47ea921fe23fa984),
    (0x481a4b7872b62433, 0x000000000000cc66, 0x0000000000009cf4),
    (0x482750064adf1592, 0x80000000154f2ee1, 0x00000000035f716b),
    (0x489f803a0da16d34, 0x3a9f6a4fb6f68d1a, 0x3a98dfb59717d0ce),
    (0x48b30197289ed1fa, 0xe6fdea0657ecdbaf, 0x48b30197289ed1fa),
    (0x48f62a4a337559c6, 0xbeeb67b137d00b88, 0x3edda0c10c63b800),
    (0x49424eab9e89d1be, 0x09f3023f5290a39f, 0x09d62fc498a15894),
    (0x49a1f9139a9f8297, 0xe180873a6520ed29, 0x49a1f9139a9f8297),
    (0x49d488dca4a41d02, 0x678379013e915311, 0x49d488dca4a41d02),
    (0x49e25d16f3685bde, 0x104c7dca451b0998, 0x1033e89e89a305e0),
    (0x4a5e757bc8601353, 0x65af93b95a85f5c1, 0x4a5e757bc8601353),
    (0x4ad00c7c817e1e30, 0x90b413059234b42f, 0x108707003af2a070),
    (0x4b59556594f2aca7, 0x21ab495046a9881c, 0x2191681c0b602308),
    (0x4b61491f5d3cae77, 0x8e045d02aa65157b, 0x0df7c755750ae72e),
    (0x4c0a30f3f1a360f8, 0xed31c29cfa07c725, 0x4c0a30f3f1a360f8),
    (0x4c5b4843b208e894, 0x5d1b81b2c299901c, 0x4c5b4843b208e894),
    (0x4c7d12a45aa4761f, 0xd564ef996189ede9, 0x4c7d12a45aa4761f),
    (0x4db6d8a456d6e7c2, 0x06b0f266c16bdc72, 0x06a3bbc3449aa1e8),
    (0x4e1a64ef8e431e6e, 0xa52f99e7810977d1, 0x252e28b86d8bc0b9),
    (0x4e718bc188d007e4, 0xee98f2caa9017c7b, 0x4e718bc188d007e4),
    (0x4ebff24bf3376e5e, 0x8f00da99d624a964, 0x0ed4573a24a2d480),
    (0x4ed559aa8a54d6cc, 0x6cc133f29e09aba2, 0x4ed559aa8a54d6cc),
    (0x4ee4443c1172e1ec, 0x54d2778be73dedd5, 0x4ee4443c1172e1ec),
    (0x4f12986998fd4b63, 0xe00875c252ef234c, 0x4f12986998fd4b63),
    (0x4f45149240383162, 0x3bd58442ca89cb24, 0x3bd18a69ea66b3a8),
    (0x4f55e0ea498afb0a, 0x4dcda4152cd27fb4, 0x4dbab5c4863c7208),
    (0x50b77187404a0dca, 0xcd54876587be3a36, 0x4d40596858b014bc),
    (0x50b816fc6a7f596d, 0x38c1fe62e49ec7f1, 0x38c00b3e1c946c9a),
    (0x513270410f64c96e, 0xd4eef9d968cd7c30, 0x513270410f64c96e),
    (0x515fadaf4eb5a972, 0x9fb54090c9bc9eb6, 0x1fb50f2566ba62d4),
    (0x52c3c880d33227ec, 0x16cdb70eef6ab095, 0x168ee0cda3d2f940),
    (0x52c859f6c03cf89b, 0x7aad1e3d8e6ad162, 0x52c859f6c03cf89b),
    (0x52d80b5d714670f2, 0xe329ee6439526022, 0x52d80b5d714670f2),
    (0x535acb60cbf8af1d, 0xb0786a7e847efd70, 0x3078347738545ee0),
    (0x536465993e839048, 0x37355ecd6a0e1907, 0x371ef1f2a3b8952c),
    (0x54bc386054d44c52, 0x250924d833d276f0, 0x25071b00c33d5af0),
    (0x54db30be795d5850, 0xc4be8266bfb5a8cb, 0x44a7997acf45b862),
    (0x54e3186b11197c67, 0x5e174cd6444f6099, 0x54e3186b11197c67),
    (0x552f1a45bf5a2a48, 0x638ee0a78ab23fed, 0x552f1a45bf5a2a48),
    (0x5553821cfce9c242, 0x8a0e18167df4666f, 0x09fd27fc3c60898e),
    (0x557ccfefca52473c, 0xf6142bf68a8098fa, 0x557ccfefca52473c),
    (0x55926a525092a39e, 0xdf5e8a82b01d445d, 0x55926a525092a39e),
    (0x55e23c0317bb90f6, 0xb5b3ff9507a1a1f0, 0x35a4b4778c87ffe0),
    (0x55f592000c93f54d, 0xc98b681c603bd524, 0x4989967a04110e9c),
    (0x57ac69c52ff71bf8, 0x8e7c782913260665, 0x0e6d25ac1996b670),
    (0x57ecbda5813e3ee2, 0x2d540a1191f25435, 0x2d10a9d597ec7cd0),
    (0x5801f352f5eae620, 0xb13f5ebd5a891770, 0x3136899ab99ae850),
    (0x584c19c6775385dc, 0x6b318a848fd0a7cc, 0x584c19c6775385dc),
    (0x587dbd7be98202c3, 0xcaccfd90b780a239, 0x4aab605a6362c7bc),
    (0x58a21b0dbc6a67cf, 0xd205dc1072c96167, 0x51ea8e3e0e29fa78),
    (0x593b219f9a84bd67, 0x926855493a1dd496, 0x124f95a072442de8),
    (0x5957d46553714059, 0xf11d6c0b81d36689, 0x5957d46553714059),
    (0x5b742196b2d3192a, 0xa1f787cc9ca06165, 0x21d4aaa37c07a3d8),
    (0x5c3ffe637beee8a2, 0xcc9da4f3f4253b75, 0x4c7c6ee1f0939028),
    (0x5e3af31a61838220, 0x5369447997379b1f, 0x53667662dd98b23e),
    (0x5e458968660b12c4, 0xac17405e83b73d4c, 0x2c0a7b2613b718b8),
    (0x5e783193a797d0d7, 0x2dcc6c55b4b38790, 0x2db54213000cd9a0),
    (0x5ed7302a9684efbc, 0xaf5f354f3138bad1, 0x2f3b302a6e1cbb5c),
    (0x5fb6f8009087d347, 0x25b7ca1aaa618685, 0x25b3e2ea33caff04),
    (0x5ffa4cdba818f00f, 0x4f5227c522039f64, 0x4f09563f8a32ef80),
    (0x6010238bb69cd927, 0xe2595d5a4bae3790, 0x6010238bb69cd927),
    (0x6019798f090ab6b4, 0x443000546c2f4010, 0x440e64be77583500),
    (0x6027baec0cdb57de, 0x031281e4d95d229c, 0x030f42c47e4198b8),
    (0x60f4cd45e09fc6ff, 0x7b6aba9cb4d431da, 0x60f4cd45e09fc6ff),
    (0x6172d2bd865401b5, 0x695387367ec28bb4, 0x6172d2bd865401b5),
    (0x621bc1e6aeb9a148, 0x651cf5dd35f61a19, 0x621bc1e6aeb9a148),
    (0x63862fb78aa84df7, 0xdc9b00eeade37770, 0x5c5c6763ee61ab00),
    (0x63af84dc4803cc1d, 0xa1d63220ad02343b, 0x21ce67d320217044),
    (0x63c8d46dfa563411, 0xbd2f57ecb6cf9e12, 0x3d2249a6b034d164),
    (0x642a0412bcb64979, 0x8a642bacb4201e86, 0x0a437768b8caff00),
    (0x64b034b40ddc4bfc, 0x5a30f64f4119ef6a, 0x5a23b1489e244340),
    (0x6553d55980aeb30f, 0xcd78bec5b647770d, 0x4d6abcd27aa158c0),
    (0x65b1f25c5ed53be5, 0x0e1e9a22ac96d4da, 0x0df3ce805dcdad20),
    (0x6670c3896e4ce7cf, 0xc70a9677b7cc3f8e, 0x46f09b826c68cadc),
    (0x66723a7244f78457, 0xcd385a4bab7975bf, 0x4d3183adfae17155),
    (0x66dae7d4a622f8e4, 0x327b69192579be81, 0x32751a95194f584e),
    (0x67281e4a8409ef4e, 0x3410c2b43168f8dc, 0x3400714e3693d2d0),
    (0x673f41d54c9ba21d, 0x915a9f9f0755fa04, 0x114c192ba8dd8b40),
    (0x677ac00880e438a5, 0x4b6b94b1ddaad976, 0x4b60da2762a0fc9c),
    (0x67a62b38b3b7ff64, 0x82c4797a6d665c60, 0x028627d2d077dc00),
    (0x67db48d2c51c18fc, 0x4d08c4da0a00f887, 0x4d064e3158b50b09),
    (0x680e027183a80ff4, 0x800000000000001b, 0x0000000000000002),
    (0x6813b92cf9874cfe, 0x9c4f5638e9232451, 0x1c447803d91c6396),
    (0x690c40985f838962, 0xb7451cbba7497bcb, 0x370605c09312a440),
    (0x6a372baaaacb5ed5, 0xedcb7cfca8be27be, 0x6a372baaaacb5ed5),
    (0x6a50c6652b5b65ea, 0xb748323c9c4b5a9c, 0x3742feced2f51260),
    (0x6a6478e4e3a28dbb, 0x485d8ce7b7944dda, 0x48520b96c7e1f11e),
    (0x6a80411ae761a671, 0x6da84e64cdd56fd0, 0x6a80411ae761a671),
    (0x6abc952f3895de25, 0x3c601ac36756c67f, 0x3c47f22d69e859a4),
    (0x6ac8113d3f84b0a3, 0x704850091151f77e, 0x6ac8113d3f84b0a3),
    (0x6b71ee01c2ec20b3, 0x139a0da0430f8ea4, 0x1376cf783c988190),
    (0x6c41bd0bb418011c, 0x119c9217c2efb1ff, 0x1196d1596cc086bc),
    (0x6d0113d4cf48fc87, 0x1aa91eb1f84d2357, 0x1aa1e2f8dee77f0a),
    (0x6d306cf9761af616, 0x9c168790002b0a57, 0x1bf9bb9dcbe71338),
    (0x6d9fa173e6a545df, 0x35dc21439f1bcd2e, 0x35d548ef2e198210),
    (0x6e9dea2872f73a4d, 0xe2580980b07240d1, 0x62449026c52beb16),
    (0x6f8112b065f7789d, 0x2e465d0da326daa6, 0x2e34d23b2ec93bc8),
    (0x6f9188a986ac8359, 0x22fd1af6421c1408, 0x22f0d2fcff6f84b8),
    (0x6fedb4b368d04dff, 0x394b39367f86bb64, 0x394539492e31201c),
    (0x71971aece5d00e90, 0x5f2e73b206cb3963, 0x5f26a4d77fc32920),
    (0x71b268af2a2227a4, 0x006e7572fb2470c5, 0x0032a1c75105cd50),
    (0x73171839222134dc, 0xea444d002ae6284a, 0x6a403b83e7b34cc8),
    (0x743c82b533d5275f, 0x36bcda2d1328903f, 0x36b267874f69caa0),
    (0x74cd29da97275f3f, 0x72f575139b6d9ba1, 0x72eca391e8ccb470),
    (0x752c8dbe15fbdfd4, 0x9d1955580e85eaa5, 0x1d01fd91e3a03792),
    (0x75ca1112c2744ecb, 0x4facf59799f46e2d, 0x4f807c029cf89f1c),
    (0x760af5dc700718b4, 0x840ce23c9c45017f, 0x03b321f7b6587620),
    (0x760ce7bc25a77d92, 0x45bf5e4336be1211, 0x4596af2e3964b0e0),
    (0x765dfb1491ff0e14, 0x8d128caa3146d194, 0x0d1082f058984cd4),
    (0x769000c94a7007d5, 0xb6b201f94b78f83c, 0x367be18596d9de00),
    (0x76931548ef55388c, 0xcffb8859e539e422, 0x4ff19cc65781f2e0),
    (0x76ca45b1f6f3b118, 0x329666577c3247d2, 0x328921d6edba5880),
    (0x76fdc4480b661b0f, 0x37efe8ff396dfdf8, 0x37c2b0fdc0c735a0),
    (0x77666621b679596b, 0x939bce56e3d9bd03, 0x138b784696823b44),
    (0x777bcb1bfb0d158d, 0x0a47499a7e74ba21, 0x0a403fe5f7298eee),
    (0x7794bf9c6c0686d1, 0x3e30815d1e3e0539, 0x3e2913048bfe4946),
    (0x784056fa73dcc9c2, 0xe0d0067b94248bcf, 0x6083fd1f728d20c0),
    (0x7852eb35ca04eb12, 0xe808857de6510d24, 0x680014d7b6263840),
];

#[test]
fn frem_matches_reference_table() {
    for (i, &(a, b, expected)) in FREM_TABLE.iter().enumerate() {
        let got = frem_f64(f64::from_bits(a), f64::from_bits(b));
        let want = if f64::from_bits(expected).is_nan() {
            CANONICAL_F64_NAN
        } else {
            expected
        };
        assert_eq!(got, want, "pair {i}: frem({a:#x}, {b:#x})");
    }
}

#[test]
fn frem_matches_int_remainder_on_integral_values() {
    // For integral operands the float remainder is exactly the integer
    // remainder — 4000 exact pairs with no libm in the loop.
    // All operands are exactly representable: above 2^53 the `as f64`
    // conversion itself rounds, so the comparison would test the
    // conversion, not the remainder.
    for a in [0u64, 1, 2, 7, 17, 100, 1000, (1 << 52) + 1, (1 << 53) - 1] {
        for b in [1u64, 2, 3, 5, 7, 16, 100] {
            let got = frem_f64(a as f64, b as f64);
            assert_eq!(f64::from_bits(got), (a % b) as f64, "frem({a}, {b})");
        }
    }
    for a in [-17i64, -1, 0, 1, 17, 100] {
        for b in [-7i64, -1, 1, 5] {
            if b == 0 {
                continue;
            }
            let got = frem_f64(a as f64, b as f64);
            // Rust `%` on integers matches C `fmod` sign rules here
            // (remainder takes the dividend's sign), and every value is
            // exactly representable.
            assert_eq!(f64::from_bits(got), (a % b) as f64, "frem({a}, {b})");
        }
    }
}

#[test]
fn frem_f32_exact_pairs_and_properties() {
    // Hand-checked exact pairs.
    let cases: [(f32, f32, f32); 10] = [
        (5.5, 2.0, 1.5),
        (7.25, 1.5, 1.25),
        (-7.25, 1.5, -1.25),
        (7.25, -1.5, 1.25),
        (1.0, 2.0, 1.0),
        (0.0, 1.0, 0.0),
        (17.0, 5.0, 2.0),
        (100.0, 3.0, 1.0),
        (0.5, 0.25, 0.0),
        (3.0, 1.5, 0.0),
    ];
    for (a, b, want) in cases {
        assert_eq!(frem_f32(a, b), want.to_bits() as u64, "frem_f32({a}, {b})");
    }
    // Properties over integral values: exact, sign-correct, bounded.
    for a in 0u32..200 {
        for b in [1u32, 2, 3, 7, 13] {
            let got = f32::from_bits(frem_f32(a as f32, b as f32) as u32);
            assert_eq!(got, (a % b) as f32, "frem_f32({a}, {b})");
        }
    }
}

#[test]
fn wrap_and_trunc_as_widen_a_negative_with_its_sign() {
    // `wrap_as` is the source VALUE modulo `2^w` (two's-complement
    // truncation), so widening a negative keeps its value: `(-1i8)
    // .wrap_as[i32]()` is `-1`, not `255`; `(-1i32).wrap_as[u64]()` is
    // `2^64 - 1`, not `2^32 - 1`.
    assert_eq!(
        conv_wrap(0xFF, nk(PrimKind::I8), nk(PrimKind::I32)),
        0xFFFF_FFFF
    );
    assert_eq!(
        conv_wrap(0xFFFF_FFFF, nk(PrimKind::I32), nk(PrimKind::U64)),
        u64::MAX
    );
    assert_eq!(
        conv_trunc(0xFFFF_FFFB, nk(PrimKind::I32), nk(PrimKind::I64)),
        (-5i64) as u64
    );
    // An unsigned source still zero-extends.
    assert_eq!(conv_wrap(0xFF, nk(PrimKind::U8), nk(PrimKind::I32)), 0xFF);
    // Narrowing is unchanged: the low bits.
    assert_eq!(conv_wrap(300, nk(PrimKind::U32), nk(PrimKind::U8)), 44);
}

#[test]
fn sat_shl_clamps_the_true_result() {
    // design §5.5: `sat_*` clamps to the type's bounds; the count rule
    // (`count >= width` traps) is mode-independent (design §11.1 Q4).
    assert_eq!(
        int_binop("shl", ArithMode::Sat, 7, 31, ik(PrimKind::I32)),
        Ok(0x7FFF_FFFF)
    );
    assert_eq!(
        int_binop("shl", ArithMode::Sat, 0xFFFF_FFFF, 1, ik(PrimKind::I32)),
        Ok(0xFFFF_FFFE)
    );
    assert_eq!(
        int_binop("shl", ArithMode::Sat, 0x8000_0000, 1, ik(PrimKind::I32)),
        Ok(0x8000_0000)
    );
    assert_eq!(
        int_binop("shl", ArithMode::Sat, 128, 1, ik(PrimKind::U8)),
        Ok(255)
    );
    assert_eq!(
        int_binop("shl", ArithMode::Sat, 3, 2, ik(PrimKind::U8)),
        Ok(12)
    );
    assert_eq!(
        int_binop("shl", ArithMode::Sat, 1, 64, ik(PrimKind::U64)),
        Err(TrapKind::Shift)
    );
    // `wrap_shl` keeps the low bits.
    assert_eq!(
        int_binop("shl", ArithMode::Wrap, 128, 1, ik(PrimKind::U8)),
        Ok(0)
    );
}

#[test]
fn checked_f64_to_f32_traps_unless_exact() {
    // ch03 Rule 6: `as` traps if the value is not exactly representable.
    assert_eq!(
        conv_checked(0.1f64.to_bits(), nk(PrimKind::F64), nk(PrimKind::F32)),
        Err(TrapKind::CheckedConversion)
    );
    assert_eq!(
        conv_checked(0.5f64.to_bits(), nk(PrimKind::F64), nk(PrimKind::F32)),
        Ok(0.5f32.to_bits() as u64)
    );
    assert_eq!(
        conv_checked(1e300f64.to_bits(), nk(PrimKind::F64), nk(PrimKind::F32)),
        Err(TrapKind::CheckedConversion)
    );
    assert_eq!(
        conv_checked(
            f64::INFINITY.to_bits(),
            nk(PrimKind::F64),
            nk(PrimKind::F32)
        ),
        Ok(f32::INFINITY.to_bits() as u64)
    );
    assert_eq!(
        conv_checked(f64::NAN.to_bits(), nk(PrimKind::F64), nk(PrimKind::F32)),
        Ok(CANONICAL_F32_NAN as u64)
    );
}
