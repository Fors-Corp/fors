//! The 8-bit floating-point immediate used by `FMOV <Fd>, #<imm>`
//! (`VFPExpandImm` in the ARM ARM). Same "decode is the spec, encode
//! searches it" shape as `bitmask.rs`: only 256 values of `imm8` exist, so
//! brute-forcing which one (if any) expands to a target bit pattern is
//! cheap and avoids a second, independent derivation of the same table.

use crate::error::EncodeError;
use core::fmt;

/// Expands `imm8` to the 32- or 64-bit float bit pattern it represents.
/// Always succeeds (every `imm8` is valid; this operand only ever fails to
/// *construct* when no `imm8` matches the requested value).
fn expand(imm8: u8, is64: bool) -> u64 {
    let sign = ((imm8 >> 7) & 1) as u64;
    let b = (imm8 >> 6) & 1;
    let cd = ((imm8 >> 4) & 0b11) as u64;
    let efgh = (imm8 & 0xF) as u64;
    if is64 {
        // E=11, F=52. exp = NOT(b):Replicate(b,8):cd (11 bits).
        let not_b = (1 - b as u64) & 1;
        let rep_b: u64 = if b == 1 { 0xFF } else { 0 }; // 8 bits of b
        let exp = (not_b << 10) | (rep_b << 2) | cd;
        let frac = efgh << 48; // 4 bits then 48 zeros = 52 bits
        (sign << 63) | (exp << 52) | frac
    } else {
        // E=8, F=23. exp = NOT(b):Replicate(b,5):cd (8 bits).
        let not_b = (1 - b as u64) & 1;
        let rep_b: u64 = if b == 1 { 0x1F } else { 0 }; // 5 bits of b
        let exp = (not_b << 7) | (rep_b << 2) | cd;
        let frac = efgh << 19; // 4 bits then 19 zeros = 23 bits
        (sign << 31) | (exp << 23) | frac
    }
}

/// A validated `FMOV` 8-bit float immediate, plus the width it was
/// validated for (a `D`-form `FpImm8` cannot be reused as an `S`-form one:
/// the bit pattern it expands to is different).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FpImm8 {
    imm8: u8,
    is64: bool,
    bits: u64,
}

impl FpImm8 {
    /// `bits` is the target IEEE-754 bit pattern (`f32::to_bits()` widened
    /// to `u64`, or `f64::to_bits()`, matching `is64`).
    pub fn from_bits(bits: u64, is64: bool) -> Result<FpImm8, EncodeError> {
        let target = if is64 { bits } else { bits & 0xFFFF_FFFF };
        for imm8 in 0u16..256 {
            let imm8 = imm8 as u8;
            if expand(imm8, is64) == target {
                return Ok(FpImm8 {
                    imm8,
                    is64,
                    bits: target,
                });
            }
        }
        Err(EncodeError::ImmediateOutOfRange {
            what: "FMOV immediate (not one of the 256 representable values)",
            value: target as i64,
        })
    }

    pub fn from_f64(v: f64) -> Result<FpImm8, EncodeError> {
        Self::from_bits(v.to_bits(), true)
    }

    pub fn from_f32(v: f32) -> Result<FpImm8, EncodeError> {
        Self::from_bits(v.to_bits() as u64, false)
    }

    pub(crate) fn encoding(self) -> u32 {
        self.imm8 as u32
    }

    pub fn is64(self) -> bool {
        self.is64
    }

    pub fn bits(self) -> u64 {
        self.bits
    }
}

impl fmt::Display for FpImm8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Print the exact decimal value so the assembler re-derives the
        // same imm8 independently of how we got here.
        if self.is64 {
            write!(f, "#{:?}", f64::from_bits(self.bits))
        } else {
            write!(f, "#{:?}", f32::from_bits(self.bits as u32))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_point_zero() {
        let imm = FpImm8::from_f64(1.0).unwrap();
        assert_eq!(f64::from_bits(imm.bits()), 1.0);
    }

    #[test]
    fn every_imm8_round_trips_both_widths() {
        for imm8 in 0u16..256 {
            let imm8 = imm8 as u8;
            let v64 = expand(imm8, true);
            let back = FpImm8::from_bits(v64, true).unwrap();
            assert_eq!(back.encoding(), imm8 as u32);
            let v32 = expand(imm8, false);
            let back32 = FpImm8::from_bits(v32, false).unwrap();
            assert_eq!(back32.encoding(), imm8 as u32);
        }
    }

    #[test]
    fn arbitrary_double_is_rejected() {
        assert!(FpImm8::from_f64(12345.6789).is_err());
    }
}
