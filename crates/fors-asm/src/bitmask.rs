//! The AArch64 bitmask-immediate (`N:immr:imms`) encoding used by
//! `AND`/`ORR`/`EOR`/`ANDS` immediate forms.
//!
//! This is deliberately the one piece of this crate implemented as
//! "decode is the spec, encode searches it" rather than two independent
//! derivations that could disagree: `encode_bitmask` brute-forces the
//! (small, fixed) `(N, immr, imms)` space and asks [`decode_bitmask`]
//! whether a candidate reproduces the target value. `decode_bitmask` is a
//! direct transcription of the ARM ARM's `DecodeBitMasks` pseudocode, so
//! there is exactly one place this can be wrong, and it is covered by an
//! exhaustive oracle test (see `tests/`) rather than trusted on inspection.

/// Decodes `(N, immr, imms)` into the 32- or 64-bit pattern it represents,
/// or `None` if the encoding is reserved/unallocated. `reg_size` is 32 or
/// 64; for `reg_size == 32`, `N` must be 0 (the field would otherwise force
/// a 64-bit-only element size), which falls out naturally below because it
/// forces `size == 64 > reg_size`.
pub fn decode_bitmask(n: u8, immr: u8, imms: u8, reg_size: u32) -> Option<u64> {
    debug_assert!(reg_size == 32 || reg_size == 64);
    let n = (n & 1) as u32;
    let immr = (immr as u32) & 0x3f;
    let imms = (imms as u32) & 0x3f;

    // len = HighestSetBit(N:NOT(imms)), a 7-bit concatenation with N as bit 6.
    let concat = (n << 6) | (!imms & 0x3f);
    if concat == 0 {
        return None; // HighestSetBit of an all-zero field is undefined.
    }
    let len = 31 - concat.leading_zeros();
    if len < 1 {
        return None; // element size must be >= 2 (len >= 1).
    }
    let size = 1u32 << len;
    if size > reg_size {
        return None; // only reachable via N=1 in a 32-bit context.
    }
    let levels = size - 1;
    let s = imms & levels;
    let r = immr & levels;
    if s == levels {
        return None; // reserved: would encode an all-ones element.
    }

    // welem: S+1 low bits set, within an `size`-bit field (S <= size-2, so
    // this never sets the top bit and 1u64 << (s+1) never shifts by >=64).
    let welem: u64 = (1u64 << (s + 1)) - 1;
    let telem = ror(welem, r, size);
    Some(replicate(telem, size, reg_size))
}

/// Rotates the low `width` bits of `x` right by `amount` (`amount` need not
/// already be reduced mod `width`). `width` is 2..=64.
fn ror(x: u64, amount: u32, width: u32) -> u64 {
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let x = x & mask;
    let amount = amount % width;
    if amount == 0 {
        x
    } else {
        (x >> amount) | (x << (width - amount)) & mask
    }
}

/// Tiles a `width`-bit pattern across `total` bits (`width` divides `total`,
/// both powers of two, as guaranteed by the bitmask-immediate encoding).
fn replicate(pattern: u64, width: u32, total: u32) -> u64 {
    let mut result = pattern;
    let mut filled = width;
    while filled < total {
        result |= result << filled;
        filled *= 2;
    }
    if total == 64 {
        result
    } else {
        result & ((1u64 << total) - 1)
    }
}

/// Searches for an `(N, immr, imms)` triple that decodes to `value` at the
/// given register size. `value` must already be the target pattern
/// (zero-extended into a `u64` for `reg_size == 32`, i.e. the caller passes
/// `value as u32 as u64`, not a sign-extended 64-bit view of a 32-bit
/// value). Returns `None` for the two patterns that are never encodable
/// (all-zero, all-one) and for anything without a bitmask-immediate form.
pub fn encode_bitmask(value: u64, reg_size: u32) -> Option<(u8, u8, u8)> {
    debug_assert!(reg_size == 32 || reg_size == 64);
    let all_ones = if reg_size == 64 {
        u64::MAX
    } else {
        (1u64 << reg_size) - 1
    };
    if value == 0 || value == all_ones {
        return None;
    }
    let n_choices: &[u8] = if reg_size == 64 { &[1, 0] } else { &[0] };
    for &n in n_choices {
        for immr in 0u8..64 {
            for imms in 0u8..64 {
                if decode_bitmask(n, immr, imms, reg_size) == Some(value) {
                    return Some((n, immr, imms));
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_bit_64() {
        // and x0, x0, #1 : N=1, immr=0, imms=0 (worked example in the docs).
        assert_eq!(encode_bitmask(1, 64), Some((1, 0, 0)));
        assert_eq!(decode_bitmask(1, 0, 0, 64), Some(1));
    }

    #[test]
    fn all_zero_and_all_one_are_unencodable() {
        assert_eq!(encode_bitmask(0, 64), None);
        assert_eq!(encode_bitmask(u64::MAX, 64), None);
        assert_eq!(encode_bitmask(0, 32), None);
        assert_eq!(encode_bitmask(0xFFFF_FFFF, 32), None);
    }

    #[test]
    fn alternating_bits_32() {
        // 0x55555555 = 0b0101...01, element size 2, S=0,R=1 -> N=0.
        let (n, immr, imms) = encode_bitmask(0x5555_5555, 32).expect("encodable");
        assert_eq!(n, 0);
        assert_eq!(decode_bitmask(n, immr, imms, 32), Some(0x5555_5555));
    }

    #[test]
    fn round_trips_every_valid_encoding() {
        // (N, immr, imms) triples that decode successfully vastly
        // outnumber distinct VALUES: `r = immr & levels` and the high bits
        // of `imms` both fold many triples onto the same pattern. The
        // widely-cited "5334" (64-bit) / "2667" (32-bit) counts are of
        // distinct values, so collect into a set rather than counting
        // triples.
        use std::collections::HashSet;
        let mut values_64: HashSet<u64> = HashSet::new();
        for n in [0u8, 1] {
            for immr in 0u8..64 {
                for imms in 0u8..64 {
                    if let Some(v) = decode_bitmask(n, immr, imms, 64) {
                        values_64.insert(v);
                        let (n2, immr2, imms2) = encode_bitmask(v, 64).unwrap_or_else(|| {
                            panic!("value 0x{v:x} from ({n},{immr},{imms}) did not re-encode")
                        });
                        assert_eq!(decode_bitmask(n2, immr2, imms2, 64), Some(v));
                    }
                }
            }
        }
        let mut values_32: HashSet<u32> = HashSet::new();
        for immr in 0u8..64 {
            for imms in 0u8..64 {
                if let Some(v) = decode_bitmask(0, immr, imms, 32) {
                    values_32.insert(v as u32);
                }
            }
        }
        eprintln!(
            "bitmask.rs: {} distinct valid 64-bit values, {} distinct valid 32-bit values",
            values_64.len(),
            values_32.len()
        );
        // Closed-form cross-check, independent of this file's decode/encode
        // logic: for element size e, S ranges over 0..=e-2 (e-1 choices)
        // and each gives e distinct rotations that never collide with
        // another size's (a known property of this encoding), so the
        // count is sum(e*(e-1)) over the element sizes legal at this
        // width. This is what pins the two numbers below: 5334 for 64-bit
        // (e in 2..=64) matches this crate's task brief; the 32-bit count
        // (e in 2..=32) works out to 1302, not the 2667 initially assumed
        // here from memory — caught by this exact cross-check, not trusted
        // on inspection (see the encoder's root-cause notes in the crate
        // docs).
        let closed_form = |max_e: u32| -> u64 {
            let mut total = 0u64;
            let mut e = 2u64;
            while e <= max_e as u64 {
                total += e * (e - 1);
                e *= 2;
            }
            total
        };
        assert_eq!(values_64.len() as u64, closed_form(64));
        assert_eq!(values_32.len() as u64, closed_form(32));
        assert_eq!(
            values_64.len(),
            5334,
            "distinct 64-bit bitmask-immediate count changed"
        );
        assert_eq!(
            values_32.len(),
            1302,
            "distinct 32-bit bitmask-immediate count changed"
        );
    }
}
