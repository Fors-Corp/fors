//! Register roles of the dev tier (§3's table, rows "Scratch registers",
//! "Reserved", "Frame", "Trap").
//!
//! CONTRIBUTION POINT (PLAN §5, owner Q7): the scratch set below is the
//! decision point `compiler-architecture.md` names as Marc's
//! (`fors-codegen-dev/src/regs.rs` in that document; it lives here so the
//! backend and the linker read one table). The marked implementation follows
//! the design's recommendation: `x10..x15`, with `x9` kept OUT so a stencil
//! can never overwrite a failure tag.

/// GPR scratch set every stencil may clobber: `x10..=x15`.
pub const SCRATCH: [u8; 6] = [10, 11, 12, 13, 14, 15];

/// The failure tag register (ch02 R4): not scratch, clobbered only by the
/// failure ABI itself.
pub const TAG: u8 = crate::failure::FAILURE_TAG_REG;
/// `x16`/`x17` (IP0/IP1) belong to `fors-link`'s stubs.
pub const IP0: u8 = 16;
pub const IP1: u8 = 17;
/// Apple's platform register: never touched.
pub const PLATFORM: u8 = 18;
/// Frame pointer (the `x29` chain is always valid) and link register.
pub const FP: u8 = 29;
pub const LR: u8 = 30;

/// Registers no stencil may name as a scratch: the tag, the stub pair, the
/// platform register, the frame pointer and the link register. `x19..x28`
/// are callee-saved and unused by the dev tier.
pub const RESERVED: [u8; 6] = [TAG, IP0, IP1, PLATFORM, FP, LR];

/// `brk #(TRAP_BRK_BASE + kind)` is a trap site's one instruction (ch02 R6).
pub const TRAP_BRK_BASE: u16 = 0x4600;

/// ch02 R15's closed list: exactly eight trap kinds, discriminants `0..8`.
pub const TRAP_KIND_COUNT: u16 = 8;

/// The `brk` immediate of trap kind `kind` (a `TrapKind` discriminant).
/// `None` for a kind outside ch02 R15's eight.
pub const fn brk_imm(kind: u16) -> Option<u16> {
    if kind < TRAP_KIND_COUNT {
        Some(TRAP_BRK_BASE + kind)
    } else {
        None
    }
}

/// The trap kind a `brk` immediate encodes, if it is one of the eight.
pub const fn kind_of_brk(imm: u16) -> Option<u16> {
    if imm >= TRAP_BRK_BASE && imm < TRAP_BRK_BASE + TRAP_KIND_COUNT {
        Some(imm - TRAP_BRK_BASE)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scratch_and_reserved_are_disjoint() {
        for r in SCRATCH {
            assert!(!RESERVED.contains(&r), "x{r} is both scratch and reserved");
        }
        assert!(!SCRATCH.contains(&TAG), "x9 must never be scratch");
        assert!(!SCRATCH.contains(&PLATFORM), "x18 is never touched");
    }

    #[test]
    fn brk_immediates_round_trip_for_exactly_eight_kinds() {
        for k in 0..TRAP_KIND_COUNT {
            let imm = brk_imm(k).unwrap();
            assert_eq!(kind_of_brk(imm), Some(k));
        }
        assert_eq!(brk_imm(8), None);
        assert_eq!(kind_of_brk(TRAP_BRK_BASE + 8), None);
        assert_eq!(kind_of_brk(TRAP_BRK_BASE - 1), None);
    }
}
