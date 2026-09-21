//! The target a layout is computed for: the pointer width.
//!
//! ch09 Rule 3 (`docs/spec/09-types.md` T0003) gives `isize`/`usize`/`rawptr`
//! "the target pointer" width, so every `usize`-denominated value — a
//! [`crate::Layout`] size, a `Layout.of[T]().size` branch, every comptime
//! result derived from one — is target-dependent. Layout therefore takes an
//! explicit [`Target`] and never reads the host: computing a layout with the
//! host's width would silently break cross-compilation and the comptime memo
//! (design `docs/design/fmir-interpreter.md` §5.1, engineering call E12).
//!
//! v0.1's only targets are `aarch64-apple-darwin` and `x86_64-*`: 64-bit,
//! little-endian. Endianness is pinned here (little) because it is
//! observable — `@memcpy` plus a `Slice[u8]` view of an integer is one line
//! of Fors — rather than inherited from the host.

/// The target pointer width a layout is computed for.
///
/// The only observable width in v0.1 is 64 bits; 32 is accepted so the rule
/// stays total over the widths ch09 Rule 3 admits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Target {
    ptr_bits: u8,
}

impl Target {
    /// `aarch64-apple-darwin`: 64-bit pointers (PLAN §5's pinned dev box).
    pub const AARCH64_APPLE_DARWIN: Target = Target { ptr_bits: 64 };
    /// `x86_64-*`: 64-bit pointers (M5.5's correctness path).
    pub const X86_64_UNKNOWN: Target = Target { ptr_bits: 64 };

    /// The target with `ptr_bits`-bit pointers, or `None` for a width v0.1
    /// does not admit (ch09 Rule 3 knows no other pointer width).
    pub const fn new(ptr_bits: u8) -> Option<Target> {
        match ptr_bits {
            32 | 64 => Some(Target { ptr_bits }),
            _ => None,
        }
    }

    /// The pointer width in bits (32 or 64).
    pub const fn ptr_bits(self) -> u8 {
        self.ptr_bits
    }

    /// The pointer width in bytes (4 or 8).
    pub const fn ptr_bytes(self) -> usize {
        (self.ptr_bits / 8) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pointer_widths_and_rejections() {
        assert_eq!(Target::new(64).unwrap().ptr_bytes(), 8);
        assert_eq!(Target::new(32).unwrap().ptr_bytes(), 4);
        assert_eq!(Target::new(64).unwrap().ptr_bits(), 64);
        assert_eq!(Target::AARCH64_APPLE_DARWIN.ptr_bytes(), 8);
        assert_eq!(Target::X86_64_UNKNOWN.ptr_bytes(), 8);
        assert_eq!(Target::new(0), None);
        assert_eq!(Target::new(16), None);
        assert_eq!(Target::new(128), None);
    }
}
