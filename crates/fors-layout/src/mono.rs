//! The ch03 Rule 16 monomorphize-vs-witness decision, size half.
//!
//! ch03 Rule 16 (`docs/spec/03-numerics-determinism.md`): "Monomorphize when
//! instantiation shape is scalar, `<= MONOMORPHIZE_SIZE_MAX` (16) bytes, or
//! the body's instruction count is below the named constant
//! `MONOMORPHIZE_INSTR_THRESHOLD`; otherwise lower via witness table
//! (layout-identical to `dyn T`)". The instantiation shape is `(size, align,
//! pointerness, qualifier, deinit-ness)`; brand arguments are not part of it
//! (ch01 Rule 15e).
//!
//! This module owns the first two disjuncts — the ones a layout answers.
//! The third (instruction count) belongs to whoever holds the callee body:
//! `fors-lower` owns the whole decision (design
//! `docs/design/fmir-interpreter.md` §4.1 [HOLE-5], engineering call E10),
//! computing it from scalar-ness and size here plus the callee's FMIR
//! instruction count, cached by ch03 Rule 17's key. That threshold's numeric
//! value is deferred to whoever first writes std against it (ch03 R16's own
//! rationale; spec README: "`MONOMORPHIZE_INSTR_THRESHOLD` (unset)"), hence
//! [`MONOMORPHIZE_INSTR_THRESHOLD`] is `None` until pinned.

use crate::layout::size_of;
use crate::target::Target;
use crate::ty::Ty;

/// ch03 Rule 16's named bound: instantiations `<= 16` bytes monomorphize.
pub const MONOMORPHIZE_SIZE_MAX: usize = 16;

/// ch03 Rule 16's instruction-count threshold: UNSET (see the module docs).
/// `None` until whoever first writes std against it pins a value; the size
/// half of the decision below does not read it.
pub const MONOMORPHIZE_INSTR_THRESHOLD: Option<u32> = None;

/// ch03 Rule 16's first two disjuncts in scalar form: true when `ty` is
/// scalar (ch09 T0003, [`Ty::is_scalar`]) and its layout is `<= 16` bytes.
/// Every scalar is at most 8 bytes, so this is true for all of them today;
/// it is written against [`MONOMORPHIZE_SIZE_MAX`] rather than that fact so
/// a wider scalar tomorrow re-evaluates instead of silently passing.
pub fn is_scalar_le16(ty: &Ty, target: &Target) -> bool {
    ty.is_scalar() && size_of(ty, target) <= MONOMORPHIZE_SIZE_MAX
}

/// ch03 Rule 16's size half over a precomputed shape: monomorphize when the
/// instantiation is scalar or `<= 16` bytes. The caller ORs the instruction
/// disjunct (`instrs < MONOMORPHIZE_INSTR_THRESHOLD`, once set); `fors-lower`
/// owns that full decision ([HOLE-5]/E10) and ch03 Rule 17's cache key.
pub fn shape_monomorphized(is_scalar: bool, size_bytes: usize) -> bool {
    is_scalar || size_bytes <= MONOMORPHIZE_SIZE_MAX
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::Variant;

    fn t64() -> Target {
        Target::AARCH64_APPLE_DARWIN
    }

    #[test]
    fn every_scalar_is_scalar_le16_on_both_targets() {
        for target in [Target::AARCH64_APPLE_DARWIN, Target::new(32).unwrap()] {
            for ty in [
                Ty::Bool,
                Ty::I8,
                Ty::I16,
                Ty::I32,
                Ty::I64,
                Ty::U8,
                Ty::U16,
                Ty::U32,
                Ty::U64,
                Ty::Isize,
                Ty::Usize,
                Ty::F32,
                Ty::F64,
                Ty::Ptr,
            ] {
                assert!(is_scalar_le16(&ty, &target), "{ty:?}");
                assert!(shape_monomorphized(ty.is_scalar(), size_of(&ty, &target)));
            }
        }
    }

    #[test]
    fn composites_are_not_scalar_le16_even_when_small() {
        let t = t64();
        // Small but not scalar: the size disjunct still monomorphizes them;
        // is_scalar_le16 stays false because the scalar disjunct is false.
        let small = Ty::Struct(vec![Ty::U8, Ty::U8]);
        assert!(!is_scalar_le16(&small, &t));
        assert!(shape_monomorphized(false, size_of(&small, &t)));
        assert!(!Ty::SliceView.is_scalar());
        assert!(!is_scalar_le16(&Ty::SliceView, &t));
    }

    #[test]
    fn sixteen_byte_boundary() {
        // 16 bytes monomorphizes, 17 does not (non-scalar shapes).
        assert!(shape_monomorphized(false, 16));
        assert!(!shape_monomorphized(false, 17));
        let t = t64();
        let at = Ty::Array {
            elem: Box::new(Ty::U8),
            len: 16,
        };
        let over = Ty::Array {
            elem: Box::new(Ty::U8),
            len: 17,
        };
        assert!(shape_monomorphized(at.is_scalar(), size_of(&at, &t)));
        assert!(!shape_monomorphized(over.is_scalar(), size_of(&over, &t)));
        // A scalar flag monomorphizes at any size.
        assert!(shape_monomorphized(true, usize::MAX));
    }

    #[test]
    fn large_composites_go_witness() {
        let t = t64();
        let big = Ty::Array {
            elem: Box::new(Ty::U64),
            len: 3,
        };
        assert_eq!(size_of(&big, &t), 24);
        assert!(!shape_monomorphized(big.is_scalar(), size_of(&big, &t)));
        let e = Ty::Enum {
            variants: vec![Variant::unit(), Variant::of(Ty::U64)],
        };
        assert_eq!(size_of(&e, &t), 16);
        assert!(shape_monomorphized(e.is_scalar(), size_of(&e, &t)));
    }
}
