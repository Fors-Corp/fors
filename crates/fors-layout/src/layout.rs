//! The Q1 layout rule and the `Layout` surface.
//!
//! Owner decision Q1 (`docs/design/fmir-interpreter.md` §11.1, [HOLE-6]):
//! fields in **declaration order** with natural alignment and no reordering
//! (so `soa struct` and FFI stay predictable), `align <= MEM_MAX_ALIGN =
//! 16`, the enum discriminant the smallest unsigned type fitting the variant
//! count, the payload at the first suitably aligned offset. This module is
//! that paragraph as code: [`layout_of`] and friends implement it for every
//! [`Ty`](crate::Ty), and the C-table tests below diff the struct rule
//! against `clang` on the C-equivalent structs (risk R3's retiring
//! experiment: where they agree, the rule is also the FFI rule).
//!
//! The `Layout` surface mirrors ch10 Rule S0013 (`docs/spec/10-std.md`):
//! [`Layout`] has the same two `pub` fields (`size`, `align`), [`Layout::array`]
//! raises [`LayoutError::TooLarge`] exactly where `Layout.array[T](n)` raises
//! `AllocError.too_large`, and [`validate_align`] enforces the "power of two
//! and at most `MEM_MAX_ALIGN`" legality condition whose violation makes an
//! allocator raise `AllocError.unsupported_align`.
//!
//! # Examples
//!
//! ```
//! use fors_layout::{Target, Ty, layout_of};
//!
//! let t = Target::AARCH64_APPLE_DARWIN;
//! let s = Ty::Struct(vec![Ty::U8, Ty::U32]);
//! let l = layout_of(&s, &t);
//! assert_eq!((l.size, l.align), (8, 4));
//! ```

use crate::target::Target;
use crate::ty::{Ty, Variant};

/// ch10 S0013's named constant: no legal alignment exceeds 16 "until
/// measured" (also `docs/spec/PACK.md` D0013 and `10-std.md` §"Tunables").
pub const MEM_MAX_ALIGN: usize = 16;

/// The std `Layout` value (ch10 S0013): `{ pub size: usize, pub align: usize }`.
///
/// `align` is always a power of two and at most [`MEM_MAX_ALIGN`]; the only
/// constructors are [`layout_of`]/[`struct_layout_of`]/[`enum_layout_of`] and
/// [`Layout::array`], which all compute it, so an illegal value is
/// impossible to construct — exactly S0013's invariant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Layout {
    /// The size in bytes, including tail padding.
    pub size: usize,
    /// The alignment in bytes: a power of two, at most [`MEM_MAX_ALIGN`].
    pub align: usize,
}

impl Layout {
    /// `Layout.array[T](n)` (ch10 S0013): `n` consecutive copies of `self`.
    ///
    /// Raises [`LayoutError::TooLarge`] where the spec raises
    /// `AllocError.too_large` — when `n * size` overflows `usize` — so no
    /// allocation path through this constructor can overflow silently.
    pub fn array(&self, n: usize) -> Result<Layout, LayoutError> {
        let size = self.size.checked_mul(n).ok_or(LayoutError::TooLarge)?;
        Ok(Layout {
            size,
            align: self.align,
        })
    }
}

/// The spec error this crate's fallible paths report, mapped to ch10
/// S0007's `AllocError` variants: [`LayoutError::TooLarge`] is
/// `AllocError.too_large`, [`LayoutError::UnsupportedAlign`] is
/// `AllocError.unsupported_align`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LayoutError {
    /// `n * size` overflowed `usize` (ch10 S0013, `Layout.array`).
    TooLarge,
    /// `align` is not a power of two or exceeds [`MEM_MAX_ALIGN`] (ch10 S0013).
    UnsupportedAlign,
}

/// The S0013 legality condition: `align` MUST be a power of two and at most
/// [`MEM_MAX_ALIGN`]. An allocator that cannot satisfy a legal `align` must
/// raise `AllocError.unsupported_align`; this check decides which side of
/// that line a value falls on.
pub fn validate_align(align: usize) -> Result<(), LayoutError> {
    if align.is_power_of_two() && align <= MEM_MAX_ALIGN {
        Ok(())
    } else {
        Err(LayoutError::UnsupportedAlign)
    }
}

/// Round `off` up to a multiple of `align` (`align` a power of two, >= 1).
fn align_up(off: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two() && align >= 1);
    let mask = align - 1;
    off.checked_add(mask).map_or(usize::MAX, |s| s & !mask)
}

/// Checked add that saturates: struct/enum nesting of a gigantic [`Ty::Array`]
/// cannot overflow the counter. The spec's only mandated overflow report is
/// [`Layout::array`]'s `TooLarge`; the infallible queries saturate instead of
/// panicking on inputs no allocator could ever back.
fn sat_add(a: usize, b: usize) -> usize {
    a.saturating_add(b)
}

/// The layout of `ty` on `target`: Q1's rule as a function.
///
/// Scalars take their natural size/align (ch09 T0003); structs, tuples and
/// arrays follow [`struct_layout_of`] and [`Layout::array`]; enums follow
/// [`enum_layout_of`].
pub fn layout_of(ty: &Ty, target: &Target) -> Layout {
    match ty {
        Ty::Unit | Ty::Never => Layout { size: 0, align: 1 },
        Ty::Bool | Ty::I8 | Ty::U8 => Layout { size: 1, align: 1 },
        Ty::I16 | Ty::U16 => Layout { size: 2, align: 2 },
        Ty::I32 | Ty::U32 | Ty::F32 => Layout { size: 4, align: 4 },
        Ty::I64 | Ty::U64 | Ty::F64 => Layout { size: 8, align: 8 },
        Ty::Isize | Ty::Usize | Ty::Ptr => {
            let w = target.ptr_bytes();
            Layout { size: w, align: w }
        }
        Ty::SliceView => {
            let w = target.ptr_bytes();
            Layout {
                size: sat_add(w, w),
                align: w,
            }
        }
        Ty::Array { elem, len } => {
            let e = layout_of(elem, target);
            // Infallible twin of Layout::array: saturates where the spec
            // path reports TooLarge (documented on sat_add).
            Layout {
                size: e.size.saturating_mul(*len),
                align: e.align,
            }
        }
        Ty::Tuple(fields) | Ty::Struct(fields) => struct_layout_of(fields, target).layout,
        Ty::Enum { variants } => enum_layout_of(variants, target).layout,
    }
}

/// `size_of[T]()`: the size component of [`layout_of`].
pub fn size_of(ty: &Ty, target: &Target) -> usize {
    layout_of(ty, target).size
}

/// `align_of[T]()`: the alignment component of [`layout_of`].
pub fn align_of(ty: &Ty, target: &Target) -> usize {
    layout_of(ty, target).align
}

/// A struct (or tuple) layout: the aggregate [`Layout`] plus each field's
/// byte offset in declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructLayout {
    /// The aggregate size/align (size includes tail padding to `align`).
    pub layout: Layout,
    /// `offsets[i]` is the byte offset of field `i`, in declaration order.
    pub offsets: Vec<usize>,
}

/// Q1's struct rule: fields in **declaration order** with natural alignment
/// and no reordering. Field `i` sits at `align_up(end_{i-1}, align_i)`; the
/// size is the end aligned up to the maximum field align; the align is that
/// maximum (1 for the empty struct). Capped by [`MEM_MAX_ALIGN`] by
/// construction, since no field align exceeds it.
pub fn struct_layout_of(fields: &[Ty], target: &Target) -> StructLayout {
    let mut offsets = Vec::with_capacity(fields.len());
    let mut off = 0usize;
    let mut max_align = 1usize;
    for f in fields {
        let l = layout_of(f, target);
        off = align_up(off, l.align);
        offsets.push(off);
        off = sat_add(off, l.size);
        max_align = max_align.max(l.align);
    }
    StructLayout {
        layout: Layout {
            size: align_up(off, max_align),
            align: max_align,
        },
        offsets,
    }
}

/// An enum layout: the aggregate [`Layout`], the tag width, and where the
/// payload starts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumLayout {
    /// The aggregate size/align.
    pub layout: Layout,
    /// The discriminant width from [`discriminant_size`] (0 when the enum
    /// needs no tag).
    pub discriminant_size: usize,
    /// The byte offset of the payload: the first offset past the tag
    /// suitably aligned for the largest payload.
    pub payload_offset: usize,
}

/// Q1's enum rule: the discriminant is the smallest unsigned type fitting
/// the variant count ([`discriminant_size`]), and the payload — the largest
/// variant payload, unit variants contributing nothing — sits at the first
/// suitably aligned offset past the tag. The align is the maximum of the tag
/// align and the payload align. A one-variant enum carries no tag and has
/// exactly its payload's layout; the empty enum is size 0, align 1.
pub fn enum_layout_of(variants: &[Variant], target: &Target) -> EnumLayout {
    let disc = discriminant_size(variants.len());
    // u8 -> 1, u16 -> 2, u32 -> 4, u64 -> 8; no tag -> 1.
    let disc_align = disc.max(1);
    let mut payload_size = 0usize;
    let mut payload_align = 1usize;
    for v in variants {
        if let Some(p) = &v.payload {
            let l = layout_of(p, target);
            payload_size = payload_size.max(l.size);
            payload_align = payload_align.max(l.align);
        }
    }
    let align = disc_align.max(payload_align);
    let payload_offset = align_up(disc, payload_align);
    EnumLayout {
        layout: Layout {
            size: align_up(sat_add(payload_offset, payload_size), align),
            align,
        },
        discriminant_size: disc,
        payload_offset,
    }
}

/// Q1's discriminant rule: the smallest unsigned type fitting the variant
/// count — 0 bytes when no tag is needed (0 or 1 variants), 1 byte to 256
/// variants, 2 bytes to 65,536, 4 bytes to 2^32, 8 beyond (unreachable in
/// practice; total so [`encode_discriminant`] stays total too).
pub fn discriminant_size(variant_count: usize) -> usize {
    if variant_count <= 1 {
        0
    } else if variant_count <= 256 {
        1
    } else if variant_count <= 65_536 {
        2
    } else if variant_count as u64 <= u64::from(u32::MAX) + 1 {
        4
    } else {
        8
    }
}

/// Encode variant index `discriminant` for an enum of `variant_count`
/// variants as little-endian tag bytes (the target is little-endian; see
/// the [`crate::target`] docs). Returns `None` for an empty enum, for an
/// index outside the variant set, or when the index is unrepresentable —
/// never a wrapping truncation.
pub fn encode_discriminant(discriminant: u32, variant_count: usize) -> Option<Vec<u8>> {
    let n = discriminant_size(variant_count);
    if variant_count == 0 || (discriminant as usize) >= variant_count {
        return None;
    }
    // `discriminant < variant_count` fits in `n` bytes by construction of
    // discriminant_size (n = 0 forces discriminant == 0).
    let bytes = discriminant.to_le_bytes();
    Some(bytes[..n].to_vec())
}

/// Decode tag bytes for an enum of `variant_count` variants back to the
/// variant index. Returns `None` when `bytes.len()` is not the tag width,
/// when the value names no variant, or when the width exceeds `u32` (a
/// >2^32-variant enum has no `u32`-denominated index to return).
pub fn decode_discriminant(bytes: &[u8], variant_count: usize) -> Option<u32> {
    let n = discriminant_size(variant_count);
    if bytes.len() != n || variant_count == 0 || n > 4 {
        return None;
    }
    let mut buf = [0u8; 4];
    buf[..n].copy_from_slice(bytes);
    let v = u32::from_le_bytes(buf);
    if (v as usize) < variant_count {
        Some(v)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t64() -> Target {
        Target::AARCH64_APPLE_DARWIN
    }

    #[test]
    fn primitives_match_spec_t0003() {
        let t = t64();
        for (ty, size, align) in [
            (Ty::Bool, 1, 1),
            (Ty::I8, 1, 1),
            (Ty::U8, 1, 1),
            (Ty::I16, 2, 2),
            (Ty::U16, 2, 2),
            (Ty::I32, 4, 4),
            (Ty::U32, 4, 4),
            (Ty::F32, 4, 4),
            (Ty::I64, 8, 8),
            (Ty::U64, 8, 8),
            (Ty::F64, 8, 8),
            (Ty::Isize, 8, 8),
            (Ty::Usize, 8, 8),
            (Ty::Ptr, 8, 8),
        ] {
            assert_eq!(layout_of(&ty, &t), Layout { size, align }, "{ty:?}");
        }
        // Pointer-width shapes follow the target (ch09 Rule 3).
        let t32 = Target::new(32).unwrap();
        assert_eq!(layout_of(&Ty::Usize, &t32), Layout { size: 4, align: 4 });
        assert_eq!(layout_of(&Ty::Ptr, &t32), Layout { size: 4, align: 4 });
        assert_eq!(
            layout_of(&Ty::SliceView, &t32),
            Layout { size: 8, align: 4 }
        );
        // Fixed widths do not move with the target.
        assert_eq!(layout_of(&Ty::U32, &t32), Layout { size: 4, align: 4 });
    }

    #[test]
    fn unit_never_and_empty_struct_are_zero_sized() {
        let t = t64();
        assert_eq!(layout_of(&Ty::Unit, &t), Layout { size: 0, align: 1 });
        assert_eq!(layout_of(&Ty::Never, &t), Layout { size: 0, align: 1 });
        let s = struct_layout_of(&[], &t);
        assert_eq!(s.layout, Layout { size: 0, align: 1 });
        assert!(s.offsets.is_empty());
    }

    #[test]
    fn mem_max_align_is_16() {
        assert_eq!(MEM_MAX_ALIGN, 16);
    }

    #[test]
    fn aligns_are_power_of_two_and_capped() {
        let t = t64();
        let shapes = vec![
            Ty::Bool,
            Ty::F64,
            Ty::Usize,
            Ty::Ptr,
            Ty::SliceView,
            Ty::Array {
                elem: Box::new(Ty::U16),
                len: 5,
            },
            Ty::Struct(vec![Ty::U8, Ty::U64, Ty::U16]),
            Ty::Enum {
                variants: vec![Variant::unit(), Variant::of(Ty::F64)],
            },
        ];
        for ty in &shapes {
            let l = layout_of(ty, &t);
            assert!(l.align.is_power_of_two(), "{ty:?}");
            assert!(l.align <= MEM_MAX_ALIGN, "{ty:?}");
            assert_eq!(validate_align(l.align), Ok(()));
        }
    }

    #[test]
    fn struct_u8_then_u32_pads() {
        // C: struct { uint8_t a; uint32_t b; } -> size 8, align 4.
        let s = struct_layout_of(&[Ty::U8, Ty::U32], &t64());
        assert_eq!(s.offsets, vec![0, 4]);
        assert_eq!(s.layout, Layout { size: 8, align: 4 });
    }

    #[test]
    fn struct_fields_keep_declaration_order_no_reordering() {
        // The rule under test: Q1 forbids reordering, so {u8, u32, u8} keeps
        // the tail pad a sorted layout would remove.
        let t = t64();
        let packed = struct_layout_of(&[Ty::U8, Ty::U8, Ty::U32], &t);
        assert_eq!(packed.offsets, vec![0, 1, 4]);
        assert_eq!(packed.layout.size, 8);
        let spread = struct_layout_of(&[Ty::U8, Ty::U32, Ty::U8], &t);
        assert_eq!(spread.offsets, vec![0, 4, 8]);
        assert_eq!(spread.layout.size, 12);
        // Same multiset of fields, different order, different size: order
        // is observable, so no pass may reorder.
        assert_ne!(packed.layout.size, spread.layout.size);
    }

    #[test]
    fn struct_tail_pads_to_align() {
        // C: struct { uint64_t a; uint8_t b; } -> size 16, align 8.
        let s = struct_layout_of(&[Ty::U64, Ty::U8], &t64());
        assert_eq!(s.offsets, vec![0, 8]);
        assert_eq!(s.layout, Layout { size: 16, align: 8 });
    }

    #[test]
    fn tuple_matches_struct_and_nesting_flattens() {
        let t = t64();
        let tup = struct_layout_of(&[Ty::U16, Ty::U64], &t);
        assert_eq!(tup.offsets, vec![0, 8]);
        assert_eq!(tup.layout, Layout { size: 16, align: 8 });
        assert_eq!(
            layout_of(&Ty::Tuple(vec![Ty::U16, Ty::U64]), &t),
            layout_of(&Ty::Struct(vec![Ty::U16, Ty::U64]), &t)
        );
        // Nested: { {u8, u32}, u8 } -> inner size 8 align 4, outer 12/4.
        let inner = Ty::Struct(vec![Ty::U8, Ty::U32]);
        let outer = struct_layout_of(&[inner, Ty::U8], &t);
        assert_eq!(outer.offsets, vec![0, 8]);
        assert_eq!(outer.layout, Layout { size: 12, align: 4 });
    }

    #[test]
    fn array_strides_and_empty() {
        let t = t64();
        assert_eq!(
            layout_of(
                &Ty::Array {
                    elem: Box::new(Ty::U16),
                    len: 3,
                },
                &t
            ),
            Layout { size: 6, align: 2 }
        );
        assert_eq!(
            layout_of(
                &Ty::Array {
                    elem: Box::new(Ty::U64),
                    len: 0,
                },
                &t
            ),
            Layout { size: 0, align: 8 }
        );
        // Layout::array preserves align and multiplies.
        let e = Layout { size: 4, align: 4 };
        assert_eq!(e.array(3), Ok(Layout { size: 12, align: 4 }));
    }

    #[test]
    fn array_overflow_is_too_large() {
        // ch10 S0013: Layout.array[T](n) raises too_large on overflow.
        let e = Layout { size: 8, align: 8 };
        assert_eq!(e.array(usize::MAX), Err(LayoutError::TooLarge));
        assert_eq!(
            Layout {
                size: usize::MAX,
                align: 1
            }
            .array(2),
            Err(LayoutError::TooLarge)
        );
        assert_eq!(
            Layout { size: 0, align: 1 }.array(usize::MAX),
            Ok(Layout { size: 0, align: 1 })
        );
    }

    #[test]
    fn align_validation() {
        for a in [1, 2, 4, 8, 16] {
            assert_eq!(validate_align(a), Ok(()), "align {a}");
        }
        for a in [0, 3, 6, 24, 32] {
            assert_eq!(
                validate_align(a),
                Err(LayoutError::UnsupportedAlign),
                "align {a}"
            );
        }
    }

    #[test]
    fn enum_needs_no_tag_for_zero_or_one_variant() {
        let t = t64();
        assert_eq!(discriminant_size(0), 0);
        assert_eq!(discriminant_size(1), 0);
        let e0 = enum_layout_of(&[], &t);
        assert_eq!(e0.layout, Layout { size: 0, align: 1 });
        let e1 = enum_layout_of(&[Variant::unit()], &t);
        assert_eq!(e1.layout, Layout { size: 0, align: 1 });
        // One payload variant is exactly the payload (no tag).
        let e1p = enum_layout_of(&[Variant::of(Ty::U32)], &t);
        assert_eq!(e1p.discriminant_size, 0);
        assert_eq!(e1p.payload_offset, 0);
        assert_eq!(e1p.layout, Layout { size: 4, align: 4 });
    }

    #[test]
    fn enum_two_units_is_one_byte() {
        let e = enum_layout_of(&[Variant::unit(), Variant::unit()], &t64());
        assert_eq!(e.discriminant_size, 1);
        assert_eq!(e.payload_offset, 1);
        assert_eq!(e.layout, Layout { size: 1, align: 1 });
    }

    #[test]
    fn enum_payload_offset_respects_payload_align() {
        // { none, u64 }: tag 1 byte, payload align 8 -> payload at 8,
        // size 16, align 8.
        let e = enum_layout_of(&[Variant::unit(), Variant::of(Ty::U64)], &t64());
        assert_eq!(e.discriminant_size, 1);
        assert_eq!(e.payload_offset, 8);
        assert_eq!(e.layout, Layout { size: 16, align: 8 });
        // Largest payload wins: { u8, u32 } -> tag 1, payload align 4,
        // offset 4, size 8.
        let e2 = enum_layout_of(&[Variant::of(Ty::U8), Variant::of(Ty::U32)], &t64());
        assert_eq!(e2.payload_offset, 4);
        assert_eq!(e2.layout, Layout { size: 8, align: 4 });
    }

    #[test]
    fn discriminant_width_boundaries() {
        assert_eq!(discriminant_size(2), 1);
        assert_eq!(discriminant_size(255), 1);
        assert_eq!(discriminant_size(256), 1);
        assert_eq!(discriminant_size(257), 2);
        assert_eq!(discriminant_size(65_535), 2);
        assert_eq!(discriminant_size(65_536), 2);
        assert_eq!(discriminant_size(65_537), 4);
        assert_eq!(discriminant_size(u32::MAX as usize + 1), 4);
    }

    #[test]
    fn discriminant_encode_decode_roundtrip() {
        for (count, width) in [(2, 1), (256, 1), (257, 2), (65_536, 2), (65_537, 4)] {
            assert_eq!(discriminant_size(count), width);
            for v in [0u32, 1, (count - 1) as u32] {
                let bytes = encode_discriminant(v, count).expect("encodable");
                assert_eq!(bytes.len(), width);
                assert_eq!(decode_discriminant(&bytes, count), Some(v));
            }
        }
        // Tagless enums carry no bytes.
        assert_eq!(encode_discriminant(0, 1), Some(vec![]));
        assert_eq!(decode_discriminant(&[], 1), Some(0));
    }

    #[test]
    fn discriminant_rejects_out_of_range() {
        assert_eq!(encode_discriminant(0, 0), None);
        assert_eq!(encode_discriminant(2, 2), None);
        assert_eq!(encode_discriminant(256, 256), None);
        assert_eq!(decode_discriminant(&[], 0), None);
        assert_eq!(decode_discriminant(&[2], 2), None);
        // Wrong width is a mismatch, not a truncation.
        assert_eq!(decode_discriminant(&[0, 0], 2), None);
        assert_eq!(decode_discriminant(&[], 2), None);
    }

    #[test]
    fn enum_tag_widths_drive_layout() {
        let t = t64();
        let wide = vec![Variant::unit(); 257];
        let e = enum_layout_of(&wide, &t);
        assert_eq!(e.discriminant_size, 2);
        assert_eq!(e.layout, Layout { size: 2, align: 2 });
        let wider = vec![Variant::unit(); 65_537];
        let e2 = enum_layout_of(&wider, &t);
        assert_eq!(e2.discriminant_size, 4);
        assert_eq!(e2.layout, Layout { size: 4, align: 4 });
    }

    /// Risk R3's retiring experiment: the struct rule diffed against `clang`
    /// on the C-equivalent structs (LP64, `-O0`). Each row is `(fields,
    /// c_size, c_align, c_offsets)`; where they agree, Q1's rule is also the
    /// FFI rule and Q1 answers itself.
    #[test]
    fn c_table_agrees_with_c_abi() {
        let t = Target::AARCH64_APPLE_DARWIN;
        // (fields, clang size, clang align, clang offsets)
        let rows: Vec<(Vec<Ty>, usize, usize, Vec<usize>)> = vec![
            (vec![Ty::U8, Ty::U32], 8, 4, vec![0, 4]),
            (vec![Ty::U32, Ty::U8], 8, 4, vec![0, 4]),
            (vec![Ty::U8, Ty::U64, Ty::U8], 24, 8, vec![0, 8, 16]),
            (vec![Ty::F64, Ty::U8], 16, 8, vec![0, 8]),
            (vec![Ty::U16, Ty::U16, Ty::U32], 8, 4, vec![0, 2, 4]),
            (vec![Ty::U8, Ty::U8, Ty::U8], 3, 1, vec![0, 1, 2]),
            (vec![Ty::U16, Ty::U64], 16, 8, vec![0, 8]),
            (vec![Ty::Bool, Ty::U64], 16, 8, vec![0, 8]),
            (
                vec![
                    Ty::Array {
                        elem: Box::new(Ty::U64),
                        len: 3,
                    },
                    Ty::U8,
                ],
                32,
                8,
                vec![0, 24],
            ),
            (
                vec![Ty::U8, Ty::U16, Ty::U32, Ty::U64],
                16,
                8,
                vec![0, 2, 4, 8],
            ),
        ];
        for (fields, size, align, offsets) in &rows {
            let s = struct_layout_of(fields, &t);
            assert_eq!(s.layout.size, *size, "{fields:?}");
            assert_eq!(s.layout.align, *align, "{fields:?}");
            assert_eq!(&s.offsets, offsets, "{fields:?}");
        }
    }

    #[test]
    fn c_table_nested_and_pointer_shapes() {
        let t = Target::AARCH64_APPLE_DARWIN;
        // C: struct { struct { uint8_t a; uint32_t b; } inner; uint8_t d; }
        // -> inner 8/4, d at 8, size 12, align 4.
        let inner = Ty::Struct(vec![Ty::U8, Ty::U32]);
        let outer = struct_layout_of(&[inner, Ty::U8], &t);
        assert_eq!(outer.offsets, vec![0, 8]);
        assert_eq!(outer.layout, Layout { size: 12, align: 4 });
        // C: struct { void *p; uint32_t n; } -> 16/8, offsets [0, 8].
        let s = struct_layout_of(&[Ty::Ptr, Ty::U32], &t);
        assert_eq!(s.offsets, vec![0, 8]);
        assert_eq!(s.layout, Layout { size: 16, align: 8 });
        // C: struct { void *p; size_t n; } (a Slice view) -> 16/8.
        let v = struct_layout_of(&[Ty::SliceView], &t);
        assert_eq!(v.layout, Layout { size: 16, align: 8 });
    }

    #[test]
    fn size_and_align_of_agree_with_layout_of() {
        let t = t64();
        let ty = Ty::Struct(vec![Ty::U8, Ty::F64]);
        let l = layout_of(&ty, &t);
        assert_eq!(size_of(&ty, &t), l.size);
        assert_eq!(align_of(&ty, &t), l.align);
        assert_eq!((l.size, l.align), (16, 8));
    }
}
