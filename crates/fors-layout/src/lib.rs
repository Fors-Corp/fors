//! `fors-layout`: the Fors type-layout rule (owner Q1) as a pure function.
//!
//! Owner decision Q1 (`docs/design/fmir-interpreter.md` §11.1, [HOLE-6]):
//! no chapter defined type layout, yet `Layout.of[T]().size` is observable
//! from a Fors program, so layout is a language fact. The decided rule,
//! implemented here, is the thinnest honest content: fields in **declaration
//! order** with natural alignment and no reordering (so `soa struct` and FFI
//! stay predictable), `align <= MEM_MAX_ALIGN = 16` (ch10 S0013), the enum
//! discriminant the smallest unsigned type fitting the variant count, the
//! payload at the first suitably aligned offset.
//!
//! Module map:
//! - [`target`] — the [`Target`] pointer width layouts are computed for
//!   (ch09 Rule 3; never the host).
//! - [`ty`] — the [`Ty`] shapes the rule covers (ch09 T0003-T0006).
//! - [`layout`] — the rule itself: [`layout_of`], [`size_of`],
//!   [`align_of`], [`struct_layout_of`], [`enum_layout_of`], discriminant
//!   [`encode_discriminant`]/[`decode_discriminant`], and the std `Layout`
//!   surface ([`Layout`], [`MEM_MAX_ALIGN`], [`Layout::array`]).
//! - [`mono`] — ch03 Rule 16's size half: [`is_scalar_le16`] and
//!   [`shape_monomorphized`] over [`MONOMORPHIZE_SIZE_MAX`].
//!
//! # Spec rules implemented, by item
//!
//! - Q1/`[HOLE-6]`: [`layout_of`], [`struct_layout_of`], [`enum_layout_of`],
//!   [`discriminant_size`](layout::discriminant_size).
//! - ch10 S0013 (`docs/spec/10-std.md`): [`Layout`], [`MEM_MAX_ALIGN`],
//!   [`Layout::array`], [`validate_align`], [`LayoutError`].
//! - ch09 T0003-T0006 (`docs/spec/09-types.md`): [`Ty`], [`Ty::is_scalar`].
//! - ch03 R16-R17 (`docs/spec/03-numerics-determinism.md`):
//!   [`is_scalar_le16`], [`shape_monomorphized`], [`MONOMORPHIZE_SIZE_MAX`],
//!   [`MONOMORPHIZE_INSTR_THRESHOLD`].
//!
//! # Integration points (F1/F2; D11/D12 consumers) — documented, not wired
//!
//! `fors-lower` does not exist on this branch, so nothing here imports it;
//! when it lands, these are the seams it takes (design §4.1):
//!
//! - **D12 (layout)**: `Layout.of[T]()` lowers to [`layout_of`] via the
//!   `@size_of`/`@align_of` intrinsics (design §5.8); `Own` (whose block
//!   MUST have `Layout.of[T]()`'s size and align, ch10 Rule 28), `Vec`
//!   growth, `Buffer`/`Array` indexing and `Block` sizing read
//!   [`size_of`]/[`align_of`]; field projections read
//!   [`struct_layout_of`] offsets; variant construction and `match`
//!   lowering read [`enum_layout_of`] plus
//!   [`encode_discriminant`]/[`decode_discriminant`].
//! - **D11 (mono-vs-witness)**: `fors-lower` owns the decision ([HOLE-5],
//!   E10) and calls [`is_scalar_le16`]/[`shape_monomorphized`] for the
//!   "scalar, `<= 16` bytes" half — the 16-byte test F6's `Vec`/`Own`
//!   lowering and F7's generics both gate on — ORing the
//!   `MONOMORPHIZE_INSTR_THRESHOLD` disjunct from the callee body it holds.
//!
//! This crate is a leaf: std only, zero dependencies (not even `fors-fir`,
//! so no cycle is possible whichever layer consumes it).
//!
//! License: Apache-2.0 via the workspace (`Cargo.toml`
//! `license.workspace = true`), as every other crate; like them this crate
//! carries no per-file header.

#![deny(unsafe_code)]

pub mod layout;
pub mod mono;
pub mod target;
pub mod ty;

pub use layout::{
    EnumLayout, Layout, LayoutError, MEM_MAX_ALIGN, StructLayout, align_of, decode_discriminant,
    discriminant_size, encode_discriminant, enum_layout_of, layout_of, size_of, struct_layout_of,
    validate_align,
};
pub use mono::{
    MONOMORPHIZE_INSTR_THRESHOLD, MONOMORPHIZE_SIZE_MAX, is_scalar_le16, shape_monomorphized,
};
pub use target::Target;
pub use ty::{Ty, Variant};
