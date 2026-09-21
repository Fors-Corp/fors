//! The type shapes the layout rule covers.
//!
//! This is deliberately NOT `fors-fir`'s `TyId`: the rule is a pure function
//! of a shape (design `docs/design/fmir-interpreter.md` §11.1 Q1, risk R3),
//! and depending on the checker's universe would put the checker's types
//! under every consumer of a byte count. A consumer that owns FIR types
//! maps them onto [`Ty`] once — scalars to scalars, `Array[T, N]` to
//! [`Ty::Array`], nominal structs/tuples to [`Ty::Struct`]/[`Ty::Tuple`],
//! enums to [`Ty::Enum`], `Own`/`Ref`/`fn` values to [`Ty::Ptr`],
//! `Slice[T]`/`Str` views to [`Ty::SliceView`] — and calls
//! [`crate::layout_of`]. The shapes are exactly the ones the 64 runtime
//! conformance tests use (design §1.1: scalars, `Array`, `Slice`, tuples,
//! `struct`, `enum` with payloads, `Own`, `Ref`, `Arena`, `fn` values).

use crate::target::Target;

/// One variant of a [`Ty::Enum`]: a unit variant (`payload: None`) or a
/// payload variant (`payload: Some`, the carried type).
///
/// A multi-field payload nests as [`Ty::Tuple`] or [`Ty::Struct`]; the
/// discriminant is the variant's declaration index (ch09 Rule T0006: an
/// enum's variant set is exactly its declaration's, in order), encoded by
/// [`crate::encode_discriminant`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variant {
    /// The carried type, or `None` for a unit variant.
    pub payload: Option<Ty>,
}

impl Variant {
    /// A unit variant carrying nothing.
    pub fn unit() -> Variant {
        Variant { payload: None }
    }

    /// A payload variant carrying `payload`.
    pub fn of(payload: Ty) -> Variant {
        Variant {
            payload: Some(payload),
        }
    }
}

/// A type shape the layout rule knows how to lay out.
///
/// Primitive sizes are ch09 Rule T0003 (`docs/spec/09-types.md`): `i8 u8
/// bool` 1; `i16 u16` 2; `i32 u32 f32` 4; `i64 u64 f64` 8; `isize usize`
/// and the pointer word the target width. `()` and `never` are size 0
/// (T0004). Layout of every non-primitive type is ch05's — i.e. this crate,
/// per Q1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ty {
    /// `()`: one value, size 0 (T0004).
    Unit,
    /// `never`: uninhabited, size 0 (T0004).
    Never,
    /// `bool`: exactly `true`/`false`, 1 byte (T0003).
    Bool,
    /// `i8`: 1 byte (T0003).
    I8,
    /// `i16`: 2 bytes (T0003).
    I16,
    /// `i32`: 4 bytes (T0003).
    I32,
    /// `i64`: 8 bytes (T0003).
    I64,
    /// `u8`: 1 byte (T0003).
    U8,
    /// `u16`: 2 bytes (T0003).
    U16,
    /// `u32`: 4 bytes (T0003).
    U32,
    /// `u64`: 8 bytes (T0003).
    U64,
    /// `isize`: the target pointer width (T0003, ch09 Rule 3).
    Isize,
    /// `usize`: the target pointer width (T0003, ch09 Rule 3).
    Usize,
    /// `f32`: 4 bytes (T0003).
    F32,
    /// `f64`: 8 bytes (T0003).
    F64,
    /// One target word: `rawptr` (T0003) and the erased address word of
    /// `Own[T, A]`, `Ref[T, A]` and `fn` values (ch01 Rules 15e, 18: brands
    /// are erased after checking, so no brand survives in the layout).
    ///
    /// `rawptr` is scalar by T0003's "no other scalar exists"; the erased
    /// word shares its shape exactly, so [`Ty::is_scalar`] counts both.
    /// The conflation is unobservable through
    /// [`crate::shape_monomorphized`]: a one-word type is at most 8 bytes
    /// and therefore monomorphizes via the size disjunct either way.
    Ptr,
    /// A fat view (`Slice[T]`, `Str`): address plus length, two target
    /// words. Never scalar: it is an aggregate shape, not a primitive.
    SliceView,
    /// `Array[T, N]`: `N` consecutive `T` (T0005, ch03 Rules 21-24a).
    Array { elem: Box<Ty>, len: usize },
    /// `(T1, ..., Tn)`: laid out exactly like a struct (T0004).
    Tuple(Vec<Ty>),
    /// A nominal `struct`'s fields in declaration order (T0006).
    Struct(Vec<Ty>),
    /// A nominal `enum`'s variants in declaration order (T0006).
    Enum { variants: Vec<Variant> },
}

impl Ty {
    /// ch09 T0003's scalar set: the fixed-width integers, `isize`/`usize`,
    /// `f32`/`f64`, `bool`, and the pointer word. Everything else — `()`,
    /// `never`, arrays, tuples, structs, enums, fat views — is not scalar.
    ///
    /// This is the predicate ch03 Rule 16's first disjunct ("monomorphize
    /// when scalar") reads; see [`crate::is_scalar_le16`].
    pub fn is_scalar(&self) -> bool {
        matches!(
            self,
            Ty::Bool
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::Isize
                | Ty::Usize
                | Ty::F32
                | Ty::F64
                | Ty::Ptr
        )
    }

    /// The target width of the pointer-sized shapes, for tests and for
    /// consumers that pre-size buffers. Scalar fixed widths need no target.
    pub fn ptr_sized(target: &Target) -> usize {
        target.ptr_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_primitive_is_scalar() {
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
            assert!(ty.is_scalar(), "{ty:?} must be scalar (ch09 T0003)");
        }
    }

    #[test]
    fn composites_unit_never_and_views_are_not_scalar() {
        assert!(!Ty::Unit.is_scalar());
        assert!(!Ty::Never.is_scalar());
        assert!(!Ty::SliceView.is_scalar());
        assert!(
            !Ty::Array {
                elem: Box::new(Ty::U8),
                len: 4,
            }
            .is_scalar()
        );
        assert!(!Ty::Tuple(vec![Ty::U8]).is_scalar());
        assert!(!Ty::Struct(vec![Ty::U8]).is_scalar());
        assert!(
            !Ty::Enum {
                variants: vec![Variant::unit()],
            }
            .is_scalar()
        );
    }

    #[test]
    fn variant_constructors() {
        assert_eq!(Variant::unit().payload, None);
        assert_eq!(Variant::of(Ty::U32).payload, Some(Ty::U32));
    }
}
