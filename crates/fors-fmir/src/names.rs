//! The static names ch02 R17's `render` needs and FMIR otherwise never
//! carries (design §5.4 step 4, F3).
//!
//! `render` is defined on the STATIC type of the error leaving `main`, and
//! the clause list names things no instruction holds: an enum's or struct's
//! fully-qualified path (`std.mem.alloc.AllocError`), its variant names, a
//! struct-form variant's or a struct's field names, and the static type of
//! every payload component it recurses into. The interpreter is the oracle
//! and reads no checker output (ch05 R3), so lowering — which can see the
//! declarations — writes these down once per build, keyed by the
//! lowering-owned `TyId`, and the interpreter reads them back.
//!
//! Only NOMINAL types appear here. Primitives, tuples and `()` render from
//! the type store alone, and a type with no row renders as `..` (R17's
//! "every other type" clause), which is also how lowering says "opaque": a
//! root-capability or allocator type, `Own`, `Slice`, a `fn` or `dyn` type,
//! a rigid parameter.

use fors_fir::ty::TyId;

/// One variant's payload, in declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VariantPayload {
    /// A unit variant: `E.a`.
    Unit,
    /// A tuple-form payload: `E.a(x, y)`, each component's static type.
    Tuple(Vec<TyId>),
    /// A struct-form payload: `E.a { n: x }`, `(field name, static type)`.
    Fields(Vec<(String, TyId)>),
}

/// One enum variant: the discriminant `fors-layout` decided (what slot 0 of
/// the interpreter's variant cell holds), its name and its payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VariantName {
    pub discr: u64,
    pub name: String,
    pub payload: VariantPayload,
}

/// How one nominal type renders.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeName {
    /// An enum: its fully-qualified path and every variant.
    Enum {
        path: String,
        variants: Vec<VariantName>,
    },
    /// A struct: its fully-qualified path and its fields in declaration
    /// order.
    Struct {
        path: String,
        fields: Vec<(String, TyId)>,
    },
}

/// The build's render table: `(TyId, TypeName)` rows, at most one per type.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeNames {
    pub rows: Vec<(TyId, TypeName)>,
}

impl TypeNames {
    /// The row for `ty`, when lowering wrote one.
    pub fn get(&self, ty: TyId) -> Option<&TypeName> {
        self.rows.iter().find(|(t, _)| *t == ty).map(|(_, n)| n)
    }

    /// Adds `name` for `ty` unless a row already exists (the first writer
    /// wins: a type's names do not depend on who asked).
    pub fn insert(&mut self, ty: TyId, name: TypeName) {
        if self.get(ty).is_none() {
            self.rows.push((ty, name));
        }
    }

    /// Merges `other`'s rows in, first writer winning.
    pub fn extend(&mut self, other: TypeNames) {
        for (t, n) in other.rows {
            self.insert(t, n);
        }
    }
}
