//! `u32` newtypes indexing FMIR's own per-declaration pools.
//!
//! Same convention as `fors_index::ids` and `fors_fir::{ty,sig,defpath}`: an
//! id carries no data itself, so a pool's columns are the only storage. Every
//! id here is relative to ONE `DeclFmir`'s own pools (design §3.1: "every
//! index is relative to this struct's own pools"), never global, which is
//! what makes a `DeclFmir` movable between processes and content-hashable.
//!
//! `fors_index::ids::index_newtype!` is crate-private to `fors-index` (no
//! `#[macro_export]`), so this is a separate copy rather than a shared one;
//! the two macros must stay textually identical. [decision: local macro copy]

macro_rules! index_newtype {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(pub u32);

        impl $name {
            pub const fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

index_newtype!(
    /// One row of [`crate::value::ValPool`]: one FMIR SSA-ish value.
    ValId
);
index_newtype!(
    /// One row of [`crate::block::BlockPool`]: one basic block.
    BlockId
);
index_newtype!(
    /// One row of [`crate::inst::InstPool`]: one non-terminator instruction.
    InstId
);
index_newtype!(
    /// One row of [`crate::scope::ScopePool`]: one node of the lexical scope
    /// tree (design §3.2 — an annotation on blocks, never control flow).
    ScopeId
);
index_newtype!(
    /// One row of [`crate::place::PlacePool`]: one interned `(root, segs)`
    /// place shape (design §3.3).
    PlaceId
);
index_newtype!(
    /// One row of [`crate::region::RegionPool`]: one `spawn`/`parallel`/
    /// `with-arena` region shell (design §3.7, §1.2 — M3 executes them for
    /// real, M1 represents and serially elides).
    RegionId
);
index_newtype!(
    /// One row of [`crate::site::SitePool`]: a `(span, TrapKind slot, decl)`
    /// side-table entry a diagnostic or a trap points at (design §3.1).
    SiteId
);
index_newtype!(
    /// One row of [`crate::constpool::ConstPool`]: one comptime-known,
    /// content-addressed value (design §3.1). Named `FmirConstId` rather than
    /// `ConstId` because `fors_fir::ty::ConstId` already owns that name and
    /// this crate imports both. [decision: renamed to avoid the collision]
    FmirConstId
);
index_newtype!(
    /// One row of [`crate::scope::DeferPool`] (design §3.8).
    DeferId
);
index_newtype!(
    /// One row of [`crate::scope::ObligPool`], a `PlaceId` under a linear
    /// obligation (design §3.5).
    ObligId
);
index_newtype!(
    /// One row of a `SourcePool` of `PlaceId`s a `SCOPED` value keeps live
    /// (design §3.4, ch01 R19c(d)).
    SourceId
);
index_newtype!(
    /// An arena brand id. Compile-time IR metadata only (ch05 Rule 5): no
    /// execution reads it, it only seeds an `AliasSeed::Arena` (design
    /// §3.4a, §3.7).
    BrandId
);
index_newtype!(
    /// One row of [`crate::region::CapturePool`]: one entry of a region's
    /// explicit typed capture list (ch05 Rule 9).
    CaptureId
);

/// Sentinel for "no scope" / "no region" / "no brand" / "no arena-mediated
/// caller" — every id type here is a bare `u32`, so `u32::MAX` is reserved as
/// the absent value uniformly, matching `fors_fir`'s own `NO_*` convention
/// (e.g. `defpath::NO_DEF`, `ty::NO_TY`). [decision: u32::MAX absent sentinel,
/// uniform across every id type in this crate]
pub const ABSENT: u32 = u32::MAX;

impl ScopeId {
    pub const NONE: ScopeId = ScopeId(ABSENT);
}
impl RegionId {
    pub const NONE: RegionId = RegionId(ABSENT);
}
impl BrandId {
    pub const NONE: BrandId = BrandId(ABSENT);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absent_sentinels_round_trip() {
        assert_eq!(ScopeId::NONE.0, u32::MAX);
        assert_eq!(RegionId::NONE.0, u32::MAX);
        assert_eq!(BrandId::NONE.0, u32::MAX);
    }

    #[test]
    fn index_newtype_index_matches_field() {
        let v = ValId(7);
        assert_eq!(v.index(), 7usize);
    }
}
