//! One FMIR value (design §3.1): "12 bytes. There is no `Vec<Box<..>>`
//! anywhere." `flags.SECRET` and `ct` are non-optional (ch05 Rule 6).
//! [`ValRow::new`] is what makes that hard to get wrong: it takes `secret`
//! and `ct` as required arguments, never an `Option` and never a default.
//!
//! It is not, and cannot be, the *only* way in: design §3.1 fixes `ValRow` as
//! a plain fixed-width row with public fields, so a caller can always write a
//! struct literal (or [`ValRow::with_flags`]) carrying
//! [`crate::flags::SECRET_UNSPECIFIED`] / [`crate::flags::CT_UNSPECIFIED`] —
//! `tests/verify_rejects.rs` and the textual parser both do exactly that on
//! purpose, to build the negative corpus. That is why design §1 states the
//! rule as a disjunction ("a row without them must not be constructible, **or**
//! the verifier must reject it"): the enforcement that actually holds for
//! every provenance is `verify()`'s `MissingSecretField`/`MissingCtRegion`
//! (see `tests/adversarial.rs::rows_lacking_the_mandatory_fields_are_rejected_however_built`),
//! and this constructor is the ergonomic half, not a guarantee.

use std::ops::Range;

use fors_fir::ty::TyId;

use crate::flags::{CT_UNSPECIFIED, ValFlags};
use crate::ids::InstId;

/// Where a value comes from: a defining instruction, or a parameter ordinal.
/// design §3.1: "def: u32, // defining instruction, or PARAM|u16 for
/// parameters". The exact bit layout is not spelled out further, so this
/// crate fixes one: the top bit tags "parameter", the low 16 bits are the
/// ordinal, which leaves 15 middle bits unused/zero — comfortably inside a
/// `u32` and never confusable with a real `InstId` (an FMIR body with
/// `2^31` instructions is many orders past every budget in design §10.3).
/// [decision: `PARAM_TAG = 1 << 31`, ordinal in the low 16 bits]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValDef {
    Inst(InstId),
    Param(u16),
}

pub const PARAM_TAG: u32 = 1 << 31;

impl ValDef {
    pub fn encode(self) -> u32 {
        match self {
            ValDef::Inst(id) => {
                debug_assert!(
                    id.0 & PARAM_TAG == 0,
                    "InstId must not use the reserved top bit"
                );
                id.0
            }
            ValDef::Param(ordinal) => PARAM_TAG | (ordinal as u32),
        }
    }

    pub fn decode(raw: u32) -> ValDef {
        if raw & PARAM_TAG != 0 {
            ValDef::Param((raw & 0xFFFF) as u16)
        } else {
            ValDef::Inst(InstId(raw))
        }
    }
}

/// design §3.1's literal `ValRow`, field for field: `ty`, `flags`, `ct`,
/// `def`. `#[repr(C)]` because the design's own comment ("12 bytes. There is
/// no `Vec<Box<..>>` anywhere") is about the row's host memory layout.
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ValRow {
    pub ty: TyId,
    pub flags: ValFlags,
    pub ct: u16,
    pub def: u32,
}

impl ValRow {
    /// The only safe constructor. `secret` and `ct` are both required
    /// arguments (never defaulted, never `Option`), which is ch05 Rule 6 at
    /// the API level: a caller of this crate's builder cannot construct a row
    /// while forgetting either field.
    pub fn new(ty: TyId, secret: bool, ct: u16, def: ValDef) -> Self {
        debug_assert_ne!(
            ct, CT_UNSPECIFIED,
            "0..=65534 is the legal ct_region domain at F0 (design §3.11)"
        );
        ValRow {
            ty,
            flags: ValFlags::new(secret),
            ct,
            def: def.encode(),
        }
    }

    pub fn with_flags(mut self, extra: u16) -> Self {
        self.flags = self.flags.with(extra);
        self
    }

    pub fn def(self) -> ValDef {
        ValDef::decode(self.def)
    }

    pub fn is_secret(self) -> bool {
        self.flags.is_secret()
    }
}

/// SoA pool of [`ValRow`]s, plus the `SCOPED`-only `sources` side table
/// (design §3.4: "a `flags.SCOPED` value carries `sources: Range<u32>` into a
/// `SourcePool` of `PlaceId`s").
#[derive(Clone, Debug, Default)]
pub struct ValPool {
    rows: Vec<ValRow>,
    /// Parallel to `rows`; `None` unless the row is `SCOPED`.
    /// [decision: parallel `Option<Range<u32>>`, matching the `AliasSeed`
    /// pool's "parallel array, keyed by position" shape rather than a
    /// separate id-indexed side map]
    scoped_sources: Vec<Option<Range<u32>>>,
}

impl ValPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn push(&mut self, row: ValRow) -> crate::ids::ValId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        self.scoped_sources.push(None);
        crate::ids::ValId(i)
    }

    pub fn row(&self, id: crate::ids::ValId) -> ValRow {
        self.rows[id.index()]
    }

    /// [`ValPool::row`] for an id that came out of an instruction slot rather
    /// than out of this pool's own iteration: an `InstRow.a` is a raw `u32`,
    /// and arbitrary FMIR (hand-written, decoded, fuzzed) may name a value
    /// that does not exist. `verify()` uses this so a dangling operand is a
    /// diagnostic, never a panic.
    pub fn try_row(&self, id: crate::ids::ValId) -> Option<ValRow> {
        self.rows.get(id.index()).copied()
    }

    pub fn set_scoped_sources(&mut self, id: crate::ids::ValId, sources: Range<u32>) {
        self.scoped_sources[id.index()] = Some(sources);
    }

    pub fn scoped_sources(&self, id: crate::ids::ValId) -> Option<Range<u32>> {
        self.scoped_sources[id.index()].clone()
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (crate::ids::ValId, ValRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (crate::ids::ValId(i as u32), *r))
    }
}

/// `sources: Range<u32>` resolves into this pool of interned `PlaceId`s
/// (design §3.4, `SourceId` in `ids.rs`). Kept distinct from
/// `crate::scope::PlaceListPool` only nominally — same shape, but a `SCOPED`
/// value's sources are indexed from `ValPool`, never from a `ScopeRow`, so
/// giving it a different alias avoids one range meaning two different things
/// depending which table you found it in.
pub type SourcePool = crate::scope::PlaceListPool;

#[cfg(test)]
mod tests {
    use super::*;
    use fors_fir::ty::TY_UNIT;

    #[test]
    fn val_def_param_round_trips() {
        let d = ValDef::Param(12);
        assert_eq!(ValDef::decode(d.encode()), d);
    }

    #[test]
    fn val_def_inst_round_trips() {
        let d = ValDef::Inst(InstId(5));
        assert_eq!(ValDef::decode(d.encode()), d);
    }

    #[test]
    fn new_row_is_never_secret_unspecified() {
        let row = ValRow::new(TY_UNIT, false, 0, ValDef::Param(0));
        assert!(!row.flags.is_secret_unspecified());
        assert_eq!(row.ct, 0);
    }
}
