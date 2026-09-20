//! The lexical scope tree (design §3.2): "an annotation on blocks, never a
//! control-flow structure". Each block names its `ScopeId`; each scope
//! records its parent, arena brand, pending `defer`/`errdefer` ranges,
//! linear obligations and region membership (design §3.2, §3.4a, §3.5,
//! §3.7, §3.8).

use std::ops::Range;

use crate::ids::{BlockId, BrandId, DeferId, ObligId, PlaceId, RegionId, ScopeId};

/// A flat `Vec<PlaceId>` with range-interned slices, shared by
/// [`ScopeRow::obligations`] (design §3.5) and by a `SCOPED` value's
/// `sources` (design §3.4) — both are "a range into a list of `PlaceId`s",
/// so one pool type serves both rather than two structurally identical
/// copies. [decision: one shared `PlaceListPool` type, two separate
/// instances (`DeclFmir::obligations`, `DeclFmir::scoped_sources`) rather
/// than the design's separately-named `ObligPool`/`SourcePool`]
#[derive(Clone, Debug, Default)]
pub struct PlaceListPool {
    items: Vec<PlaceId>,
}

impl PlaceListPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_list(&mut self, places: &[PlaceId]) -> Range<u32> {
        let start = self.items.len() as u32;
        self.items.extend_from_slice(places);
        let end = self.items.len() as u32;
        start..end
    }

    /// Clamped to the pool ([`crate::inst::clamp_range`]): the range comes out
    /// of a row that arbitrary FMIR is free to malform.
    pub fn get(&self, range: Range<u32>) -> &[PlaceId] {
        &self.items[crate::inst::clamp_range(range, self.items.len())]
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// For `encode.rs` only: raw backing storage and its inverse, so a
    /// decoded flat list lands back at the exact same positions the ranges
    /// stored elsewhere (`ScopeRow.obligations`, a `SCOPED` value's
    /// `sources`) already point at.
    pub fn as_slice(&self) -> &[PlaceId] {
        &self.items
    }

    pub fn from_raw(items: Vec<PlaceId>) -> Self {
        PlaceListPool { items }
    }
}

/// `ObligId`/`DeferId` reference a *position*, e.g. inside a diagnostic —
/// kept as real newtypes (unlike the shared list above) since `Discharge`
/// and `DeferRow` are stored one-per-slot rather than sliced.
#[allow(dead_code)]
fn assert_ids_exist(_o: ObligId, _d: DeferId) {}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeferKind {
    Defer,
    ErrDefer,
}

/// design §3.8's literal `DeferRow`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DeferRow {
    pub kind: DeferKind,
    pub body: BlockId,
    pub stmt_order: u16,
}

#[derive(Clone, Debug, Default)]
pub struct DeferPool {
    rows: Vec<DeferRow>,
}

impl DeferPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, row: DeferRow) -> DeferId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        DeferId(i)
    }

    /// Clamped to the pool ([`crate::inst::clamp_range`]): the range comes out
    /// of a row that arbitrary FMIR is free to malform.
    pub fn get(&self, range: Range<u32>) -> &[DeferRow] {
        &self.rows[crate::inst::clamp_range(range, self.rows.len())]
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

/// design §3.5's literal `Discharge` enum: how a linear obligation was
/// satisfied on one scope-exit edge.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Discharge {
    MovedTo(crate::ids::InstId),
    /// `BodyId` in the design's prose is exactly a `DeferRow.body`, i.e. a
    /// `BlockId` — no separate `BodyId` newtype is introduced.
    /// [decision: reuse `BlockId` for the design's `BodyId`]
    DeferredBody(ScopeId, BlockId),
    Raised(crate::ids::InstId),
    Returned,
}

/// One node of the scope tree (design §3.2).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ScopeRow {
    pub parent: ScopeId,
    pub brand: BrandId,
    pub defers: Range<u32>,
    pub obligations: Range<u32>,
    pub region: RegionId,
}

impl ScopeRow {
    pub const fn root(brand: BrandId) -> Self {
        ScopeRow {
            parent: ScopeId::NONE,
            brand,
            defers: 0..0,
            obligations: 0..0,
            region: RegionId::NONE,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ScopePool {
    rows: Vec<ScopeRow>,
}

impl ScopePool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, row: ScopeRow) -> ScopeId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        ScopeId(i)
    }

    pub fn row(&self, id: ScopeId) -> ScopeRow {
        self.rows[id.index()].clone()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (ScopeId, ScopeRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (ScopeId(i as u32), r.clone()))
    }

    /// Is `ancestor` `scope` itself or one of its transitive parents? Used by
    /// the scoped-projection extent check (design §3.4) and is kept
    /// termination-safe (`ScopeId::NONE` stops the walk) even over a
    /// hand-written or fuzzed pool that is not guaranteed acyclic —
    /// `verify()` separately checks the tree is acyclic before anything
    /// calls this. [decision: bounded by `self.len()` iterations rather than
    /// trusting acyclicity, so a malformed cyclic pool can never hang this
    /// crate's own tests]
    pub fn is_ancestor_or_self(&self, scope: ScopeId, ancestor: ScopeId) -> bool {
        let mut cur = scope;
        for _ in 0..=self.rows.len() {
            if cur == ancestor {
                return true;
            }
            if cur == ScopeId::NONE {
                return false;
            }
            cur = self.row(cur).parent;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn place_list_pool_slices_round_trip() {
        let mut pool = PlaceListPool::new();
        let places = [PlaceId(1), PlaceId(2), PlaceId(3)];
        let range = pool.push_list(&places);
        assert_eq!(pool.get(range), &places);
    }

    #[test]
    fn ancestor_walk_reaches_root() {
        let mut scopes = ScopePool::new();
        let root = scopes.push(ScopeRow::root(BrandId::NONE));
        let mut child = ScopeRow::root(BrandId::NONE);
        child.parent = root;
        let child = scopes.push(child);
        assert!(scopes.is_ancestor_or_self(child, root));
        assert!(scopes.is_ancestor_or_self(child, child));
        assert!(!scopes.is_ancestor_or_self(root, child));
    }

    #[test]
    fn ancestor_walk_terminates_on_a_cycle() {
        let mut scopes = ScopePool::new();
        let a = scopes.push(ScopeRow::root(BrandId::NONE));
        let mut b_row = ScopeRow::root(BrandId::NONE);
        b_row.parent = a;
        let b = scopes.push(b_row);
        // Corrupt `a`'s parent to point at `b`, forming a cycle no real
        // builder would ever produce.
        let rows = &mut scopes.rows;
        rows[a.index()].parent = b;
        assert!(!scopes.is_ancestor_or_self(a, ScopeId(999)));
    }
}
