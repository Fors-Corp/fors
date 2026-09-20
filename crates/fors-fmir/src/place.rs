//! Places, moves and conventions (design §3.3): "A place is interned per
//! declaration (same shape as the type checker's own tape place id, extended
//! with `Deref` for `Own`/`Ref`)" — paraphrased rather than quoted verbatim,
//! since the literal crate name is exactly what
//! `tests/no_checker_dependency.rs` greps this whole directory for.

use std::ops::Range;

use fors_fir::ty::TyId;

use crate::ids::{PlaceId, ValId};

/// One projection step of a place path.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Seg {
    Field(u16),
    Index(ValId),
    Deref,
}

/// One interned place: a local slot plus a path of [`Seg`]s.
///
/// `root` is a **local slot** index (design §3.3: "root: u32 /*local
/// slot*/") — a per-declaration numbering of parameters and `let` bindings,
/// deliberately a bare `u32` rather than a `ValId`: a place exists whether or
/// not it currently holds a live value (`&out x` targets an *uninitialised*
/// slot, design §3.3's `borrow_out` row), so it cannot be indexed by the
/// value that (maybe) lives there.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PlaceRow {
    pub root: u32,
    pub segs: Range<u32>,
    pub ty: TyId,
}

/// Interned `(root, segs)` shapes plus the flat [`Seg`] backing storage the
/// `segs` ranges index into. Interning means two places with the same root
/// and the same projection path are the same [`PlaceId`], which is what lets
/// the verifier's scoped-projection and linear-obligation checks (design
/// §3.4, §3.5) compare places by id instead of walking paths.
#[derive(Clone, Debug, Default)]
pub struct PlacePool {
    rows: Vec<PlaceRow>,
    segs: Vec<Seg>,
}

impl PlacePool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn row(&self, id: PlaceId) -> PlaceRow {
        self.rows[id.index()].clone()
    }

    pub fn segs(&self, id: PlaceId) -> &[Seg] {
        let r = self.row(id);
        &self.segs[crate::inst::clamp_range(r.segs, self.segs.len())]
    }

    /// Interns `(root, path, ty)`, reusing an existing row with the same
    /// shape when one exists.
    pub fn intern(&mut self, root: u32, path: &[Seg], ty: TyId) -> PlaceId {
        for (i, row) in self.rows.iter().enumerate() {
            if row.root == root && row.ty == ty && self.segs_eq(row.segs.clone(), path) {
                return PlaceId(i as u32);
            }
        }
        let start = self.segs.len() as u32;
        self.segs.extend_from_slice(path);
        let end = self.segs.len() as u32;
        let id = PlaceId(self.rows.len() as u32);
        self.rows.push(PlaceRow {
            root,
            segs: start..end,
            ty,
        });
        id
    }

    fn segs_eq(&self, range: Range<u32>, path: &[Seg]) -> bool {
        let existing = &self.segs[range.start as usize..range.end as usize];
        existing == path
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (PlaceId, PlaceRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (PlaceId(i as u32), r.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_fir::ty::TY_UNIT;

    #[test]
    fn interning_is_shape_sensitive() {
        let mut pool = PlacePool::new();
        let a = pool.intern(0, &[Seg::Field(1)], TY_UNIT);
        let b = pool.intern(0, &[Seg::Field(1)], TY_UNIT);
        let c = pool.intern(0, &[Seg::Field(2)], TY_UNIT);
        let d = pool.intern(1, &[Seg::Field(1)], TY_UNIT);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(a, d);
        assert_eq!(pool.len(), 3);
    }

    #[test]
    fn segs_read_back_in_order() {
        let mut pool = PlacePool::new();
        let path = [Seg::Deref, Seg::Field(3), Seg::Index(ValId(9))];
        let id = pool.intern(2, &path, TY_UNIT);
        assert_eq!(pool.segs(id), &path);
    }
}
