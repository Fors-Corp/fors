//! **Exit edges**: everything a scope exit carries, as DATA on the edge
//! (design §3.5, §3.8; `type-checker.md` §13 I8b's `D7` and `D8`).
//!
//! `fors-lower` builds these rows from I8b's side tables; `verify()` ASSERTS
//! them against [`crate::scope::DeferPool`] and [`crate::scope::ScopeRow`]'s
//! obligations (design §3.8: "the verifier (asserting every exit edge of a
//! scope carries exactly the right multiset)"; §3.5: "The interpreter does
//! **not** re-derive this ... but it **asserts** it"); `fors-interp`
//! EXECUTES them. Nothing re-derives which bodies run or what discharged an
//! obligation — that is I8b's answer, carried here.
//!
//! One edge's execution order is fixed by `type-checker.md` §13 I8b and is
//! the order `fors-lower` must reproduce and the interpreter must execute:
//!
//! 1. the returned or raised operand is evaluated and moved into the result
//!    (ch01 R23a) — structural, by block order (design §3.8), so this table
//!    carries nothing for it;
//! 2. [`ExitEdgeRow::pending`]: the pending bodies of the scopes being
//!    left, innermost scope first, each scope's in ONE reverse `stmt_order`
//!    sequence interleaving `Defer` and `ErrDefer`, `ErrDefer` present only
//!    on an error exit (ch01 R23a, R23b);
//! 3. [`ExitEdgeRow::drops`]: the drops of the remaining non-linear
//!    bindings of those scopes — AFTER the bodies (R23d(a), R23d(f));
//! 4. [`ExitEdgeRow::discharges`]: ch01 R22h's check on what is left, one
//!    [`crate::scope::Discharge`] per obligation of the scopes being left.
//!
//! A `trap` is **not** an exit (ch01 R23f, R22d, ch02 R7): it runs none of
//! (2) or (3) and discharges nothing, so a `trap`-terminated block MUST
//! carry no row here at all — [`crate::diag::DiagCode::TrapHasExitEdge`].
//!
//! [decision: one `ExitEdgePool` on `DeclFmir` keyed by `(from, to)` rather
//! than a per-terminator inline field. design §3.1 fixes `InstRow` at
//! `op, a, b, c, ty, site` with no room for four more ranges, and a
//! `cond_br`/`switch_discr` has SEVERAL exit edges out of one terminator —
//! so the edge, not the terminator, is the row.]

use std::ops::Range;

use crate::ids::{ABSENT, BlockId, DeferId, ExitEdgeId, PlaceId, ScopeId};
use crate::scope::{Discharge, PlaceListPool};

/// Is this exit edge an **error exit** (ch02 R16)? `ErrDefer` bodies run on
/// `Error` edges and never on `Normal` ones (ch01 R23b). A handler that
/// yields a value makes a NORMAL exit (ch02 R16, design §5.4), which is
/// exactly why this is carried rather than inferred from the terminator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExitKind {
    Normal,
    Error,
}

impl ExitKind {
    pub const fn as_u32(self) -> u32 {
        match self {
            ExitKind::Normal => 0,
            ExitKind::Error => 1,
        }
    }

    pub const fn from_u32(v: u32) -> Option<ExitKind> {
        Some(match v {
            0 => ExitKind::Normal,
            1 => ExitKind::Error,
            _ => return None,
        })
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            ExitKind::Normal => "normal",
            ExitKind::Error => "error",
        }
    }
}

/// One obligation and what discharged it on this edge (design §3.5's
/// `Discharge`, plus the `PlaceId` it answers for). ch01 R22h is checked
/// "AFTER the pending `defer`/`errdefer` bodies ... have been accounted
/// for", so a `Discharge::DeferredBody` row is the normal shape for a place
/// a body moves (R22d(iii), R23d(b)).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DischargeRow {
    pub place: PlaceId,
    pub how: Discharge,
}

/// One exit edge of the CFG. `to == BlockId::NONE` is a **function** exit
/// (`ret`/`raise`), which has no successor block but is still an exit of
/// every scope up to the body's own.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExitEdgeRow {
    /// The block whose terminator leaves the scopes.
    pub from: BlockId,
    /// The successor this edge goes to, or [`BlockId::NONE`] for a function
    /// exit.
    pub to: BlockId,
    pub kind: ExitKind,
    /// The scopes being left, **innermost first** (step 2's order):
    /// a range into the pool's scope list. `verify()` asserts it is the
    /// parent chain from `from`'s own scope outward
    /// ([`crate::diag::DiagCode::ExitEdgeScopesNotAChain`]): the pending
    /// order is derived from this list, so the list's order is the order.
    pub scopes: Range<u32>,
    /// Step 2: the pending bodies, already in execution order.
    pub pending: Range<u32>,
    /// Step 3: the non-linear bindings dropped after the bodies.
    pub drops: Range<u32>,
    /// Step 4: one row per obligation of the scopes being left.
    pub discharges: Range<u32>,
}

impl ExitEdgeRow {
    /// A normal edge leaving no scope and running nothing — the shape every
    /// builder starts from and then fills.
    pub const fn plain(from: BlockId, to: BlockId, kind: ExitKind) -> Self {
        ExitEdgeRow {
            from,
            to,
            kind,
            scopes: 0..0,
            pending: 0..0,
            drops: 0..0,
            discharges: 0..0,
        }
    }

    pub fn is_function_exit(&self) -> bool {
        self.to.0 == ABSENT
    }
}

/// The exit-edge table plus the four flat lists its ranges resolve into.
/// Same SoA discipline as every other pool here (design §3.1): `u32`
/// indices, range-interned slices, no `Option` inflating a row.
#[derive(Clone, Debug, Default)]
pub struct ExitEdgePool {
    rows: Vec<ExitEdgeRow>,
    scope_list: Vec<ScopeId>,
    pending: Vec<DeferId>,
    drops: PlaceListPool,
    discharges: Vec<DischargeRow>,
}

impl ExitEdgePool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn push(&mut self, row: ExitEdgeRow) -> ExitEdgeId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        ExitEdgeId(i)
    }

    pub fn push_scopes(&mut self, scopes: &[ScopeId]) -> Range<u32> {
        let start = self.scope_list.len() as u32;
        self.scope_list.extend_from_slice(scopes);
        start..(self.scope_list.len() as u32)
    }

    pub fn push_pending(&mut self, pending: &[DeferId]) -> Range<u32> {
        let start = self.pending.len() as u32;
        self.pending.extend_from_slice(pending);
        start..(self.pending.len() as u32)
    }

    pub fn push_drops(&mut self, drops: &[PlaceId]) -> Range<u32> {
        self.drops.push_list(drops)
    }

    pub fn push_discharges(&mut self, rows: &[DischargeRow]) -> Range<u32> {
        let start = self.discharges.len() as u32;
        self.discharges.extend_from_slice(rows);
        start..(self.discharges.len() as u32)
    }

    pub fn row(&self, id: ExitEdgeId) -> ExitEdgeRow {
        self.rows[id.index()].clone()
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (ExitEdgeId, ExitEdgeRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (ExitEdgeId(i as u32), r.clone()))
    }

    /// Clamped to the pool ([`crate::inst::clamp_range`]) like every other
    /// accessor whose range comes out of a row arbitrary FMIR may malform.
    pub fn scopes(&self, range: Range<u32>) -> &[ScopeId] {
        &self.scope_list[crate::inst::clamp_range(range, self.scope_list.len())]
    }

    pub fn pending(&self, range: Range<u32>) -> &[DeferId] {
        &self.pending[crate::inst::clamp_range(range, self.pending.len())]
    }

    pub fn drops(&self, range: Range<u32>) -> &[PlaceId] {
        self.drops.get(range)
    }

    pub fn discharges(&self, range: Range<u32>) -> &[DischargeRow] {
        &self.discharges[crate::inst::clamp_range(range, self.discharges.len())]
    }

    /// The edge a terminator takes to `to` (or [`BlockId::NONE`] for a
    /// function exit). The interpreter's one lookup: a terminator with no
    /// row here leaves no scope and runs nothing.
    pub fn find(&self, from: BlockId, to: BlockId) -> Option<(ExitEdgeId, ExitEdgeRow)> {
        self.rows
            .iter()
            .enumerate()
            .find(|(_, r)| r.from == from && r.to == to)
            .map(|(i, r)| (ExitEdgeId(i as u32), r.clone()))
    }

    /// Does any edge leave `from`? Used by the verifier's "a `trap` is not
    /// an exit" check.
    pub fn any_from(&self, from: BlockId) -> bool {
        self.rows.iter().any(|r| r.from == from)
    }

    /// For `encode.rs` only: the raw backing lists and their inverse, so a
    /// decoded pool lands its items back at the exact positions the ranges
    /// already stored in [`ExitEdgeRow`]s point at.
    pub fn raw(&self) -> (&[ScopeId], &[DeferId], &[PlaceId], &[DischargeRow]) {
        (
            &self.scope_list,
            &self.pending,
            self.drops.as_slice(),
            &self.discharges,
        )
    }

    pub fn from_raw(
        rows: Vec<ExitEdgeRow>,
        scope_list: Vec<ScopeId>,
        pending: Vec<DeferId>,
        drops: Vec<PlaceId>,
        discharges: Vec<DischargeRow>,
    ) -> Self {
        ExitEdgePool {
            rows,
            scope_list,
            pending,
            drops: PlaceListPool::from_raw(drops),
            discharges,
        }
    }

    /// `canonicalize`'s hook: remap every `BlockId` this pool stores, in
    /// place. [`ExitEdgeRow::to`] of [`BlockId::NONE`] is left alone — it is
    /// the absent sentinel, not a block index.
    pub fn remap_blocks(&mut self, f: impl Fn(u32) -> u32) {
        for row in &mut self.rows {
            row.from = BlockId(f(row.from.0));
            if row.to.0 != ABSENT {
                row.to = BlockId(f(row.to.0));
            }
        }
    }

    /// `canonicalize`'s second hook: a [`Discharge::DeferredBody`] names a
    /// body `BlockId` too.
    pub fn remap_discharge_blocks(&mut self, f: impl Fn(u32) -> u32) {
        for row in &mut self.discharges {
            if let Discharge::DeferredBody(scope, body) = row.how {
                row.how = Discharge::DeferredBody(scope, BlockId(f(body.0)));
            }
        }
    }
}

/// The pending bodies that MUST run on an edge of `kind` leaving `scopes`
/// (innermost first): ch01 R23a's reverse textual order, R23b's
/// `ErrDefer`-only-on-error filter, interleaved across kinds in ONE
/// sequence per scope.
///
/// This is the verifier's expectation and nothing else: the interpreter
/// executes [`ExitEdgeRow::pending`] as carried, so a lowering that gets
/// this wrong is REPORTED, not silently corrected (design §3.8).
pub fn expected_pending(
    scopes: &crate::scope::ScopePool,
    defers: &crate::scope::DeferPool,
    leaving: &[ScopeId],
    kind: ExitKind,
) -> Vec<DeferId> {
    let mut out = Vec::new();
    for scope in leaving {
        if scope.index() >= scopes.len() {
            continue;
        }
        let range = scopes.row(*scope).defers;
        let start = range.start;
        let rows = defers.get(range);
        let mut here: Vec<(u16, DeferId)> = rows
            .iter()
            .enumerate()
            .filter(|(_, r)| r.kind == crate::scope::DeferKind::Defer || kind == ExitKind::Error)
            .map(|(i, r)| (r.stmt_order, DeferId(start + i as u32)))
            .collect();
        // Reverse textual order, interleaved across kinds: ONE sort key, the
        // statement order, descending. `sort_by_key` is stable, so two rows
        // that (malformed FMIR only) share a `stmt_order` keep their pool
        // order; `Reverse` makes it descending without a comparator.
        here.sort_by_key(|(order, _)| std::cmp::Reverse(*order));
        out.extend(here.into_iter().map(|(_, id)| id));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::BrandId;
    use crate::scope::{DeferKind, DeferPool, DeferRow, ScopePool, ScopeRow};

    /// Two scopes, the inner one with `defer`(0), `errdefer`(1),
    /// `defer`(2) — the interleaved shape ch01 R23b fixes.
    fn two_scopes() -> (ScopePool, DeferPool, ScopeId, ScopeId) {
        let mut defers = DeferPool::new();
        for (kind, order) in [
            (DeferKind::Defer, 0u16),
            (DeferKind::ErrDefer, 1),
            (DeferKind::Defer, 2),
        ] {
            defers.push(DeferRow {
                kind,
                body: BlockId(10 + order as u32),
                stmt_order: order,
            });
        }
        defers.push(DeferRow {
            kind: DeferKind::Defer,
            body: BlockId(20),
            stmt_order: 0,
        });
        let mut scopes = ScopePool::new();
        let outer = scopes.push(ScopeRow {
            parent: ScopeId::NONE,
            brand: BrandId::NONE,
            defers: 3..4,
            obligations: 0..0,
            region: crate::ids::RegionId::NONE,
        });
        let inner = scopes.push(ScopeRow {
            parent: outer,
            brand: BrandId::NONE,
            defers: 0..3,
            obligations: 0..0,
            region: crate::ids::RegionId::NONE,
        });
        (scopes, defers, outer, inner)
    }

    #[test]
    fn normal_exit_skips_errdefer_and_runs_in_reverse_order() {
        let (scopes, defers, outer, inner) = two_scopes();
        let got = expected_pending(&scopes, &defers, &[inner, outer], ExitKind::Normal);
        // inner: stmt_order 2 then 0 (the errdefer at 1 is skipped), then
        // the outer scope's single body.
        assert_eq!(got, vec![DeferId(2), DeferId(0), DeferId(3)]);
    }

    #[test]
    fn error_exit_interleaves_errdefer_in_one_reverse_sequence() {
        let (scopes, defers, outer, inner) = two_scopes();
        let got = expected_pending(&scopes, &defers, &[inner, outer], ExitKind::Error);
        assert_eq!(
            got,
            vec![DeferId(2), DeferId(1), DeferId(0), DeferId(3)],
            "one reverse stmt_order sequence, kinds interleaved (ch01 R23b)"
        );
    }

    #[test]
    fn find_distinguishes_the_two_edges_of_one_terminator() {
        let mut pool = ExitEdgePool::new();
        pool.push(ExitEdgeRow::plain(BlockId(0), BlockId(1), ExitKind::Normal));
        pool.push(ExitEdgeRow::plain(BlockId(0), BlockId(2), ExitKind::Error));
        assert_eq!(
            pool.find(BlockId(0), BlockId(2)).map(|(_, r)| r.kind),
            Some(ExitKind::Error)
        );
        assert!(pool.find(BlockId(0), BlockId(3)).is_none());
        assert!(pool.any_from(BlockId(0)));
        assert!(!pool.any_from(BlockId(5)));
    }

    #[test]
    fn a_function_exit_edge_is_recognised() {
        let row = ExitEdgeRow::plain(BlockId(0), BlockId::NONE, ExitKind::Normal);
        assert!(row.is_function_exit());
        assert!(!ExitEdgeRow::plain(BlockId(0), BlockId(1), ExitKind::Normal).is_function_exit());
    }
}
