//! `spawn`/`parallel`/`with-arena` region shells (design §3.7, §1.2): "FMIR
//! must still **represent** them... M1 executes a `spawn` region by running
//! it inline, which IS the serial elision, and asserts the capture list is
//! well-formed" and ch05 Rule 9: "`detach` MUST carry an explicit typed
//! capture list as an IR operand; no pass MUST reconstruct it from alias
//! classes." FMIR's `spawn` is the direct ancestor of OIR's Tapir `detach`
//! (ch05 Rule 10), so this crate's `captures` list *is* Rule 9's list, one
//! level up. [decision: "detach" in the task's gate-test name
//! `verify_rejects_detach_without_captures` means an FMIR `spawn` region,
//! since FMIR has no `detach` opcode of its own — `detach`/`reattach` are
//! OIR-level names for what FMIR represents as `spawn`/`sync` (ch05
//! Definitions, Rule 10)]

use std::ops::Range;

use fors_fir::sig::Conv;

use crate::ids::{ABSENT, BrandId, CaptureId, RegionId, ValId};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RegionKind {
    Spawn,
    Parallel,
    WithArena,
}

/// One entry of a region's **typed** capture list (ch05 Rule 9): which
/// value, and by which convention it crosses into the region (moved, shared,
/// …) — reusing `fors_fir::sig::Conv` again, the same four-way convention a
/// call's arguments carry (the type checker's own captures are already
/// conventions in this sense, and FMIR should not invent a second vocabulary
/// for the same idea).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CaptureRow {
    pub value: ValId,
    pub conv: Conv,
}

#[derive(Clone, Debug, Default)]
pub struct CapturePool {
    rows: Vec<CaptureRow>,
}

impl CapturePool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn push(&mut self, row: CaptureRow) -> CaptureId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        CaptureId(i)
    }

    /// Clamped to the pool ([`crate::inst::clamp_range`]): the range comes out
    /// of a row that arbitrary FMIR is free to malform.
    pub fn get(&self, range: Range<u32>) -> &[CaptureRow] {
        &self.rows[crate::inst::clamp_range(range, self.rows.len())]
    }
}

/// One region shell. `captures` distinguishes three states, not two:
///
/// - **absent** (`ABSENT..ABSENT`): the capture list was never computed —
///   exactly the lowering bug ch05 Rule 9 exists to catch, and what
///   `verify_rejects_detach_without_captures` constructs by hand;
/// - **empty but present** (`n..n`, `n != ABSENT`): a `spawn` that
///   legitimately captures nothing (e.g. a closure over no outer bindings) —
///   accepted, since Rule 9 requires the list to be *explicit*, not
///   *non-empty*;
/// - **non-empty** (`n..m`, `m > n`): the ordinary case.
///
/// [decision: a real Rust `Option<Range<u32>>` would say the same thing more
/// idiomatically, but every other pool in this crate spells "absent" as an
/// in-band `u32::MAX` sentinel (design §3.1's fixed-width-row philosophy: no
/// `Option` inflating a row), so `captures` stays consistent with that rather
/// than being the one exception]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RegionRow {
    pub kind: RegionKind,
    pub captures: Range<u32>,
    /// `WithArena`'s brand; `BrandId::NONE` otherwise.
    pub brand: BrandId,
}

impl RegionRow {
    pub const ABSENT_CAPTURES: Range<u32> = ABSENT..ABSENT;

    pub fn captures_absent(&self) -> bool {
        self.captures.start == ABSENT
    }
}

#[derive(Clone, Debug, Default)]
pub struct RegionPool {
    rows: Vec<RegionRow>,
    pub captures: CapturePool,
}

impl RegionPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn push(&mut self, row: RegionRow) -> RegionId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        RegionId(i)
    }

    pub fn row(&self, id: RegionId) -> RegionRow {
        self.rows[id.index()].clone()
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (RegionId, RegionRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (RegionId(i as u32), r.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absent_and_empty_captures_are_distinguishable() {
        let absent = RegionRow {
            kind: RegionKind::Spawn,
            captures: RegionRow::ABSENT_CAPTURES,
            brand: BrandId::NONE,
        };
        let empty = RegionRow {
            kind: RegionKind::Spawn,
            captures: 0..0,
            brand: BrandId::NONE,
        };
        assert!(absent.captures_absent());
        assert!(!empty.captures_absent());
    }
}
