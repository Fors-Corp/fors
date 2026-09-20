//! The `AliasSeed` pool of design §3.4a: the five sources of ch05 Rule 5,
//! **carried, not computed**. "Three of the five are erased by the checker
//! and are unrecoverable at OIR unless FMIR carries them" — this crate's
//! only job here is to hold the seed and let `verify()` check it is present
//! on every memory-producing instruction; deriving disjointness from it is
//! M5's (design §1.2).

use crate::ids::{BrandId, PlaceId};
use crate::op::Op;
use fors_fir::sig::Conv;

/// One of ch05 Rule 5's five alias-class sources, or `None` for "not
/// applicable to this instruction" (design §3.4a's literal enum, reproduced
/// verbatim: `AliasSeed { None, Conv(Conv), Own(PlaceId), Arena(BrandId),
/// Split { parent: PlaceId, side: u8 } }`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AliasSeed {
    /// Not a memory-producing instruction — the common case, and distinct
    /// from "memory-producing but the seed is missing" (design §1: `verify()`
    /// rejects the latter, never the former; see [`AliasSeedPool::missing`]).
    None,
    /// Parameter convention (ch01 Rule 7: "a `let` parameter is not a
    /// no-alias fact and MUST NOT seed one" — reusing `fors_fir::sig::Conv`
    /// rather than a local duplicate, since it is the exact same four-way
    /// convention `CallRow.convs` already carries). [decision: reuse
    /// `fors_fir::sig::Conv`, not a second `Conv` enum]
    Conv(Conv),
    /// Affine ownership: an `Own[T, A]` root is its own seed.
    Own(PlaceId),
    /// Arena brand id — "compile-time IR metadata only" (ch05 Rule 5): no
    /// execution ever reads it.
    Arena(BrandId),
    /// Split-token provenance (ch01 Rule 19b), recorded by `slice_range` and
    /// any split: `side` distinguishes the two halves so they get distinct
    /// seeds (`split_at_halves_get_distinct_seeds`).
    Split { parent: PlaceId, side: u8 },
}

/// One [`AliasSeed`] per [`crate::inst::InstPool`] row, positionally aligned
/// (index `i` here describes `InstPool` row `i`) rather than its own
/// range-indexed pool — design §3.4a calls it "its own pool" and says it is
/// "one `u64` per memory-producing instruction"; a parallel array indexed by
/// `InstId` gives O(1) lookup with no extra id type and costs nothing extra
/// on a non-memory-producing row (`AliasSeed::None` there anyway).
/// [decision: parallel `Vec<AliasSeed>` keyed by `InstId` position, not a
/// separately-indexed range pool]
#[derive(Clone, Debug, Default)]
pub struct AliasSeedPool {
    seeds: Vec<AliasSeed>,
}

impl AliasSeedPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.seeds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.seeds.is_empty()
    }

    /// Appends a row's seed; must be called once per `InstPool` push, in the
    /// same order, so index `i` here always describes `InstPool` row `i`.
    pub fn push(&mut self, seed: AliasSeed) {
        self.seeds.push(seed);
    }

    /// The seed of instruction `inst_index`. A seed column shorter than the
    /// instruction pool means the two fell out of lockstep, which is exactly
    /// the "memory op with no alias seed" `verify()` reports — so a missing
    /// entry reads as [`AliasSeed::None`] rather than panicking.
    pub fn get(&self, inst_index: usize) -> AliasSeed {
        self.seeds
            .get(inst_index)
            .copied()
            .unwrap_or(AliasSeed::None)
    }

    /// For `encode.rs` only: the raw backing storage, and its inverse. A
    /// `Vec<AliasSeed>` decoded off the wire is already in `InstId` position
    /// order (encode.rs writes it that way), so reconstruction is a plain
    /// move, no re-derivation.
    pub fn as_slice(&self) -> &[AliasSeed] {
        &self.seeds
    }

    pub fn from_raw(seeds: Vec<AliasSeed>) -> Self {
        AliasSeedPool { seeds }
    }

    /// ch05 Rule 5 / design §3.4a's verifier obligation: every
    /// [`Op::is_memory_producing`] row must carry a seed other than `None`.
    /// Returns the index of the first violation, if any.
    pub fn missing(&self, ops: &[Op]) -> Option<usize> {
        ops.iter()
            .zip(self.seeds.iter())
            .position(|(op, seed)| op.is_memory_producing() && *seed == AliasSeed::None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_sides_are_distinct_seeds() {
        let parent = PlaceId(0);
        let left = AliasSeed::Split { parent, side: 0 };
        let right = AliasSeed::Split { parent, side: 1 };
        assert_ne!(left, right);
    }

    #[test]
    fn missing_detects_none_on_a_memory_producing_row_only() {
        let mut pool = AliasSeedPool::new();
        pool.push(AliasSeed::None); // Op::Alloc below - VIOLATION
        pool.push(AliasSeed::None); // Op::Add - fine, not memory-producing
        let ops = [Op::Alloc, Op::Add(crate::op::ArithMode::Trap)];
        assert_eq!(pool.missing(&ops), Some(0));
    }
}
