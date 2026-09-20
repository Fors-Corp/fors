//! `DepSet`: what typing one body read (design §9, the `check_body` node's
//! in-edges).
//!
//! ch09 R2 makes the SIGNATURE the only interface between declarations, so
//! a body's dependency key is the set of declarations whose signature it
//! consulted, paired with each one's `sig_hash`. I3 records the set; I9's
//! query engine turns it into the DAG's edges and the invalidation test.
//!
//! MARC: the design puts the query DAG in `fors-query`, so the obvious
//! home for `DepSet` is there — but I9 makes `fors-query` the crate that
//! WRAPS `fors-check`, and a `fors-check -> fors-query` dependency would
//! invert that the moment it is written. The recording therefore lives
//! beside the code that does the reading, and `fors-query` will consume it
//! as data.

use fors_fir::Fir;
use fors_index::ids::DefId;

/// The declarations one body's typing read, in `DefId` order after
/// [`DepSet::finish`].
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct DepSet {
    defs: Vec<DefId>,
}

impl DepSet {
    pub fn new() -> DepSet {
        DepSet::default()
    }

    /// Records a read. The guard against the last entry makes the common
    /// case (the same callee twice in a row) free; `finish` does the rest.
    pub fn record(&mut self, def: DefId) {
        if def == fors_fir::NO_DEF {
            return;
        }
        if self.defs.last() == Some(&def) {
            return;
        }
        self.defs.push(def);
    }

    /// Sorts and deduplicates: the set, not the sequence, is the key.
    pub fn finish(&mut self) {
        self.defs.sort_unstable_by_key(|d| d.0);
        self.defs.dedup();
    }

    pub fn defs(&self) -> &[DefId] {
        &self.defs
    }

    pub fn len(&self) -> usize {
        self.defs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.defs.is_empty()
    }

    pub fn take(&mut self) -> DepSet {
        let mut out = DepSet { defs: std::mem::take(&mut self.defs) };
        out.finish();
        out
    }

    /// The 128-bit fold of the read declarations' `sig_hash`es: the value
    /// I9 compares to decide whether a body must be re-checked. Order-free
    /// by construction ([`DepSet::finish`] sorts), and a change to any one
    /// signature changes it.
    pub fn key(&self, fir: &Fir) -> u128 {
        let mut h: u128 = 0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835;
        for &d in &self.defs {
            let s = fir.sigs.sig_hash(d);
            h ^= s;
            h = h.rotate_left(17).wrapping_mul(0x0000_0100_0000_01b3);
        }
        h
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_dep_set_is_a_set_in_defid_order() {
        let mut d = DepSet::new();
        for x in [7u32, 3, 7, 3, 9, 3] {
            d.record(DefId(x));
        }
        d.finish();
        assert_eq!(d.defs(), &[DefId(3), DefId(7), DefId(9)]);
    }

    #[test]
    fn recording_nothing_leaves_it_empty() {
        let mut d = DepSet::new();
        d.record(fors_fir::NO_DEF);
        d.finish();
        assert!(d.is_empty());
    }
}
