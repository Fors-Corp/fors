//! The hash-consing table (design `docs/design/type-checker.md` §4.1,
//! `cons.rs`): open addressing with linear probing, keys `u64`, values `u32`,
//! mixed with this workspace's one avalanche step
//! (`fors_index::fingerprint::splitmix64`). No `std::HashMap` on the hot path
//! and no `RandomState`, so interning order — and therefore every `TyId` in a
//! build — is reproducible.
//!
//! The table stores the 64-bit key *alongside* the value, which buys two
//! things: growing rehashes without asking the caller to recompute anything,
//! and — more importantly — the caller verifies the candidate row itself
//! ([`ConsTable::lookup`] takes an equality closure), so a 64-bit hash
//! collision costs one extra probe instead of silently aliasing two distinct
//! types. That is why the design's "one table for rows, args, trait refs, proj
//! keys and fn tys" is implemented here as one *type* instantiated once per
//! pool rather than one shared table: with one shared table a cross-pool hash
//! collision would hand the equality closure an index into the wrong pool,
//! where it could compare a valid-but-unrelated entry and return it. Seven
//! small tables cost a few hundred bytes more and remove that failure class
//! entirely.

use fors_index::fingerprint::splitmix64;

/// Marks an empty slot. A pool can therefore hold at most `u32::MAX` entries,
/// which is also the ceiling every index newtype in this crate already has.
const EMPTY: u32 = u32::MAX;

/// Load factor numerator/denominator: grow at 7/8 full. Linear probing wants
/// headroom; 7/8 with a good mixer keeps the average probe count near 1.
const LOAD_NUM: usize = 7;
const LOAD_DEN: usize = 8;

pub struct ConsTable {
    keys: Vec<u64>,
    vals: Vec<u32>,
    mask: usize,
    len: usize,
}

impl Default for ConsTable {
    fn default() -> Self {
        Self::new()
    }
}

impl ConsTable {
    pub fn new() -> ConsTable {
        Self::with_capacity(64)
    }

    /// `capacity` is rounded up to a power of two (the mask is the whole point
    /// of a power-of-two table: index selection is one `&`, never a `%`).
    pub fn with_capacity(capacity: usize) -> ConsTable {
        let cap = capacity.max(8).next_power_of_two();
        ConsTable { keys: vec![0; cap], vals: vec![EMPTY; cap], mask: cap - 1, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Mixes an arbitrary `(a, b, c)` triple into a table key. Callers use it
    /// so every pool hashes the same way; `salt` separates the domains within
    /// a pool (a row's `(tag, a, b, quals)` versus an args list's length and
    /// contents, say) without needing a second hash function.
    pub fn key3(salt: u64, a: u64, b: u64, c: u64) -> u64 {
        let mut h = splitmix64(salt ^ a);
        h = splitmix64(h ^ b);
        splitmix64(h ^ c)
    }

    /// Folds a slice of `u32`s (an args list, a bound list) into a table key,
    /// length first so `[x]` and `[x, x]` cannot collide structurally.
    pub fn key_slice(salt: u64, xs: &[u32]) -> u64 {
        Self::key_iter(salt, xs.len(), xs.iter().map(|&x| x as u64))
    }

    /// [`key_slice`] over any word sequence, so a caller with the words in a
    /// struct-of-arrays or a newtype slice need not copy them into a `Vec`
    /// first. `len` is folded first exactly as `key_slice` folds a slice's.
    ///
    /// [`key_slice`]: ConsTable::key_slice
    pub fn key_iter(salt: u64, len: usize, xs: impl Iterator<Item = u64>) -> u64 {
        let mut h = splitmix64(salt ^ len as u64);
        for x in xs {
            h = splitmix64(h ^ x);
        }
        h
    }

    /// Returns the value whose key is `key` and for which `eq` holds, probing
    /// past hash collisions. `eq` is the caller's real equality on the pool
    /// entry, so this never confuses two entries that happen to hash alike.
    pub fn lookup<F: FnMut(u32) -> bool>(&self, key: u64, mut eq: F) -> Option<u32> {
        let mut i = (key as usize) & self.mask;
        loop {
            let v = self.vals[i];
            if v == EMPTY {
                return None;
            }
            if self.keys[i] == key && eq(v) {
                return Some(v);
            }
            i = (i + 1) & self.mask;
        }
    }

    /// Inserts `(key, val)`. The caller must have just failed a [`lookup`] for
    /// the same key and entry, so duplicates are impossible by construction.
    ///
    /// [`lookup`]: ConsTable::lookup
    pub fn insert(&mut self, key: u64, val: u32) {
        debug_assert_ne!(val, EMPTY, "u32::MAX is reserved for the empty slot");
        if (self.len + 1) * LOAD_DEN > self.keys.len() * LOAD_NUM {
            self.grow();
        }
        let mut i = (key as usize) & self.mask;
        while self.vals[i] != EMPTY {
            i = (i + 1) & self.mask;
        }
        self.keys[i] = key;
        self.vals[i] = val;
        self.len += 1;
    }

    fn grow(&mut self) {
        let cap = self.keys.len() * 2;
        let old_keys = std::mem::replace(&mut self.keys, vec![0; cap]);
        let old_vals = std::mem::replace(&mut self.vals, vec![EMPTY; cap]);
        self.mask = cap - 1;
        for (k, v) in old_keys.into_iter().zip(old_vals) {
            if v == EMPTY {
                continue;
            }
            let mut i = (k as usize) & self.mask;
            while self.vals[i] != EMPTY {
                i = (i + 1) & self.mask;
            }
            self.keys[i] = k;
            self.vals[i] = v;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_lookup_round_trips() {
        let mut t = ConsTable::new();
        for i in 0..1000u32 {
            let k = ConsTable::key3(0, i as u64, 0, 0);
            assert_eq!(t.lookup(k, |v| v == i), None);
            t.insert(k, i);
        }
        assert_eq!(t.len(), 1000);
        for i in 0..1000u32 {
            let k = ConsTable::key3(0, i as u64, 0, 0);
            assert_eq!(t.lookup(k, |v| v == i), Some(i));
        }
    }

    #[test]
    fn colliding_keys_are_separated_by_the_equality_closure() {
        // Two entries deliberately stored under the SAME key: the closure is
        // what tells them apart, which is the property the type store relies
        // on when a 64-bit hash collides.
        let mut t = ConsTable::new();
        t.insert(7, 1);
        t.insert(7, 2);
        assert_eq!(t.lookup(7, |v| v == 2), Some(2));
        assert_eq!(t.lookup(7, |v| v == 1), Some(1));
        assert_eq!(t.lookup(7, |v| v == 3), None);
    }

    #[test]
    fn key_slice_distinguishes_length() {
        assert_ne!(ConsTable::key_slice(0, &[5]), ConsTable::key_slice(0, &[5, 5]));
        assert_ne!(ConsTable::key_slice(0, &[1, 2]), ConsTable::key_slice(0, &[2, 1]));
        assert_eq!(ConsTable::key_slice(0, &[1, 2]), ConsTable::key_slice(0, &[1, 2]));
    }
}
