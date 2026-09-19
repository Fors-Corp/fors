//! Byte-string interning: `Symbol` is a small index into a build-wide
//! table, never an owned `String` per name. Interning order is whatever
//! order callers intern in; a build that always interns in the same
//! (deterministic) order gets the same `Symbol` values, but nothing here
//! reorders or sorts on its own, so callers that need order-independent
//! output must sort by the interned bytes (`Interner::resolve`), never by
//! `Symbol` value, wherever more than one legal intern order is possible
//! (e.g. multiple files indexed in parallel).

use std::collections::HashMap;

/// An interned byte-string. Stable for the lifetime of the `Interner` that
/// produced it; never compared across two different interners.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Symbol(pub u32);

/// Maps byte-strings to `Symbol`s and back. `HashMap` here only ever
/// determines whether a string was seen before (a lookup keyed on its
/// bytes, not iterated), so it never influences ordering or ids: the id
/// assigned to a new string is always `strings.len()` at the time it is
/// first interned, which is deterministic given a deterministic call
/// order.
pub struct Interner {
    strings: Vec<Box<[u8]>>,
    lookup: HashMap<Box<[u8]>, Symbol>,
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

impl Interner {
    pub fn new() -> Self {
        Interner { strings: Vec::new(), lookup: HashMap::new() }
    }

    /// Interns `bytes`, returning its `Symbol`. Repeated interning of
    /// equal bytes always returns the same `Symbol`.
    pub fn intern(&mut self, bytes: &[u8]) -> Symbol {
        if let Some(&sym) = self.lookup.get(bytes) {
            return sym;
        }
        let sym = Symbol(self.strings.len() as u32);
        let boxed: Box<[u8]> = bytes.into();
        self.strings.push(boxed.clone());
        self.lookup.insert(boxed, sym);
        sym
    }

    pub fn resolve(&self, sym: Symbol) -> &[u8] {
        &self.strings[sym.0 as usize]
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_bytes_same_symbol() {
        let mut i = Interner::new();
        let a = i.intern(b"foo");
        let b = i.intern(b"bar");
        let c = i.intern(b"foo");
        assert_eq!(a, c);
        assert_ne!(a, b);
        assert_eq!(i.resolve(a), b"foo");
    }

    #[test]
    fn ids_assigned_in_first_seen_order() {
        let mut i = Interner::new();
        assert_eq!(i.intern(b"z").0, 0);
        assert_eq!(i.intern(b"a").0, 1);
        assert_eq!(i.intern(b"z").0, 0);
        assert_eq!(i.len(), 2);
    }
}
