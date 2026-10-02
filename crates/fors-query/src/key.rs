//! Query identity (design `docs/design/type-checker.md` §9): `QueryKey`,
//! `Revision` and the value hash every node is compared by.

/// One node of the DAG, named by its query kind and up to two `u32`
/// payload columns.
///
/// Every key in design §9.1 fits: a unit key (`file_set()`,
/// `module_graph()`, `infinite_size()`) uses neither column, a `FileId` /
/// `ModuleId` / `HeadKey` one, a `DeclKey` both (its stable 64-bit
/// identity split high/low), and a pair key (`impls_for(tr, h)`,
/// `candidate_traits(h, m)`) one each.
///
/// The engine stores nothing but this key, a [`ValueHash`] and the
/// dependency edges: the *memo value* of a query lives in the query set's
/// own struct-of-arrays, keyed by the same columns. That is how §9's "memo
/// values are `Arc<dyn Any>`-free: each query type has its own SoA memo" is
/// met — the engine never learns a value's type, so there is nothing to
/// erase.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct QueryKey {
    pub kind: u16,
    pub a: u32,
    pub b: u32,
}

impl QueryKey {
    pub const fn new(kind: u16, a: u32, b: u32) -> QueryKey {
        QueryKey { kind, a, b }
    }

    /// A whole-build query: `file_set()`, `module_graph()`,
    /// `infinite_size()`.
    pub const fn unit(kind: u16) -> QueryKey {
        QueryKey { kind, a: 0, b: 0 }
    }

    /// A query keyed by one id.
    pub const fn one(kind: u16, a: u32) -> QueryKey {
        QueryKey { kind, a, b: 0 }
    }

    /// A query keyed by a 64-bit identity (a stable declaration key),
    /// split across both columns.
    pub const fn wide(kind: u16, k: u64) -> QueryKey {
        QueryKey {
            kind,
            a: (k >> 32) as u32,
            b: k as u32,
        }
    }

    /// The 64-bit identity [`QueryKey::wide`] packed.
    pub const fn as_wide(self) -> u64 {
        ((self.a as u64) << 32) | self.b as u64
    }
}

/// The hash of a query's value. A derived query is re-executed when a
/// dependency's hash changed; its dependents are *not* woken when its own
/// hash comes out the same (§9's red-green early cutoff).
pub type ValueHash = u128;

/// A monotone build counter. Every changed input bumps it; a node records
/// the revision it was last verified at and the revision its value last
/// changed at, and those two numbers are the whole invalidation rule.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Revision(pub u64);

impl Revision {
    pub const ZERO: Revision = Revision(0);
}

impl std::fmt::Display for Revision {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "r{}", self.0)
    }
}
