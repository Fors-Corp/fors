//! Declaration identity (design §5.3): the name-based key a query is keyed on,
//! independent of every build-local row index. `DeclKey` is what survives an
//! edit that renumbers `DeclId`s and `DefId`s; `DefId` is only this build's row
//! number. [`DefKeys`] is the two-way map between them.

use fors_index::decl::DeclKind;
use fors_index::ids::DefId;
use fors_index::interner::Symbol;

use crate::cons::ConsTable;

macro_rules! index_newtype {
    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(pub u32);

        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

index_newtype!(DeclKeyId);
index_newtype!(ModulePathId);

/// No declaration key / no module path / no `DefId`.
pub const NO_DECL_KEY: DeclKeyId = DeclKeyId(u32::MAX);
pub const NO_DEF: DefId = DefId(u32::MAX);
/// The empty module path (a declaration in the root module), interned first.
pub const ROOT_PATH: ModulePathId = ModulePathId(0);

const SALT_PATH: u64 = 0x5041_5448_5041_5448;
const SALT_KEY: u64 = 0x4445_434b_4b45_5900;

/// Interned dotted module paths. The segments are [`Symbol`]s here, but a
/// declaration key's *hash* and its canonical encoding use the segment BYTES
/// (design §5.3), because `Symbol` values depend on intern order and two
/// builds must agree.
#[derive(Default)]
pub struct ModulePathTable {
    segs: Vec<Symbol>,
    start: Vec<u32>,
    len: Vec<u16>,
    cons: ConsTable,
}

impl ModulePathTable {
    pub fn new() -> ModulePathTable {
        let mut t = ModulePathTable::default();
        let root = t.intern(&[]);
        debug_assert_eq!(root, ROOT_PATH);
        t
    }

    pub fn intern(&mut self, segments: &[Symbol]) -> ModulePathId {
        let raw: Vec<u32> = segments.iter().map(|s| s.0).collect();
        let key = ConsTable::key_slice(SALT_PATH, &raw);
        if let Some(id) = self
            .cons
            .lookup(key, |v| self.segments(ModulePathId(v)) == segments)
        {
            return ModulePathId(id);
        }
        let id = ModulePathId(self.start.len() as u32);
        self.start.push(self.segs.len() as u32);
        self.len.push(segments.len() as u16);
        self.segs.extend_from_slice(segments);
        self.cons.insert(key, id.0);
        id
    }

    pub fn segments(&self, id: ModulePathId) -> &[Symbol] {
        let s = self.start[id.index()] as usize;
        let l = self.len[id.index()] as usize;
        &self.segs[s..s + l]
    }

    pub fn len(&self) -> usize {
        self.start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.start.is_empty()
    }
}

/// One declaration key, as callers build and read it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DeclKey {
    /// `NO_DECL_KEY` for a top-level item; the enclosing `impl`/`trait` for a
    /// method or associated item.
    pub parent: DeclKeyId,
    pub module: ModulePathId,
    pub kind: DeclKind,
    /// `None` for an `impl` (which has no name).
    pub name: Option<Symbol>,
    /// `impl`: a 32-bit fold of the header tokens, +1 per duplicate in source
    /// order. Zero for everything else.
    pub disamb: u32,
}

/// SoA, interned: equal keys are the same [`DeclKeyId`], so a query key is one
/// integer comparison.
#[derive(Default)]
pub struct DeclKeyTable {
    parent: Vec<DeclKeyId>,
    module: Vec<ModulePathId>,
    kind: Vec<DeclKind>,
    name: Vec<Option<Symbol>>,
    disamb: Vec<u32>,
    pub paths: ModulePathTable,
    cons: ConsTable,
}

impl DeclKeyTable {
    pub fn new() -> DeclKeyTable {
        DeclKeyTable {
            paths: ModulePathTable::new(),
            ..Default::default()
        }
    }

    pub fn intern(&mut self, key: DeclKey) -> DeclKeyId {
        let h = ConsTable::key3(
            SALT_KEY,
            ((key.parent.0 as u64) << 32) | key.module.0 as u64,
            ((key.kind as u64) << 32) | key.name.map_or(u32::MAX, |s| s.0) as u64,
            key.disamb as u64,
        );
        if let Some(id) = self.cons.lookup(h, |v| self.row(DeclKeyId(v)) == key) {
            return DeclKeyId(id);
        }
        let id = DeclKeyId(self.kind.len() as u32);
        self.parent.push(key.parent);
        self.module.push(key.module);
        self.kind.push(key.kind);
        self.name.push(key.name);
        self.disamb.push(key.disamb);
        self.cons.insert(h, id.0);
        id
    }

    pub fn row(&self, id: DeclKeyId) -> DeclKey {
        let i = id.index();
        DeclKey {
            parent: self.parent[i],
            module: self.module[i],
            kind: self.kind[i],
            name: self.name[i],
            disamb: self.disamb[i],
        }
    }

    pub fn parent_of(&self, id: DeclKeyId) -> DeclKeyId {
        self.parent[id.index()]
    }

    pub fn len(&self) -> usize {
        self.kind.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kind.is_empty()
    }
}

/// The head of a type after stripping qualifiers (ch09 Definitions,
/// design §5.3): the first column of an impl bucket's sort key.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum HeadKey {
    Prim(crate::ty::PrimKind),
    Nominal(DefId),
    Tuple(u16),
    Fn,
    Dyn(DefId),
    Param,
    Proj,
    Never,
    Unit,
    // MARC: design §5.3's list stops at `Unit`. `Error` is appended (at the
    // END, per the additive rule) because a poisoned type still has to answer
    // `head_key` — R10's recovery path looks it up like any other — and
    // silently reporting an error type as, say, `Unit` would make a bucket
    // lookup return impls for `()`. This variant's bucket is always empty.
    Error,
    /// A closed const argument in type position (R13): `Array[T, 4]`'s `4`.
    ConstVal,
    Brand,
}

impl HeadKey {
    /// A total, build-independent ordering column for `ImplIndex` (I2). The
    /// discriminant is in the high bits so the payload never crosses variants.
    pub fn as_u64(self) -> u64 {
        let (d, p): (u64, u64) = match self {
            HeadKey::Prim(k) => (1, k as u64),
            HeadKey::Nominal(d) => (2, d.0 as u64),
            HeadKey::Tuple(n) => (3, n as u64),
            HeadKey::Fn => (4, 0),
            HeadKey::Dyn(d) => (5, d.0 as u64),
            HeadKey::Param => (6, 0),
            HeadKey::Proj => (7, 0),
            HeadKey::Never => (8, 0),
            HeadKey::Unit => (9, 0),
            HeadKey::Error => (10, 0),
            HeadKey::ConstVal => (11, 0),
            HeadKey::Brand => (12, 0),
        };
        (d << 40) | p
    }
}

/// The two-way map between a build's `DefId` row numbers and the name-based
/// [`DeclKeyId`]s a query is keyed on (design §5.3: "`DefTable.key[def]` maps
/// one to the other; a map `DeclKeyId -> DefId` is rebuilt whenever
/// `decl_keys(file)` changes"). `fors-fir` needs both directions itself —
/// encoding writes a head's key bytes, decoding turns key bytes back into a
/// row — so the map lives here rather than in `fors-check`'s `DefTable`.
#[derive(Default)]
pub struct DefKeys {
    key: Vec<DeclKeyId>,
    def: Vec<DefId>,
}

impl DefKeys {
    pub fn new() -> DefKeys {
        DefKeys::default()
    }

    pub fn bind(&mut self, def: DefId, key: DeclKeyId) {
        if self.key.len() <= def.index() {
            self.key.resize(def.index() + 1, NO_DECL_KEY);
        }
        if self.def.len() <= key.index() {
            self.def.resize(key.index() + 1, NO_DEF);
        }
        self.key[def.index()] = key;
        self.def[key.index()] = def;
    }

    pub fn key_of(&self, def: DefId) -> DeclKeyId {
        self.key.get(def.index()).copied().unwrap_or(NO_DECL_KEY)
    }

    pub fn def_of(&self, key: DeclKeyId) -> DefId {
        self.def.get(key.index()).copied().unwrap_or(NO_DEF)
    }

    /// The `DefId` for `key`, allocating the next free row number if this
    /// build has not seen that declaration. Used by `decode` when a `.fmod`
    /// signature names a declaration that is not in this build's own tables.
    pub fn def_for_key(&mut self, key: DeclKeyId) -> DefId {
        let existing = self.def_of(key);
        if existing != NO_DEF {
            return existing;
        }
        let def = DefId(self.key.len() as u32);
        self.bind(def, key);
        def
    }

    pub fn defs(&self) -> usize {
        self.key.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_index::interner::Interner;

    fn key(
        names: &mut Interner,
        paths: &mut ModulePathTable,
        module: &[&str],
        name: &str,
    ) -> DeclKey {
        let segs: Vec<Symbol> = module.iter().map(|s| names.intern(s.as_bytes())).collect();
        DeclKey {
            parent: NO_DECL_KEY,
            module: paths.intern(&segs),
            kind: DeclKind::Struct,
            name: Some(names.intern(name.as_bytes())),
            disamb: 0,
        }
    }

    #[test]
    fn equal_keys_intern_equal() {
        let mut names = Interner::new();
        let mut t = DeclKeyTable::new();
        let a = key(&mut names, &mut t.paths, &["core", "text"], "Shape");
        let b = key(&mut names, &mut t.paths, &["core", "text"], "Shape");
        let c = key(&mut names, &mut t.paths, &["core"], "Shape");
        let ia = t.intern(a);
        let ib = t.intern(b);
        let ic = t.intern(c);
        assert_eq!(ia, ib);
        assert_ne!(ia, ic);
        assert_eq!(t.row(ia), a);
        assert_eq!(t.len(), 2);
    }

    #[test]
    fn def_keys_maps_both_ways_and_allocates() {
        let mut names = Interner::new();
        let mut t = DeclKeyTable::new();
        let row = key(&mut names, &mut t.paths, &["m"], "S");
        let k = t.intern(row);
        let mut d = DefKeys::new();
        d.bind(DefId(3), k);
        assert_eq!(d.key_of(DefId(3)), k);
        assert_eq!(d.def_of(k), DefId(3));
        let row2 = key(&mut names, &mut t.paths, &["m"], "T");
        let k2 = t.intern(row2);
        let fresh = d.def_for_key(k2);
        assert_eq!(d.def_for_key(k2), fresh);
        assert_ne!(fresh, DefId(3));
    }

    #[test]
    fn head_key_order_is_by_variant_then_payload() {
        assert!(
            HeadKey::Prim(crate::ty::PrimKind::I8).as_u64() < HeadKey::Nominal(DefId(0)).as_u64()
        );
        assert!(HeadKey::Nominal(DefId(1)).as_u64() < HeadKey::Nominal(DefId(2)).as_u64());
        assert!(HeadKey::Nominal(DefId(u32::MAX - 1)).as_u64() < HeadKey::Tuple(0).as_u64());
    }
}
