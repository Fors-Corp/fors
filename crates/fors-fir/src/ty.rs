//! The type universe (design §5.1): parallel columns, hash-consed, so ch09
//! R9's "equality is syntactic on resolved, `Self`-expanded, normalised types"
//! is one integer comparison and nothing in the checker ever walks two types
//! to compare them.
//!
//! Three things carry their weight here:
//!
//! - **`quals` is part of the intern key.** `iso Buf` and `Buf` are different
//!   `TyId`s (R9 makes qualified and unqualified forms distinct types; R10 adds
//!   no conversion between them), and `unqual` gives the same row with the
//!   qualifiers cleared in one load, which is what every rule that says
//!   "after stripping qualifiers" needs.
//! - **`flags` is the OR of the children's flags, computed at intern time.**
//!   `subst_norm` on a monomorphic type is then one load and a branch
//!   ([`TyStore::is_monomorphic`]), not a walk — the single most-executed
//!   decision in the checker.
//! - **`unqual` and `flags` are filled in the same step as interning**, so
//!   there is no second pass and no possibility of a stale derived column.

use fors_index::ids::DefId;
use fors_index::interner::Symbol;

use crate::cons::ConsTable;
use crate::constval::ConstValue;
use crate::defpath::{DeclKeyId, HeadKey};
use crate::sig::Conv;

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

index_newtype!(TyId);
index_newtype!(ArgsId);
index_newtype!(TraitRefId);
index_newtype!(ProjKeyId);
index_newtype!(FnTyId);
index_newtype!(BrandId);
index_newtype!(ConstId);

/// The poisoned type: one row, so a recovered error never multiplies into a
/// second diagnostic (design §7.10).
pub const TY_ERROR: TyId = TyId(0);
pub const TY_UNIT: TyId = TyId(1);
pub const TY_NEVER: TyId = TyId(2);

/// "Absent", for every column that is optionally a type: a `raises` clause
/// that is not written (R7 makes absent distinct from every `raises E`), an
/// unbound slot, a member with no payload.
pub const NO_TY: TyId = TyId(u32::MAX);
/// The empty argument list, interned first so it is a constant.
pub const NO_ARGS: ArgsId = ArgsId(0);
pub const NO_CONST: ConstId = ConstId(u32::MAX);

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TyTag {
    Error,
    Unit,
    Never,
    /// `a` = [`PrimKind`].
    Prim,
    /// `a` = `DefId` of the struct/enum (prelude generic types — `Array`,
    /// `Slice`, `vector`, `mask`, `Own`, `Ref`, `Option`, `Range` — included),
    /// `b` = [`ArgsId`].
    Nominal,
    /// `b` = [`ArgsId`], length >= 1.
    Tuple,
    /// `a` = [`FnTyId`].
    Fn,
    /// `a` = [`TraitRefId`].
    Dyn,
    /// `a` = owner `DefId`, `b` = ordinal in the owner's own gparam list
    /// (a trait's `Self` is ordinal 0).
    Param,
    /// `a` = head [`TyId`] (rigid: `Param` or `Proj`), `b` = [`ProjKeyId`].
    Proj,
    /// `a` = [`BrandKind`], `b` = [`BrandId`].
    Brand,
    /// `a` = [`ConstId`], `b` = the `TyId` of its type (R13's closed const
    /// argument).
    ConstVal,
}

/// ch09 R3's complete list. No `f16`, no `char`, no 128-bit.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum PrimKind {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Bool,
    Str,
    RawPtr,
}

impl PrimKind {
    pub fn is_integer(self) -> bool {
        matches!(
            self,
            PrimKind::I8
                | PrimKind::I16
                | PrimKind::I32
                | PrimKind::I64
                | PrimKind::Isize
                | PrimKind::U8
                | PrimKind::U16
                | PrimKind::U32
                | PrimKind::U64
                | PrimKind::Usize
        )
    }

    pub fn is_float(self) -> bool {
        matches!(self, PrimKind::F32 | PrimKind::F64)
    }

    pub fn from_u8(v: u8) -> Option<PrimKind> {
        const ALL: [PrimKind; 15] = [
            PrimKind::I8,
            PrimKind::I16,
            PrimKind::I32,
            PrimKind::I64,
            PrimKind::Isize,
            PrimKind::U8,
            PrimKind::U16,
            PrimKind::U32,
            PrimKind::U64,
            PrimKind::Usize,
            PrimKind::F32,
            PrimKind::F64,
            PrimKind::Bool,
            PrimKind::Str,
            PrimKind::RawPtr,
        ];
        ALL.get(v as usize).copied()
    }
}

pub const Q_ISO: u8 = 1;
pub const Q_IMM: u8 = 2;
pub const Q_SECRET: u8 = 4;

/// ch01's qualifiers. `iso` and `imm` are mutually exclusive; `secret` is
/// orthogonal to both and may sit on either or on neither.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Quals(pub u8);

impl Quals {
    pub const NONE: Quals = Quals(0);
    pub const ISO: Quals = Quals(Q_ISO);
    pub const IMM: Quals = Quals(Q_IMM);
    pub const SECRET: Quals = Quals(Q_SECRET);

    pub fn is_iso(self) -> bool {
        self.0 & Q_ISO != 0
    }

    pub fn is_imm(self) -> bool {
        self.0 & Q_IMM != 0
    }

    pub fn is_secret(self) -> bool {
        self.0 & Q_SECRET != 0
    }

    pub fn is_none(self) -> bool {
        self.0 == 0
    }

    /// The union of two qualifier sets. Used when a substitution puts a
    /// qualified argument into a qualified parameter position (`iso T` with
    /// `T := secret Buf` is `iso secret Buf`).
    pub fn union(self, other: Quals) -> Quals {
        Quals(self.0 | other.0)
    }

    /// Whether this combination is well-formed (`iso imm` is not).
    pub fn is_consistent(self) -> bool {
        !(self.is_iso() && self.is_imm())
    }
}

pub const F_PARAM: u8 = 1;
pub const F_PROJ: u8 = 2;
pub const F_BRAND: u8 = 4;
pub const F_ERROR: u8 = 8;
pub const F_FRESH: u8 = 16;

/// Everything that makes a type non-monomorphic, i.e. everything
/// `subst_norm` could possibly have work to do on.
pub const F_OPEN: u8 = F_PARAM | F_PROJ | F_BRAND;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BrandKind {
    /// A brand parameter of a declaration: an ordinary phantom parameter.
    Param = 0,
    /// A brand created by a `with` block (ch01 R15): never in a signature.
    Fresh = 1,
}

/// A brand row. Brands are phantom parameters: they have no representation and
/// participate only in identity (R40 binds them by identity, never structurally).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BrandRow {
    Param { owner: DefId, ordinal: u16 },
    Fresh { owner: DeclKeyId, ordinal: u16 },
}

impl BrandRow {
    pub fn kind(self) -> BrandKind {
        match self {
            BrandRow::Param { .. } => BrandKind::Param,
            BrandRow::Fresh { .. } => BrandKind::Fresh,
        }
    }
}

/// The `Fn` pool. Conventions live on parameters (R7's equality is pairwise on
/// conventions), `result` defaults to [`TY_UNIT`], `raises` is [`NO_TY`] for a
/// non-raising signature (R7: absent is distinct from every `raises E`; R60
/// allows it to be a `Param`). `closure` is set only on a body's local layer —
/// a closure type equals no `fn` type (R7) but coerces to an equal one
/// (R10(b)) — and never in a signature.
#[derive(Default)]
pub struct FnTys {
    conv: Vec<Conv>,
    ty: Vec<TyId>,
    p_start: Vec<u32>,
    p_len: Vec<u8>,
    result: Vec<TyId>,
    raises: Vec<TyId>,
    closure: Vec<bool>,
}

impl FnTys {
    pub fn len(&self) -> usize {
        self.result.len()
    }

    pub fn is_empty(&self) -> bool {
        self.result.is_empty()
    }

    pub fn params(&self, id: FnTyId) -> (&[Conv], &[TyId]) {
        let s = self.p_start[id.index()] as usize;
        let l = self.p_len[id.index()] as usize;
        (&self.conv[s..s + l], &self.ty[s..s + l])
    }

    pub fn result(&self, id: FnTyId) -> TyId {
        self.result[id.index()]
    }

    pub fn raises(&self, id: FnTyId) -> TyId {
        self.raises[id.index()]
    }

    pub fn is_closure(&self, id: FnTyId) -> bool {
        self.closure[id.index()]
    }
}

const SALT_ROW: u64 = 0x524f_5700_524f_5700;
const SALT_ARGS: u64 = 0x4152_4753_4152_4753;
const SALT_TR: u64 = 0x5452_4546_5452_4546;
const SALT_PK: u64 = 0x504b_4559_504b_4559;
const SALT_FN: u64 = 0x464e_5459_464e_5459;
const SALT_BRAND: u64 = 0x4252_4e44_4252_4e44;
const SALT_CONST: u64 = 0x434f_4e53_544f_4e53;

/// 20 bytes per distinct core type in parallel columns, plus the pools.
pub struct TyStore {
    tag: Vec<TyTag>,
    a: Vec<u32>,
    b: Vec<u32>,
    quals: Vec<u8>,
    flags: Vec<u8>,
    unqual: Vec<TyId>,
    copyable: Vec<u8>,

    args: Vec<TyId>,
    args_start: Vec<u32>,
    args_len: Vec<u16>,

    trait_refs: Vec<(DefId, ArgsId)>,
    proj_keys: Vec<(TraitRefId, Symbol)>,
    fn_tys: FnTys,
    brands: Vec<BrandRow>,
    consts: Vec<ConstValue>,

    rows_cons: ConsTable,
    args_cons: ConsTable,
    tr_cons: ConsTable,
    pk_cons: ConsTable,
    fn_cons: ConsTable,
    brand_cons: ConsTable,
    const_cons: ConsTable,
}

impl Default for TyStore {
    fn default() -> Self {
        Self::new()
    }
}

impl TyStore {
    /// Interns, in this fixed order, the empty argument list and then
    /// [`TY_ERROR`], [`TY_UNIT`], [`TY_NEVER`], so those three constants are
    /// the same `TyId` in every store in every build.
    pub fn new() -> TyStore {
        let mut s = TyStore {
            tag: Vec::new(),
            a: Vec::new(),
            b: Vec::new(),
            quals: Vec::new(),
            flags: Vec::new(),
            unqual: Vec::new(),
            copyable: Vec::new(),
            args: Vec::new(),
            args_start: Vec::new(),
            args_len: Vec::new(),
            trait_refs: Vec::new(),
            proj_keys: Vec::new(),
            fn_tys: FnTys::default(),
            brands: Vec::new(),
            consts: Vec::new(),
            rows_cons: ConsTable::new(),
            args_cons: ConsTable::new(),
            tr_cons: ConsTable::new(),
            pk_cons: ConsTable::new(),
            fn_cons: ConsTable::new(),
            brand_cons: ConsTable::new(),
            const_cons: ConsTable::new(),
        };
        // MARC (I3): these three `intern` calls used to sit INSIDE
        // `debug_assert_eq!`, so a RELEASE build never created rows 0, 1
        // and 2 at all: the first type any release build interned became
        // `TY_ERROR`, the second `TY_UNIT` and the third `TY_NEVER`. It was
        // invisible while only signatures were lowered (nothing compared a
        // type against those constants) and showed up the moment a body
        // did: `let n = 1;` reported T0033 "a binding must not be given the
        // type `never`" in the release binary and nothing in the test
        // build. The calls are unconditional now, and the assertion is a
        // hard one — it runs once per store, and a store whose three
        // reserved rows are not 0/1/2 is not a store anything else in this
        // crate is true about.
        let empty = s.intern_args(&[]);
        let err = s.intern(TyTag::Error, 0, 0, Quals::NONE);
        let unit = s.intern(TyTag::Unit, 0, 0, Quals::NONE);
        let never = s.intern(TyTag::Never, 0, 0, Quals::NONE);
        assert_eq!(empty, NO_ARGS, "the empty argument list must be NO_ARGS");
        assert_eq!(err, TY_ERROR, "row 0 must be TY_ERROR");
        assert_eq!(unit, TY_UNIT, "row 1 must be TY_UNIT");
        assert_eq!(never, TY_NEVER, "row 2 must be TY_NEVER");
        s
    }

    pub fn len(&self) -> usize {
        self.tag.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tag.is_empty()
    }

    // ------------------------------------------------------------- accessors

    pub fn tag(&self, t: TyId) -> TyTag {
        self.tag[t.index()]
    }

    pub fn a(&self, t: TyId) -> u32 {
        self.a[t.index()]
    }

    pub fn b(&self, t: TyId) -> u32 {
        self.b[t.index()]
    }

    pub fn quals(&self, t: TyId) -> Quals {
        Quals(self.quals[t.index()])
    }

    pub fn flags(&self, t: TyId) -> u8 {
        self.flags[t.index()]
    }

    /// The same row with the qualifiers cleared — one load, no interning.
    pub fn unqual(&self, t: TyId) -> TyId {
        self.unqual[t.index()]
    }

    /// The single load `subst_norm` is built around: a type with no parameter,
    /// projection or brand anywhere inside it substitutes to itself.
    pub fn is_monomorphic(&self, t: TyId) -> bool {
        self.flags[t.index()] & F_OPEN == 0
    }

    /// R20's "rigid": a type parameter, `Self` in a trait, or a neutral
    /// projection. These are the only legal heads of a `Proj` row.
    pub fn is_rigid(&self, t: TyId) -> bool {
        matches!(self.tag[t.index()], TyTag::Param | TyTag::Proj)
    }

    pub fn is_error(&self, t: TyId) -> bool {
        self.flags[t.index()] & F_ERROR != 0
    }

    /// Lazy R23 cache: 0 unknown, 1 yes, 2 no.
    pub fn copyable_cached(&self, t: TyId) -> u8 {
        self.copyable[t.index()]
    }

    pub fn set_copyable(&mut self, t: TyId, answer: bool) {
        self.copyable[t.index()] = if answer { 1 } else { 2 };
    }

    pub fn args(&self, id: ArgsId) -> &[TyId] {
        let s = self.args_start[id.index()] as usize;
        let l = self.args_len[id.index()] as usize;
        &self.args[s..s + l]
    }

    pub fn args_vec(&self, id: ArgsId) -> Vec<TyId> {
        self.args(id).to_vec()
    }

    pub fn trait_ref(&self, id: TraitRefId) -> (DefId, ArgsId) {
        self.trait_refs[id.index()]
    }

    pub fn proj_key(&self, id: ProjKeyId) -> (TraitRefId, Symbol) {
        self.proj_keys[id.index()]
    }

    pub fn fn_tys(&self) -> &FnTys {
        &self.fn_tys
    }

    pub fn brand(&self, id: BrandId) -> BrandRow {
        self.brands[id.index()]
    }

    pub fn const_value(&self, id: ConstId) -> ConstValue {
        self.consts[id.index()]
    }

    /// ch09 Definitions' *head*: the outermost constructor after stripping
    /// qualifiers. The first column of an impl bucket's key (§7.6).
    pub fn head_key(&self, t: TyId) -> HeadKey {
        let i = t.index();
        match self.tag[i] {
            TyTag::Error => HeadKey::Error,
            TyTag::Unit => HeadKey::Unit,
            TyTag::Never => HeadKey::Never,
            TyTag::Prim => {
                HeadKey::Prim(PrimKind::from_u8(self.a[i] as u8).unwrap_or(PrimKind::RawPtr))
            }
            TyTag::Nominal => HeadKey::Nominal(DefId(self.a[i])),
            TyTag::Tuple => HeadKey::Tuple(self.args_len[self.b[i] as usize]),
            TyTag::Fn => HeadKey::Fn,
            TyTag::Dyn => HeadKey::Dyn(self.trait_refs[self.a[i] as usize].0),
            TyTag::Param => HeadKey::Param,
            TyTag::Proj => HeadKey::Proj,
            TyTag::Brand => HeadKey::Brand,
            TyTag::ConstVal => HeadKey::ConstVal,
        }
    }

    // --------------------------------------------------------------- pools

    pub fn intern_args(&mut self, xs: &[TyId]) -> ArgsId {
        // MARC (verification round): keyed by folding the ids directly — the
        // previous `Vec<u32>` copy was one heap allocation per interned list,
        // on the path every substituted constructor takes.
        let key = ConsTable::key_iter(SALT_ARGS, xs.len(), xs.iter().map(|t| t.0 as u64));
        if let Some(id) = self.args_cons.lookup(key, |v| self.args(ArgsId(v)) == xs) {
            return ArgsId(id);
        }
        let id = ArgsId(self.args_start.len() as u32);
        self.args_start.push(self.args.len() as u32);
        self.args_len
            .push(u16::try_from(xs.len()).expect("argument list longer than u16::MAX"));
        self.args.extend_from_slice(xs);
        self.args_cons.insert(key, id.0);
        id
    }

    pub fn intern_trait_ref(&mut self, trait_def: DefId, args: ArgsId) -> TraitRefId {
        let key = ConsTable::key3(SALT_TR, trait_def.0 as u64, args.0 as u64, 0);
        if let Some(id) = self
            .tr_cons
            .lookup(key, |v| self.trait_refs[v as usize] == (trait_def, args))
        {
            return TraitRefId(id);
        }
        let id = TraitRefId(self.trait_refs.len() as u32);
        self.trait_refs.push((trait_def, args));
        self.tr_cons.insert(key, id.0);
        id
    }

    pub fn intern_proj_key(&mut self, tr: TraitRefId, name: Symbol) -> ProjKeyId {
        let key = ConsTable::key3(SALT_PK, tr.0 as u64, name.0 as u64, 0);
        if let Some(id) = self
            .pk_cons
            .lookup(key, |v| self.proj_keys[v as usize] == (tr, name))
        {
            return ProjKeyId(id);
        }
        let id = ProjKeyId(self.proj_keys.len() as u32);
        self.proj_keys.push((tr, name));
        self.pk_cons.insert(key, id.0);
        id
    }

    pub fn intern_fn_ty(
        &mut self,
        params: &[(Conv, TyId)],
        result: TyId,
        raises: TyId,
        closure: bool,
    ) -> FnTyId {
        let tail = [result.0 as u64, raises.0 as u64, closure as u64];
        let key = ConsTable::key_iter(
            SALT_FN,
            params.len() * 2 + 3,
            params
                .iter()
                .flat_map(|&(c, t)| [c as u64, t.0 as u64])
                .chain(tail),
        );
        let same = |v: u32| {
            let id = FnTyId(v);
            let (cs, ts) = self.fn_tys.params(id);
            cs.len() == params.len()
                && params
                    .iter()
                    .enumerate()
                    .all(|(i, &(c, t))| cs[i] == c && ts[i] == t)
                && self.fn_tys.result(id) == result
                && self.fn_tys.raises(id) == raises
                && self.fn_tys.is_closure(id) == closure
        };
        if let Some(id) = self.fn_cons.lookup(key, same) {
            return FnTyId(id);
        }
        let id = FnTyId(self.fn_tys.result.len() as u32);
        self.fn_tys.p_start.push(self.fn_tys.ty.len() as u32);
        self.fn_tys
            .p_len
            .push(u8::try_from(params.len()).expect("more than 255 parameters"));
        for &(c, t) in params {
            self.fn_tys.conv.push(c);
            self.fn_tys.ty.push(t);
        }
        self.fn_tys.result.push(result);
        self.fn_tys.raises.push(raises);
        self.fn_tys.closure.push(closure);
        self.fn_cons.insert(key, id.0);
        id
    }

    pub fn intern_brand(&mut self, row: BrandRow) -> BrandId {
        let (k, owner, ordinal) = match row {
            BrandRow::Param { owner, ordinal } => (0u64, owner.0, ordinal),
            BrandRow::Fresh { owner, ordinal } => (1u64, owner.0, ordinal),
        };
        let key = ConsTable::key3(SALT_BRAND, k, owner as u64, ordinal as u64);
        if let Some(id) = self
            .brand_cons
            .lookup(key, |v| self.brands[v as usize] == row)
        {
            return BrandId(id);
        }
        let id = BrandId(self.brands.len() as u32);
        self.brands.push(row);
        self.brand_cons.insert(key, id.0);
        id
    }

    pub fn intern_const(&mut self, v: ConstValue) -> ConstId {
        let (k, payload) = match v {
            ConstValue::I(n) => (0u64, n as u128),
            ConstValue::B(b) => (1u64, b as u128),
            ConstValue::S(s) => (2u64, s.0 as u128),
        };
        let key = ConsTable::key3(SALT_CONST, k, payload as u64, (payload >> 64) as u64);
        if let Some(id) = self
            .const_cons
            .lookup(key, |x| self.consts[x as usize] == v)
        {
            return ConstId(id);
        }
        let id = ConstId(self.consts.len() as u32);
        self.consts.push(v);
        self.const_cons.insert(key, id.0);
        id
    }

    // -------------------------------------------------------------- interning

    /// The one way a type row comes into existence. Hashes
    /// `(tag, a, b, quals)`, probes linearly, and in the same step ORs the
    /// children's `flags` and fills `unqual`.
    pub fn intern(&mut self, tag: TyTag, a: u32, b: u32, quals: Quals) -> TyId {
        let key = ConsTable::key3(
            SALT_ROW,
            ((tag as u64) << 8) | quals.0 as u64,
            a as u64,
            b as u64,
        );
        let same = |v: u32| {
            let i = v as usize;
            self.tag[i] == tag && self.a[i] == a && self.b[i] == b && self.quals[i] == quals.0
        };
        if let Some(id) = self.rows_cons.lookup(key, same) {
            return TyId(id);
        }

        // Store invariants (design §5.1's `cfg(paranoid)` list). MARC: these
        // are `debug_assert!`s rather than a `paranoid` cargo feature — a
        // feature nobody enables is a check nobody runs, and `debug_assert!`
        // is on for every `cargo test` in CI and off in the release build the
        // benchmarks measure, which is the same coverage for no configuration.
        debug_assert!(
            tag != TyTag::Proj || self.is_rigid(TyId(a)),
            "a projection's head must be a parameter or another projection (R20)"
        );
        debug_assert!(quals.is_consistent(), "iso and imm are mutually exclusive");

        let child_flags = self.child_flags(tag, a, b);
        let unqual = if quals.is_none() {
            None
        } else {
            Some(self.intern(tag, a, b, Quals::NONE))
        };

        let id = TyId(self.tag.len() as u32);
        self.tag.push(tag);
        self.a.push(a);
        self.b.push(b);
        self.quals.push(quals.0);
        self.flags.push(child_flags);
        self.unqual.push(unqual.unwrap_or(id));
        self.copyable.push(0);
        self.rows_cons.insert(key, id.0);
        id
    }

    fn child_flags(&self, tag: TyTag, a: u32, b: u32) -> u8 {
        let or_args = |id: u32| {
            let mut f = 0u8;
            for &x in self.args(ArgsId(id)) {
                f |= self.flags[x.index()];
            }
            f
        };
        match tag {
            TyTag::Error => F_ERROR,
            TyTag::Unit | TyTag::Never | TyTag::Prim => 0,
            TyTag::Nominal | TyTag::Tuple => or_args(b),
            TyTag::Fn => {
                let id = FnTyId(a);
                let (_, ts) = self.fn_tys.params(id);
                let mut f = ts.iter().fold(0u8, |acc, t| acc | self.flags[t.index()]);
                f |= self.flags[self.fn_tys.result(id).index()];
                let raises = self.fn_tys.raises(id);
                if raises != NO_TY {
                    f |= self.flags[raises.index()];
                }
                f
            }
            TyTag::Dyn => or_args(self.trait_refs[a as usize].1.0),
            TyTag::Param => F_PARAM,
            TyTag::Proj => {
                let mut f = F_PROJ | self.flags[a as usize];
                let (tr, _) = self.proj_keys[b as usize];
                f |= or_args(self.trait_refs[tr.index()].1.0);
                f
            }
            TyTag::Brand => {
                let mut f = F_BRAND;
                if self.brands[b as usize].kind() == BrandKind::Fresh {
                    f |= F_FRESH;
                }
                f
            }
            TyTag::ConstVal => self.flags[b as usize],
        }
    }

    // ----------------------------------------------------------- convenience

    pub fn prim(&mut self, k: PrimKind) -> TyId {
        self.intern(TyTag::Prim, k as u32, 0, Quals::NONE)
    }

    pub fn nominal(&mut self, def: DefId, args: ArgsId) -> TyId {
        self.intern(TyTag::Nominal, def.0, args.0, Quals::NONE)
    }

    pub fn nominal_of(&mut self, def: DefId, args: &[TyId]) -> TyId {
        let a = self.intern_args(args);
        self.nominal(def, a)
    }

    pub fn tuple(&mut self, args: ArgsId) -> TyId {
        debug_assert!(
            !self.args(args).is_empty(),
            "a tuple has at least one element; `()` is TY_UNIT"
        );
        self.intern(TyTag::Tuple, 0, args.0, Quals::NONE)
    }

    pub fn tuple_of(&mut self, args: &[TyId]) -> TyId {
        let a = self.intern_args(args);
        self.tuple(a)
    }

    pub fn fn_ty(&mut self, id: FnTyId) -> TyId {
        self.intern(TyTag::Fn, id.0, 0, Quals::NONE)
    }

    pub fn dyn_ty(&mut self, tr: TraitRefId) -> TyId {
        self.intern(TyTag::Dyn, tr.0, 0, Quals::NONE)
    }

    pub fn param(&mut self, owner: DefId, ordinal: u16) -> TyId {
        self.intern(TyTag::Param, owner.0, ordinal as u32, Quals::NONE)
    }

    pub fn proj(&mut self, head: TyId, key: ProjKeyId) -> TyId {
        self.intern(TyTag::Proj, head.0, key.0, Quals::NONE)
    }

    pub fn proj_of(
        &mut self,
        head: TyId,
        trait_def: DefId,
        trait_args: &[TyId],
        name: Symbol,
    ) -> TyId {
        let a = self.intern_args(trait_args);
        let tr = self.intern_trait_ref(trait_def, a);
        let pk = self.intern_proj_key(tr, name);
        self.proj(head, pk)
    }

    pub fn brand_ty(&mut self, row: BrandRow) -> TyId {
        let kind = row.kind();
        let id = self.intern_brand(row);
        self.intern(TyTag::Brand, kind as u32, id.0, Quals::NONE)
    }

    pub fn const_ty(&mut self, v: ConstValue, ty: TyId) -> TyId {
        let id = self.intern_const(v);
        self.intern(TyTag::ConstVal, id.0, ty.0, Quals::NONE)
    }

    /// The same type carrying `quals` (union'd with whatever it already has).
    /// `Quals::NONE` returns the unqualified row.
    pub fn qualified(&mut self, t: TyId, quals: Quals) -> TyId {
        let i = t.index();
        let merged = Quals(self.quals[i]).union(quals);
        if merged.0 == self.quals[i] {
            return t;
        }
        let (tag, a, b) = (self.tag[i], self.a[i], self.b[i]);
        self.intern(tag, a, b, merged)
    }
}

#[cfg(test)]
mod tests {
    /// The three reserved rows exist in EVERY build profile. This is the
    /// regression test for the release-only bug the comment in
    /// `TyStore::new` describes: it reads `len()` and the ids, neither of
    /// which a `debug_assert` can fabricate.
    #[test]
    fn the_three_reserved_rows_are_0_1_2_in_every_profile() {
        let s = TyStore::new();
        assert_eq!(
            s.len(),
            3,
            "a fresh store holds exactly TY_ERROR, TY_UNIT and TY_NEVER"
        );
        assert_eq!(s.tag(TY_ERROR), TyTag::Error);
        assert_eq!(s.tag(TY_UNIT), TyTag::Unit);
        assert_eq!(s.tag(TY_NEVER), TyTag::Never);
        assert!(s.args(NO_ARGS).is_empty());
    }

    use super::*;

    #[test]
    fn constants_are_the_first_three_rows() {
        let s = TyStore::new();
        assert_eq!(s.tag(TY_ERROR), TyTag::Error);
        assert_eq!(s.tag(TY_UNIT), TyTag::Unit);
        assert_eq!(s.tag(TY_NEVER), TyTag::Never);
        assert!(s.is_error(TY_ERROR));
        assert!(s.is_monomorphic(TY_UNIT));
    }

    #[test]
    fn equal_types_are_equal_ids() {
        let mut s = TyStore::new();
        let i32_ty = s.prim(PrimKind::I32);
        let a = s.nominal_of(DefId(7), &[i32_ty]);
        let b = s.nominal_of(DefId(7), &[i32_ty]);
        let c = s.nominal_of(DefId(7), &[]);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn quals_are_part_of_identity_and_unqual_is_one_load() {
        let mut s = TyStore::new();
        let buf = s.nominal_of(DefId(1), &[]);
        let iso_buf = s.qualified(buf, Quals::ISO);
        let iso_secret = s.qualified(iso_buf, Quals::SECRET);
        assert_ne!(buf, iso_buf);
        assert_ne!(iso_buf, iso_secret);
        assert_eq!(s.unqual(iso_secret), buf);
        assert_eq!(s.unqual(buf), buf);
        assert!(s.quals(iso_secret).is_iso() && s.quals(iso_secret).is_secret());
    }

    #[test]
    fn flags_are_the_or_of_children() {
        let mut s = TyStore::new();
        let i32_ty = s.prim(PrimKind::I32);
        let p = s.param(DefId(5), 0);
        let mono = s.nominal_of(DefId(1), &[i32_ty]);
        let open = s.nominal_of(DefId(1), &[p]);
        let nested = s.tuple_of(&[mono, open]);
        assert!(s.is_monomorphic(mono));
        assert!(!s.is_monomorphic(open));
        assert!(!s.is_monomorphic(nested));
        assert_eq!(s.flags(open) & F_PARAM, F_PARAM);
        // An error anywhere inside propagates, so recovery never re-reports.
        let bad = s.tuple_of(&[TY_ERROR, i32_ty]);
        assert!(s.is_error(bad));
    }

    #[test]
    fn projection_flags_include_the_trait_arguments() {
        let mut s = TyStore::new();
        let p = s.param(DefId(5), 0);
        let q = s.param(DefId(5), 1);
        let name = Symbol(0);
        let pr = s.proj_of(p, DefId(9), &[q], name);
        assert_eq!(s.flags(pr) & (F_PROJ | F_PARAM), F_PROJ | F_PARAM);
        assert_eq!(s.head_key(pr), HeadKey::Proj);
    }

    #[test]
    fn fresh_brands_are_flagged() {
        let mut s = TyStore::new();
        let fresh = s.brand_ty(BrandRow::Fresh {
            owner: DeclKeyId(4),
            ordinal: 0,
        });
        let parm = s.brand_ty(BrandRow::Param {
            owner: DefId(4),
            ordinal: 0,
        });
        assert_eq!(s.flags(fresh) & F_FRESH, F_FRESH);
        assert_eq!(s.flags(parm) & F_FRESH, 0);
        assert_eq!(s.flags(parm) & F_BRAND, F_BRAND);
    }
}
