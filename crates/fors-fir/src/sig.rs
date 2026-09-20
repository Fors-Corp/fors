//! Signatures (design §5.2): struct-of-arrays indexed by `DefId`, with four
//! interned pools hanging off it (bound lists, members, associated items,
//! constraint entries). Nothing here allocates per node.
//!
//! `Self` never appears in a stored signature. Inside an `impl` it is replaced
//! by the self type at lowering (R8); inside a `trait` it is
//! `Param{trait, 0}`, whose single bound is the trait itself with its own
//! parameters, so a trait's own gparam list is `[Self, P1, ..]`.

use fors_index::ids::DefId;
use fors_index::interner::Symbol;

use crate::cons::ConsTable;
use crate::ty::{ArgsId, ConstId, NO_CONST, NO_TY, TraitRefId, TyId};

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

index_newtype!(GenericsId);
index_newtype!(FnSigId);
index_newtype!(MemberListId);
index_newtype!(AssocListId);
index_newtype!(TraitRefListId);
index_newtype!(ConstraintListId);

/// The empty list of each kind, interned first so it is a constant.
pub const NO_GENERICS: GenericsId = GenericsId(0);
pub const NO_BOUNDS: TraitRefListId = TraitRefListId(0);
pub const NO_MEMBERS: MemberListId = MemberListId(0);
pub const NO_ASSOC: AssocListId = AssocListId(0);
pub const NO_CONSTRAINTS: ConstraintListId = ConstraintListId(0);
pub const NO_FN_SIG: FnSigId = FnSigId(u32::MAX);

/// `receiver`/`scoped` sentinel: an associated function has no receiver; a
/// signature with no `scoped(p)` prefix designates no parameter.
pub const NO_SLOT: u8 = 0xFF;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SigKind {
    Fn,
    ExternFn,
    Struct,
    Enum,
    Trait,
    Impl,
    Const,
    /// Lowering failed and reported; every use of this declaration recovers
    /// silently (design §7.10).
    Poisoned,
    /// Named but never declared anywhere in the build.
    Absent,
}

impl SigKind {
    pub fn from_u8(v: u8) -> Option<SigKind> {
        const ALL: [SigKind; 9] = [
            SigKind::Fn,
            SigKind::ExternFn,
            SigKind::Struct,
            SigKind::Enum,
            SigKind::Trait,
            SigKind::Impl,
            SigKind::Const,
            SigKind::Poisoned,
            SigKind::Absent,
        ];
        ALL.get(v as usize).copied()
    }
}

/// ch01's parameter conventions. R7's function-type equality is pairwise on
/// these, so they are part of a type's identity, not a side table.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Conv {
    Let,
    Inout,
    Sink,
    Set,
}

impl Conv {
    pub fn from_u8(v: u8) -> Option<Conv> {
        const ALL: [Conv; 4] = [Conv::Let, Conv::Inout, Conv::Sink, Conv::Set];
        ALL.get(v as usize).copied()
    }
}

/// R15's classification of a generic parameter, decided once at lowering:
/// exactly one trait bound list (a type parameter), exactly one non-trait type
/// (a const parameter, R13), a brand, or exactly one `fn_type` (a callable
/// parameter, R41).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GParamKind {
    Type,
    Const { ty: TyId },
    Brand,
    Callable { fn_ty: TyId },
}

impl GParamKind {
    /// The byte that identifies the shape in the canonical encoding.
    pub fn tag(self) -> u8 {
        match self {
            GParamKind::Type => 0,
            GParamKind::Const { .. } => 1,
            GParamKind::Brand => 2,
            GParamKind::Callable { .. } => 3,
        }
    }
}

const SALT_BOUNDS: u64 = 0x424f_554e_4453_0000;

/// Interned lists of trait references: a gparam's bounds, an associated type's
/// bounds, a constraint entry's bounds.
///
/// MARC: the stored list is sorted by `TraitRefId`, which is deterministic
/// within a build but is NOT the canonical order — `TraitRefId`s are assigned
/// in first-intern order, so the same set of bounds can sort differently in two
/// builds. Canonicalisation is the encoder's job (it sorts by each bound's
/// self-contained encoded bytes, §5.4), and sorting here as well is purely so
/// that `T: Eq + Ord` and `T: Ord + Eq` share one `TraitRefListId` inside a
/// build and R17's "same bounds" is an id comparison.
#[derive(Default)]
pub struct TraitRefLists {
    items: Vec<TraitRefId>,
    start: Vec<u32>,
    len: Vec<u16>,
    cons: ConsTable,
}

impl TraitRefLists {
    pub fn new() -> TraitRefLists {
        let mut t = TraitRefLists::default();
        let empty = t.intern(&[]);
        debug_assert_eq!(empty, NO_BOUNDS);
        t
    }

    /// Interns `bounds` after sorting and de-duplicating them.
    pub fn intern(&mut self, bounds: &[TraitRefId]) -> TraitRefListId {
        let mut sorted: Vec<TraitRefId> = bounds.to_vec();
        sorted.sort();
        sorted.dedup();
        let raw: Vec<u32> = sorted.iter().map(|t| t.0).collect();
        let key = ConsTable::key_slice(SALT_BOUNDS, &raw);
        if let Some(id) = self
            .cons
            .lookup(key, |v| self.get(TraitRefListId(v)) == sorted.as_slice())
        {
            return TraitRefListId(id);
        }
        let id = TraitRefListId(self.start.len() as u32);
        self.start.push(self.items.len() as u32);
        self.len
            .push(u16::try_from(sorted.len()).expect("more than u16::MAX bounds"));
        self.items.extend_from_slice(&sorted);
        self.cons.insert(key, id.0);
        id
    }

    pub fn get(&self, id: TraitRefListId) -> &[TraitRefId] {
        let s = self.start[id.index()] as usize;
        let l = self.len[id.index()] as usize;
        &self.items[s..s + l]
    }

    pub fn len(&self) -> usize {
        self.start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.start.is_empty()
    }
}

/// One generic parameter as callers build and read it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct GParam {
    pub name: Symbol,
    pub kind: GParamKind,
    pub bounds: TraitRefListId,
}

/// A declaration's own generic parameters plus its constraint entries (R62).
#[derive(Default)]
pub struct GenericsStore {
    start: Vec<u32>,
    len: Vec<u16>,
    constraints: Vec<ConstraintListId>,
    gp_name: Vec<Symbol>,
    gp_kind: Vec<GParamKind>,
    gp_bounds: Vec<TraitRefListId>,
}

impl GenericsStore {
    pub fn new() -> GenericsStore {
        let mut g = GenericsStore::default();
        let empty = g.push(&[], NO_CONSTRAINTS);
        debug_assert_eq!(empty, NO_GENERICS);
        g
    }

    /// Appends a generics row. Not interned: a declaration has exactly one, and
    /// two declarations that happen to share a shape are still two rows (their
    /// parameters are owned by different `DefId`s, so the rows are not
    /// interchangeable).
    pub fn push(&mut self, params: &[GParam], constraints: ConstraintListId) -> GenericsId {
        let id = GenericsId(self.start.len() as u32);
        self.start.push(self.gp_name.len() as u32);
        self.len
            .push(u16::try_from(params.len()).expect("more than u16::MAX generic parameters"));
        self.constraints.push(constraints);
        for p in params {
            self.gp_name.push(p.name);
            self.gp_kind.push(p.kind);
            self.gp_bounds.push(p.bounds);
        }
        id
    }

    pub fn count(&self, id: GenericsId) -> usize {
        self.len[id.index()] as usize
    }

    pub fn param(&self, id: GenericsId, ordinal: usize) -> GParam {
        let i = self.start[id.index()] as usize + ordinal;
        debug_assert!(ordinal < self.count(id));
        GParam {
            name: self.gp_name[i],
            kind: self.gp_kind[i],
            bounds: self.gp_bounds[i],
        }
    }

    pub fn constraints(&self, id: GenericsId) -> ConstraintListId {
        self.constraints[id.index()]
    }

    pub fn len(&self) -> usize {
        self.start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.start.is_empty()
    }
}

/// R62's constraint entries: `where T.Item: Display`-shaped bounds on a type
/// that is not itself a parameter of the declaration.
#[derive(Default)]
pub struct ConstraintStore {
    start: Vec<u32>,
    len: Vec<u16>,
    subject: Vec<TyId>,
    bounds: Vec<TraitRefListId>,
}

impl ConstraintStore {
    pub fn new() -> ConstraintStore {
        let mut c = ConstraintStore::default();
        let empty = c.push(&[]);
        debug_assert_eq!(empty, NO_CONSTRAINTS);
        c
    }

    pub fn push(&mut self, entries: &[(TyId, TraitRefListId)]) -> ConstraintListId {
        let id = ConstraintListId(self.start.len() as u32);
        self.start.push(self.subject.len() as u32);
        self.len
            .push(u16::try_from(entries.len()).expect("more than u16::MAX constraint entries"));
        for &(s, b) in entries {
            self.subject.push(s);
            self.bounds.push(b);
        }
        id
    }

    pub fn count(&self, id: ConstraintListId) -> usize {
        self.len[id.index()] as usize
    }

    pub fn entry(&self, id: ConstraintListId, i: usize) -> (TyId, TraitRefListId) {
        let at = self.start[id.index()] as usize + i;
        (self.subject[at], self.bounds[at])
    }

    pub fn len(&self) -> usize {
        self.start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.start.is_empty()
    }
}

/// One value parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Param {
    /// Names are in the hash: R37 makes a named argument's label observable.
    pub name: Symbol,
    pub conv: Conv,
    pub ty: TyId,
}

#[derive(Default)]
pub struct FnSigStore {
    p_start: Vec<u32>,
    p_len: Vec<u8>,
    result: Vec<TyId>,
    raises: Vec<TyId>,
    scoped: Vec<u8>,
    receiver: Vec<u8>,
    /// MARC: design §5.2 stores contracts as a CST node range, and §5.4 puts
    /// "their token hash" in the canonical encoding. Both are kept: the range
    /// is what `fors-check` re-visits to check a clause in the declaration's
    /// own context (R30), and the hash is what enters the signature encoding —
    /// a node range is a build-local index and could not be hashed canonically,
    /// while a token hash cannot be re-checked. Neither substitutes for the
    /// other, so the row carries both.
    contract_nodes: Vec<(u32, u32)>,
    contract_hash: Vec<u128>,
    p_name: Vec<Symbol>,
    p_conv: Vec<Conv>,
    p_ty: Vec<TyId>,
}

impl FnSigStore {
    pub fn new() -> FnSigStore {
        FnSigStore::default()
    }

    #[allow(clippy::too_many_arguments)]
    pub fn push(
        &mut self,
        params: &[Param],
        result: TyId,
        raises: TyId,
        scoped: u8,
        receiver: u8,
        contract_nodes: (u32, u32),
        contract_hash: u128,
    ) -> FnSigId {
        let id = FnSigId(self.result.len() as u32);
        self.p_start.push(self.p_name.len() as u32);
        self.p_len
            .push(u8::try_from(params.len()).expect("more than 255 parameters"));
        self.result.push(result);
        self.raises.push(raises);
        self.scoped.push(scoped);
        self.receiver.push(receiver);
        self.contract_nodes.push(contract_nodes);
        self.contract_hash.push(contract_hash);
        for p in params {
            self.p_name.push(p.name);
            self.p_conv.push(p.conv);
            self.p_ty.push(p.ty);
        }
        id
    }

    pub fn count(&self, id: FnSigId) -> usize {
        self.p_len[id.index()] as usize
    }

    pub fn param(&self, id: FnSigId, i: usize) -> Param {
        let at = self.p_start[id.index()] as usize + i;
        Param {
            name: self.p_name[at],
            conv: self.p_conv[at],
            ty: self.p_ty[at],
        }
    }

    pub fn result(&self, id: FnSigId) -> TyId {
        self.result[id.index()]
    }

    /// [`NO_TY`] for a non-raising signature.
    pub fn raises(&self, id: FnSigId) -> TyId {
        self.raises[id.index()]
    }

    /// [`NO_SLOT`], or the designated parameter index (ch01 R19).
    pub fn scoped(&self, id: FnSigId) -> u8 {
        self.scoped[id.index()]
    }

    /// [`NO_SLOT`] for an associated function; else 0, and the receiver's
    /// convention is `params[0].conv`.
    pub fn receiver(&self, id: FnSigId) -> u8 {
        self.receiver[id.index()]
    }

    pub fn contract_nodes(&self, id: FnSigId) -> (u32, u32) {
        self.contract_nodes[id.index()]
    }

    pub fn contract_hash(&self, id: FnSigId) -> u128 {
        self.contract_hash[id.index()]
    }

    pub fn len(&self) -> usize {
        self.result.len()
    }

    pub fn is_empty(&self) -> bool {
        self.result.is_empty()
    }
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MemberKind {
    Field,
    Variant,
    /// A trait item, an impl item, an inherent method or an associated
    /// function: `def` names it, and its own signature row has the rest.
    Item,
}

impl MemberKind {
    pub fn from_u8(v: u8) -> Option<MemberKind> {
        const ALL: [MemberKind; 3] = [MemberKind::Field, MemberKind::Variant, MemberKind::Item];
        ALL.get(v as usize).copied()
    }
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PayloadKind {
    /// A unit variant.
    None,
    /// `V(T, U)` — the types are in `args`.
    Tuple,
    /// `V { a: T }` — the fields are a nested member list in `sub`.
    Record,
}

impl PayloadKind {
    pub fn from_u8(v: u8) -> Option<PayloadKind> {
        const ALL: [PayloadKind; 3] = [PayloadKind::None, PayloadKind::Tuple, PayloadKind::Record];
        ALL.get(v as usize).copied()
    }
}

pub const VIS_PRIVATE: u8 = 0;
pub const VIS_PUBLIC: u8 = 1;

/// One member as callers build and read it. Which columns matter depends on
/// `kind`: a field uses `name`/`vis`/`ty`; a variant uses `name`/`payload` plus
/// `args` (tuple) or `sub` (record); an item uses `name`/`vis`/`def`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Member {
    pub kind: MemberKind,
    pub name: Symbol,
    pub vis: u8,
    pub ty: TyId,
    pub payload: PayloadKind,
    pub args: ArgsId,
    pub sub: MemberListId,
    pub def: DefId,
}

impl Member {
    pub fn field(name: Symbol, vis: u8, ty: TyId) -> Member {
        Member {
            kind: MemberKind::Field,
            name,
            vis,
            ty,
            payload: PayloadKind::None,
            args: crate::ty::NO_ARGS,
            sub: NO_MEMBERS,
            def: crate::defpath::NO_DEF,
        }
    }

    pub fn item(name: Symbol, vis: u8, def: DefId) -> Member {
        Member {
            kind: MemberKind::Item,
            name,
            vis,
            ty: NO_TY,
            payload: PayloadKind::None,
            args: crate::ty::NO_ARGS,
            sub: NO_MEMBERS,
            def,
        }
    }

    pub fn unit_variant(name: Symbol) -> Member {
        Member {
            kind: MemberKind::Variant,
            name,
            vis: VIS_PUBLIC,
            ty: NO_TY,
            payload: PayloadKind::None,
            args: crate::ty::NO_ARGS,
            sub: NO_MEMBERS,
            def: crate::defpath::NO_DEF,
        }
    }

    pub fn tuple_variant(name: Symbol, args: ArgsId) -> Member {
        Member {
            payload: PayloadKind::Tuple,
            args,
            ..Member::unit_variant(name)
        }
    }

    pub fn record_variant(name: Symbol, sub: MemberListId) -> Member {
        Member {
            payload: PayloadKind::Record,
            sub,
            ..Member::unit_variant(name)
        }
    }
}

/// A flat pool of members. Order is significant and never sorted: a struct's
/// field order is ch05's layout and an enum's variant order is its
/// discriminants. (The per-head sorted `(HeadKey, Symbol) -> MemberRef` index
/// that answers R43 tier 1 and R48 clashes is built over this pool by
/// `fors-check` in I2, precisely because it must not disturb this order.)
#[derive(Default)]
pub struct MemberStore {
    start: Vec<u32>,
    len: Vec<u32>,
    m_kind: Vec<MemberKind>,
    m_name: Vec<Symbol>,
    m_vis: Vec<u8>,
    m_ty: Vec<TyId>,
    m_payload: Vec<PayloadKind>,
    m_args: Vec<ArgsId>,
    m_sub: Vec<MemberListId>,
    m_def: Vec<DefId>,
}

impl MemberStore {
    pub fn new() -> MemberStore {
        let mut m = MemberStore::default();
        let empty = m.push(&[]);
        debug_assert_eq!(empty, NO_MEMBERS);
        m
    }

    pub fn push(&mut self, members: &[Member]) -> MemberListId {
        let id = MemberListId(self.start.len() as u32);
        self.start.push(self.m_kind.len() as u32);
        self.len.push(members.len() as u32);
        for m in members {
            self.m_kind.push(m.kind);
            self.m_name.push(m.name);
            self.m_vis.push(m.vis);
            self.m_ty.push(m.ty);
            self.m_payload.push(m.payload);
            self.m_args.push(m.args);
            self.m_sub.push(m.sub);
            self.m_def.push(m.def);
        }
        id
    }

    pub fn count(&self, id: MemberListId) -> usize {
        self.len[id.index()] as usize
    }

    pub fn get(&self, id: MemberListId, i: usize) -> Member {
        let at = self.start[id.index()] as usize + i;
        Member {
            kind: self.m_kind[at],
            name: self.m_name[at],
            vis: self.m_vis[at],
            ty: self.m_ty[at],
            payload: self.m_payload[at],
            args: self.m_args[at],
            sub: self.m_sub[at],
            def: self.m_def[at],
        }
    }

    pub fn len(&self) -> usize {
        self.start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.start.is_empty()
    }
}

/// A trait's associated-type declarations (`bounds` set, `rhs` = [`NO_TY`]) or
/// an impl's definitions (`rhs` set, `bounds` = [`NO_BOUNDS`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Assoc {
    pub name: Symbol,
    pub bounds: TraitRefListId,
    pub rhs: TyId,
}

#[derive(Default)]
pub struct AssocStore {
    start: Vec<u32>,
    len: Vec<u16>,
    a_name: Vec<Symbol>,
    a_bounds: Vec<TraitRefListId>,
    a_rhs: Vec<TyId>,
}

impl AssocStore {
    pub fn new() -> AssocStore {
        let mut a = AssocStore::default();
        let empty = a.push(&[]);
        debug_assert_eq!(empty, NO_ASSOC);
        a
    }

    pub fn push(&mut self, entries: &[Assoc]) -> AssocListId {
        let id = AssocListId(self.start.len() as u32);
        self.start.push(self.a_name.len() as u32);
        self.len
            .push(u16::try_from(entries.len()).expect("more than u16::MAX associated types"));
        for e in entries {
            self.a_name.push(e.name);
            self.a_bounds.push(e.bounds);
            self.a_rhs.push(e.rhs);
        }
        id
    }

    pub fn count(&self, id: AssocListId) -> usize {
        self.len[id.index()] as usize
    }

    pub fn get(&self, id: AssocListId, i: usize) -> Assoc {
        let at = self.start[id.index()] as usize + i;
        Assoc {
            name: self.a_name[at],
            bounds: self.a_bounds[at],
            rhs: self.a_rhs[at],
        }
    }

    /// The right-hand side an impl gives `name`, or [`NO_TY`].
    pub fn rhs_of(&self, id: AssocListId, name: Symbol) -> TyId {
        for i in 0..self.count(id) {
            let e = self.get(id, i);
            if e.name == name {
                return e.rhs;
            }
        }
        NO_TY
    }

    pub fn len(&self) -> usize {
        self.start.len()
    }

    pub fn is_empty(&self) -> bool {
        self.start.is_empty()
    }
}

/// `soa`-marked struct (ch03's struct-of-arrays layout modifier).
pub const SIG_SOA: u8 = 1;

/// SoA indexed by `DefId`, with the four pools it indexes into.
pub struct SigStore {
    kind: Vec<SigKind>,
    flags: Vec<u8>,
    generics: Vec<GenericsId>,
    fn_sig: Vec<FnSigId>,
    members: Vec<MemberListId>,
    self_ty: Vec<TyId>,
    trait_ref: Vec<TraitRefId>,
    assoc: Vec<AssocListId>,
    const_ty: Vec<TyId>,
    const_val: Vec<ConstId>,
    /// The canonical FIR hash (§5.4): the early-cutoff key every dependent
    /// compares. Derived, so it is filled after lowering, never read as input.
    sig_hash: Vec<u128>,

    pub generics_store: GenericsStore,
    pub fn_sigs: FnSigStore,
    pub member_store: MemberStore,
    pub assocs: AssocStore,
    pub constraints: ConstraintStore,
    pub bounds: TraitRefLists,
}

/// `NO_TRAIT_REF` marks "not an impl" in the `trait_ref` column.
pub const NO_TRAIT_REF: TraitRefId = TraitRefId(u32::MAX);

impl Default for SigStore {
    fn default() -> Self {
        Self::new()
    }
}

impl SigStore {
    pub fn new() -> SigStore {
        SigStore {
            kind: Vec::new(),
            flags: Vec::new(),
            generics: Vec::new(),
            fn_sig: Vec::new(),
            members: Vec::new(),
            self_ty: Vec::new(),
            trait_ref: Vec::new(),
            assoc: Vec::new(),
            const_ty: Vec::new(),
            const_val: Vec::new(),
            sig_hash: Vec::new(),
            generics_store: GenericsStore::new(),
            fn_sigs: FnSigStore::new(),
            member_store: MemberStore::new(),
            assocs: AssocStore::new(),
            constraints: ConstraintStore::new(),
            bounds: TraitRefLists::new(),
        }
    }

    /// Appends an empty row of `kind` and returns its `DefId`. Callers fill the
    /// columns that `kind` uses; the rest keep their "absent" sentinels.
    pub fn push(&mut self, kind: SigKind) -> DefId {
        let def = DefId(self.kind.len() as u32);
        self.kind.push(kind);
        self.flags.push(0);
        self.generics.push(NO_GENERICS);
        self.fn_sig.push(NO_FN_SIG);
        self.members.push(NO_MEMBERS);
        self.self_ty.push(NO_TY);
        self.trait_ref.push(NO_TRAIT_REF);
        self.assoc.push(NO_ASSOC);
        self.const_ty.push(NO_TY);
        self.const_val.push(NO_CONST);
        self.sig_hash.push(0);
        def
    }

    pub fn len(&self) -> usize {
        self.kind.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kind.is_empty()
    }

    pub fn kind(&self, def: DefId) -> SigKind {
        self.kind[def.index()]
    }

    pub fn set_kind(&mut self, def: DefId, kind: SigKind) {
        self.kind[def.index()] = kind;
    }

    pub fn flags(&self, def: DefId) -> u8 {
        self.flags[def.index()]
    }

    pub fn is_soa(&self, def: DefId) -> bool {
        self.flags[def.index()] & SIG_SOA != 0
    }

    pub fn set_soa(&mut self, def: DefId, soa: bool) {
        if soa {
            self.flags[def.index()] |= SIG_SOA;
        } else {
            self.flags[def.index()] &= !SIG_SOA;
        }
    }

    pub fn generics(&self, def: DefId) -> GenericsId {
        self.generics[def.index()]
    }

    pub fn set_generics(&mut self, def: DefId, g: GenericsId) {
        self.generics[def.index()] = g;
    }

    pub fn fn_sig(&self, def: DefId) -> FnSigId {
        self.fn_sig[def.index()]
    }

    pub fn set_fn_sig(&mut self, def: DefId, f: FnSigId) {
        self.fn_sig[def.index()] = f;
    }

    pub fn members(&self, def: DefId) -> MemberListId {
        self.members[def.index()]
    }

    pub fn set_members(&mut self, def: DefId, m: MemberListId) {
        self.members[def.index()] = m;
    }

    pub fn self_ty(&self, def: DefId) -> TyId {
        self.self_ty[def.index()]
    }

    pub fn set_self_ty(&mut self, def: DefId, t: TyId) {
        self.self_ty[def.index()] = t;
    }

    pub fn trait_ref(&self, def: DefId) -> TraitRefId {
        self.trait_ref[def.index()]
    }

    pub fn set_trait_ref(&mut self, def: DefId, tr: TraitRefId) {
        self.trait_ref[def.index()] = tr;
    }

    pub fn assoc(&self, def: DefId) -> AssocListId {
        self.assoc[def.index()]
    }

    pub fn set_assoc(&mut self, def: DefId, a: AssocListId) {
        self.assoc[def.index()] = a;
    }

    pub fn const_ty(&self, def: DefId) -> TyId {
        self.const_ty[def.index()]
    }

    pub fn const_val(&self, def: DefId) -> ConstId {
        self.const_val[def.index()]
    }

    pub fn set_const(&mut self, def: DefId, ty: TyId, val: ConstId) {
        self.const_ty[def.index()] = ty;
        self.const_val[def.index()] = val;
    }

    pub fn sig_hash(&self, def: DefId) -> u128 {
        self.sig_hash[def.index()]
    }

    pub fn set_sig_hash(&mut self, def: DefId, h: u128) {
        self.sig_hash[def.index()] = h;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::TY_UNIT;

    #[test]
    fn bound_lists_are_order_and_duplicate_insensitive() {
        let mut t = TraitRefLists::new();
        let a = t.intern(&[TraitRefId(5), TraitRefId(2)]);
        let b = t.intern(&[TraitRefId(2), TraitRefId(5)]);
        let c = t.intern(&[TraitRefId(2), TraitRefId(5), TraitRefId(5)]);
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(t.get(a), &[TraitRefId(2), TraitRefId(5)]);
        assert!(t.get(NO_BOUNDS).is_empty());
    }

    #[test]
    fn rows_keep_their_absent_sentinels() {
        let mut s = SigStore::new();
        let def = s.push(SigKind::Struct);
        assert_eq!(s.kind(def), SigKind::Struct);
        assert_eq!(s.fn_sig(def), NO_FN_SIG);
        assert_eq!(s.self_ty(def), NO_TY);
        assert_eq!(s.trait_ref(def), NO_TRAIT_REF);
        assert_eq!(s.members(def), NO_MEMBERS);
        assert!(!s.is_soa(def));
        s.set_soa(def, true);
        assert!(s.is_soa(def));
    }

    #[test]
    fn fn_sig_params_read_back_in_order() {
        let mut s = SigStore::new();
        let ps = [
            Param {
                name: Symbol(1),
                conv: Conv::Let,
                ty: TY_UNIT,
            },
            Param {
                name: Symbol(2),
                conv: Conv::Inout,
                ty: TY_UNIT,
            },
        ];
        let id = s.fn_sigs.push(&ps, TY_UNIT, NO_TY, NO_SLOT, 0, (0, 0), 0);
        assert_eq!(s.fn_sigs.count(id), 2);
        assert_eq!(s.fn_sigs.param(id, 1).conv, Conv::Inout);
        assert_eq!(s.fn_sigs.raises(id), NO_TY);
        assert_eq!(s.fn_sigs.receiver(id), 0);
    }

    #[test]
    fn member_order_is_preserved() {
        let mut s = SigStore::new();
        let list = s.member_store.push(&[
            Member::field(Symbol(9), VIS_PUBLIC, TY_UNIT),
            Member::field(Symbol(3), VIS_PRIVATE, TY_UNIT),
        ]);
        assert_eq!(s.member_store.get(list, 0).name, Symbol(9));
        assert_eq!(s.member_store.get(list, 1).name, Symbol(3));
        assert_eq!(s.member_store.get(list, 1).vis, VIS_PRIVATE);
    }
}
