//! The canonical, build-index-free signature encoding, its hash, and the
//! reader that re-interns it (design §5.4).
//!
//! Nothing in these bytes is a row index. A nominal or trait head is its
//! `DeclKey` bytes; a generic parameter of the declaration being encoded (or of
//! its enclosing `impl`/`trait`) is a relative `(depth, ordinal)` marker and
//! any other owner is that owner's `DeclKey` bytes plus the ordinal; every list
//! is length-prefixed; every name that is observable is its bytes, never its
//! `Symbol`. That is what makes the hash comparable between two builds and
//! between a build and a `.fmod` file, and it is why token hashing is not
//! enough: edit module `a` so `use a.Shape;` in `b` names a different `Shape`
//! and `b`'s tokens are identical while its meaning is not (ch09 R2).
//!
//! **Layout.** `"FIR1"`, a policy byte, then `uleb(n)` type entries, then the
//! signature structure. Types are emitted post-order into their own section and
//! referred to afterwards by stream position, so a type shared by four
//! parameters is emitted once. Entries are self-delimiting, so reading exactly
//! `n` of them lands on the first structure byte.
//!
//! **Canonical order without position dependence.** A bound list is sorted by
//! each bound's *self-contained* encoding — a sub-encoding with its own local
//! type stream — and only then emitted into the shared stream. Sorting by bytes
//! taken from the shared stream would not be canonical: the positions in those
//! bytes depend on the order the bounds were visited in, which is the very thing
//! being normalised. Sorting on a position-independent key makes the emission
//! order identical for `T: Eq + Ord` and `T: Ord + Eq`, so the shared stream is
//! identical too.

use fors_index::decl::DeclKind;
use fors_index::fingerprint::hash_bytes;
use fors_index::ids::DefId;
use fors_index::interner::{Interner, Symbol};

use crate::Fir;
use crate::constval::ConstValue;
use crate::defpath::{DeclKey, DeclKeyId, DeclKeyTable, NO_DECL_KEY};
use crate::sig::{
    Assoc, Conv, GParam, GParamKind, Member, MemberKind, MemberListId, NO_BOUNDS, NO_FN_SIG,
    NO_SLOT, NO_TRAIT_REF, PayloadKind, SigKind, TraitRefListId,
};
use crate::ty::{
    ArgsId, BrandId, BrandRow, ConstId, FnTyId, NO_TY, PrimKind, ProjKeyId, Quals, TraitRefId,
    TyId, TyTag,
};

const MAGIC: &[u8; 4] = b"FIR1";

// Type-entry tags. Deliberately not `TyTag as u8`: these bytes are a wire
// format that outlives any in-memory enum, so they are written out once here and
// a new `TyTag` variant must choose its own byte explicitly.
const E_ERROR: u8 = 1;
const E_UNIT: u8 = 2;
const E_NEVER: u8 = 3;
const E_PRIM: u8 = 4;
const E_NOMINAL: u8 = 5;
const E_TUPLE: u8 = 6;
const E_FN: u8 = 7;
const E_DYN: u8 = 8;
const E_PARAM: u8 = 9;
const E_PROJ: u8 = 10;
const E_BRAND: u8 = 11;
const E_CONSTVAL: u8 = 12;

const FN_CLOSURE: u8 = 1;
const FN_RAISES: u8 = 2;

// MARC: this table mirrors `fors_index::decl::DeclKind`'s declaration order,
// because a `DeclKey`'s kind travels in these bytes as one number. A variant
// appended to `DeclKind` must be appended here too (the additive rule makes
// "appended" the only legal change, so the mapping stays stable);
// `decl_kind_bytes_round_trip` fails the build if the two ever disagree in
// length.
const DECL_KINDS: [DeclKind; 12] = [
    DeclKind::Fn,
    DeclKind::ExternFn,
    DeclKind::Struct,
    DeclKind::Enum,
    DeclKind::Trait,
    DeclKind::Impl,
    DeclKind::Const,
    DeclKind::Use,
    DeclKind::ModuleHeader,
    DeclKind::Needs,
    DeclKind::Inputs,
    DeclKind::Contracts,
];

fn decl_kind_from_u8(v: u8) -> Option<DeclKind> {
    DECL_KINDS.get(v as usize).copied()
}

/// The three questions design §14 Q4/Q5/Q6 reserve for Marc, as data.
/// [`decl_fingerprint`] is the one place their values are chosen.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FingerprintPolicy {
    /// Q4: does a `const` declaration's comptime value enter its hash?
    pub include_const_value: bool,
    /// Q5: are generic-parameter names left out (alpha-equivalence)?
    pub exclude_gparam_names: bool,
    /// Q6: are bound lists sorted before hashing (`T: Eq + Ord` == `T: Ord + Eq`)?
    pub sort_bound_lists: bool,
}

impl FingerprintPolicy {
    fn to_byte(self) -> u8 {
        (self.include_const_value as u8)
            | ((self.exclude_gparam_names as u8) << 1)
            | ((self.sort_bound_lists as u8) << 2)
    }

    fn from_byte(v: u8) -> FingerprintPolicy {
        FingerprintPolicy {
            include_const_value: v & 1 != 0,
            exclude_gparam_names: v & 2 != 0,
            sort_bound_lists: v & 4 != 0,
        }
    }
}

// MARC: this function is the invalidation policy of the whole incremental
// build, and each of the three questions below is one line you can flip. Get it
// wrong in one direction and the compiler over-invalidates: it rebuilds
// declarations whose meaning did not change, which costs rebuild time and
// nothing else. Get it wrong in the other direction and it under-invalidates:
// it keeps a result that is now wrong, which is a stale-build bug — the kind
// that survives a `cargo test`, reappears after a clean build, and cannot be
// reproduced from the source alone. One unit test per line pins the current
// answer (`const_value_enters_the_fingerprint`,
// `gparam_names_do_not_enter_the_fingerprint`,
// `bound_order_does_not_change_the_fingerprint`), so flipping a line tells you
// exactly which behaviour you changed.
//
// MARC (verification round): the three lines were flipped one at a time and
// the suite run each time. Q4 and Q5 each move exactly their own test. Q6
// moved its own test AND `encoding_is_independent_of_pool_warmth_and_
// interner_order`: with sorting off the encoder emits the STORE's order, and
// `TraitRefLists::intern` keeps bounds sorted by `TraitRefId` — an interning
// order — so the hash of an identical declaration differs between two builds.
// `sort_bound_lists: false` is therefore not "over-invalidation", it is a
// non-canonical hash. The knob stays (it is a wire-format byte), and flipping
// it moves its own test plus the two canonicality tests (`encode_decode_
// roundtrip`, `encoding_is_independent_of_pool_warmth_and_interner_order`),
// which is the signal that `false` is not a choice.
pub const FINGERPRINT_POLICY: FingerprintPolicy = FingerprintPolicy {
    include_const_value: true, // §14 Q4: over-invalidate rather than risk a stale dependent
    exclude_gparam_names: true, // §14 Q5: R38(a) is positional, so a name is not observable
    sort_bound_lists: true,    // §14 Q6: `T: Eq + Ord` is the same bound set as `T: Ord + Eq`
};

pub fn decl_fingerprint(fir: &Fir, names: &Interner, def: DefId) -> u128 {
    hash_bytes(&encode_sig(fir, names, def, FINGERPRINT_POLICY))
}

/// §5.4's `sig_hash`: the value stored in `SigStore.sig_hash` and the early
/// cutoff every dependent compares. It is [`decl_fingerprint`] by definition —
/// there is one policy, in one place.
pub fn sig_hash(fir: &Fir, names: &Interner, def: DefId) -> u128 {
    decl_fingerprint(fir, names, def)
}

// ------------------------------------------------------------------ writing

fn uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7F) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn write_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    uleb(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

/// A declaration key, as bytes: its parent chain, its module segments, its
/// kind, its name and its disambiguator. No index anywhere.
fn write_decl_key(out: &mut Vec<u8>, keys: &DeclKeyTable, names: &Interner, key: DeclKeyId) {
    if key == NO_DECL_KEY {
        // MARC: a head whose declaration this build never keyed. It cannot
        // happen in a real lowering (every `DefId` gets a `DeclKey` in I2) and
        // it is not portable, so it encodes as a marker plus nothing and is
        // asserted against in debug builds. Hand-built types in unit tests are
        // the only producers.
        debug_assert!(false, "encoding a head with no DeclKey");
        out.push(2);
        return;
    }
    let row = keys.row(key);
    if row.parent == NO_DECL_KEY {
        out.push(0);
    } else {
        out.push(1);
        write_decl_key(out, keys, names, row.parent);
    }
    let segs = keys.paths.segments(row.module);
    uleb(out, segs.len() as u64);
    for &s in segs {
        write_bytes(out, names.resolve(s));
    }
    out.push(row.kind as u8);
    match row.name {
        None => out.push(0),
        Some(n) => {
            out.push(1);
            write_bytes(out, names.resolve(n));
        }
    }
    uleb(out, row.disamb as u64);
}

fn write_const_value(out: &mut Vec<u8>, names: &Interner, v: ConstValue) {
    match v {
        ConstValue::I(n) => {
            out.push(1);
            out.extend_from_slice(&n.to_le_bytes());
        }
        ConstValue::B(b) => {
            out.push(2);
            out.push(b as u8);
        }
        ConstValue::S(s) => {
            out.push(3);
            write_bytes(out, names.resolve(s));
        }
    }
}

struct Enc<'a> {
    fir: &'a Fir,
    names: &'a Interner,
    policy: FingerprintPolicy,
    /// The type-entry section.
    tys: Vec<u8>,
    /// The signature-structure section.
    body: Vec<u8>,
    /// `TyId` -> stream position. Lookups only; positions are assigned in
    /// emission order, so no iteration order can leak in.
    pos: std::collections::HashMap<TyId, u32>,
    next: u32,
    self_key: DeclKeyId,
    parent_key: DeclKeyId,
}

impl<'a> Enc<'a> {
    fn new(
        fir: &'a Fir,
        names: &'a Interner,
        policy: FingerprintPolicy,
        self_key: DeclKeyId,
        parent_key: DeclKeyId,
    ) -> Enc<'a> {
        Enc {
            fir,
            names,
            policy,
            tys: Vec::new(),
            body: Vec::new(),
            pos: std::collections::HashMap::new(),
            next: 0,
            self_key,
            parent_key,
        }
    }

    fn key_of(&self, def: DefId) -> DeclKeyId {
        self.fir.defs.key_of(def)
    }

    /// Emits `t`'s entry if it is new and returns its stream position. Children
    /// are emitted first, so every reference inside an entry points backwards.
    fn emit_ty(&mut self, t: TyId) -> u32 {
        if let Some(&p) = self.pos.get(&t) {
            return p;
        }
        debug_assert_ne!(t, NO_TY, "NO_TY is an absent column, not a type");
        let store = &self.fir.tys;
        let tag = store.tag(t);
        let a = store.a(t);
        let b = store.b(t);
        let quals = store.quals(t);

        // Children first (this may append entries of its own).
        let mut child_refs: Vec<u32> = Vec::new();
        let mut head_ref = 0u32;
        let mut param_convs: Vec<Conv> = Vec::new();
        let mut result_ref = 0u32;
        let mut raises_ref: Option<u32> = None;
        let mut closure = false;
        let mut const_ty_ref = 0u32;
        match tag {
            TyTag::Nominal | TyTag::Tuple => {
                for x in self.fir.tys.args_vec(ArgsId(b)) {
                    let r = self.emit_ty(x);
                    child_refs.push(r);
                }
            }
            TyTag::Dyn => {
                let (_, args) = self.fir.tys.trait_ref(TraitRefId(a));
                for x in self.fir.tys.args_vec(args) {
                    let r = self.emit_ty(x);
                    child_refs.push(r);
                }
            }
            TyTag::Fn => {
                let id = FnTyId(a);
                let (convs, tys) = {
                    let (c, x) = self.fir.tys.fn_tys().params(id);
                    (c.to_vec(), x.to_vec())
                };
                param_convs = convs;
                for x in tys {
                    let r = self.emit_ty(x);
                    child_refs.push(r);
                }
                let result = self.fir.tys.fn_tys().result(id);
                result_ref = self.emit_ty(result);
                let raises = self.fir.tys.fn_tys().raises(id);
                if raises != NO_TY {
                    raises_ref = Some(self.emit_ty(raises));
                }
                closure = self.fir.tys.fn_tys().is_closure(id);
            }
            TyTag::Proj => {
                head_ref = self.emit_ty(TyId(a));
                let (tr, _) = self.fir.tys.proj_key(ProjKeyId(b));
                let (_, args) = self.fir.tys.trait_ref(tr);
                for x in self.fir.tys.args_vec(args) {
                    let r = self.emit_ty(x);
                    child_refs.push(r);
                }
            }
            TyTag::ConstVal => {
                const_ty_ref = self.emit_ty(TyId(b));
            }
            _ => {}
        }

        // Every entry is `tag, quals, payload` — including `()`, `never` and the
        // error type, which can carry qualifiers like anything else. Leaving the
        // qualifier byte off for those three would make `iso ()` and `()` the
        // same entry, so a signature mentioning both would decode to one type
        // and re-encode a byte shorter.
        let mut e: Vec<u8> = Vec::new();
        e.push(match tag {
            TyTag::Error => E_ERROR,
            TyTag::Unit => E_UNIT,
            TyTag::Never => E_NEVER,
            TyTag::Prim => E_PRIM,
            TyTag::Nominal => E_NOMINAL,
            TyTag::Tuple => E_TUPLE,
            TyTag::Fn => E_FN,
            TyTag::Dyn => E_DYN,
            TyTag::Param => E_PARAM,
            TyTag::Proj => E_PROJ,
            TyTag::Brand => E_BRAND,
            TyTag::ConstVal => E_CONSTVAL,
        });
        e.push(quals.0);
        match tag {
            TyTag::Error | TyTag::Unit | TyTag::Never => {}
            TyTag::Prim => {
                e.push(a as u8);
            }
            TyTag::Nominal => {
                let key = self.key_of(DefId(a));
                write_decl_key(&mut e, &self.fir.keys, self.names, key);
                uleb(&mut e, child_refs.len() as u64);
                for r in &child_refs {
                    uleb(&mut e, *r as u64);
                }
            }
            TyTag::Tuple => {
                uleb(&mut e, child_refs.len() as u64);
                for r in &child_refs {
                    uleb(&mut e, *r as u64);
                }
            }
            TyTag::Fn => {
                let mut flags = 0u8;
                if closure {
                    flags |= FN_CLOSURE;
                }
                if raises_ref.is_some() {
                    flags |= FN_RAISES;
                }
                e.push(flags);
                uleb(&mut e, child_refs.len() as u64);
                for (i, r) in child_refs.iter().enumerate() {
                    e.push(param_convs[i] as u8);
                    uleb(&mut e, *r as u64);
                }
                uleb(&mut e, result_ref as u64);
                if let Some(r) = raises_ref {
                    uleb(&mut e, r as u64);
                }
            }
            TyTag::Dyn => {
                let (td, _) = self.fir.tys.trait_ref(TraitRefId(a));
                let key = self.key_of(td);
                write_decl_key(&mut e, &self.fir.keys, self.names, key);
                uleb(&mut e, child_refs.len() as u64);
                for r in &child_refs {
                    uleb(&mut e, *r as u64);
                }
            }
            TyTag::Param => {
                self.write_owner(&mut e, DefId(a));
                uleb(&mut e, b as u64);
            }
            TyTag::Proj => {
                uleb(&mut e, head_ref as u64);
                let (tr, name) = self.fir.tys.proj_key(ProjKeyId(b));
                let (td, _) = self.fir.tys.trait_ref(tr);
                let key = self.key_of(td);
                write_decl_key(&mut e, &self.fir.keys, self.names, key);
                uleb(&mut e, child_refs.len() as u64);
                for r in &child_refs {
                    uleb(&mut e, *r as u64);
                }
                write_bytes(&mut e, self.names.resolve(name));
            }
            TyTag::Brand => {
                // §5.4: a fresh brand in a signature is a bug (ch01 R15 keeps
                // it inside its `with` block) and encodes as `Error`.
                match self.fir.tys.brand(BrandId(b)) {
                    BrandRow::Param { owner, ordinal } => {
                        self.write_owner(&mut e, owner);
                        uleb(&mut e, ordinal as u64);
                    }
                    BrandRow::Fresh { .. } => {
                        // §5.4: ch01 R15 keeps a fresh brand inside its `with`
                        // block, so one in a signature is a bug; it is rewritten
                        // to the error type rather than encoded.
                        debug_assert!(false, "a fresh brand reached a signature");
                        e.clear();
                        e.push(E_ERROR);
                        e.push(0);
                    }
                }
            }
            TyTag::ConstVal => {
                let v = self.fir.tys.const_value(ConstId(a));
                write_const_value(&mut e, self.names, v);
                uleb(&mut e, const_ty_ref as u64);
            }
        }
        self.tys.extend_from_slice(&e);
        let p = self.next;
        self.next += 1;
        self.pos.insert(t, p);
        p
    }

    /// A parameter or brand owner: relative when it is this declaration or its
    /// enclosing `impl`/`trait`, absolute (its key bytes) otherwise.
    fn write_owner(&self, out: &mut Vec<u8>, owner: DefId) {
        let key = self.key_of(owner);
        if key != NO_DECL_KEY && key == self.self_key {
            out.push(0);
            uleb(out, 0);
        } else if key != NO_DECL_KEY && key == self.parent_key {
            out.push(0);
            uleb(out, 1);
        } else {
            out.push(1);
            write_decl_key(out, &self.fir.keys, self.names, key);
        }
    }

    fn trait_ref_bytes(&mut self, tr: TraitRefId) -> Vec<u8> {
        let (td, args) = self.fir.tys.trait_ref(tr);
        let xs = self.fir.tys.args_vec(args);
        let mut refs = Vec::with_capacity(xs.len());
        for x in xs {
            refs.push(self.emit_ty(x));
        }
        let mut out = Vec::new();
        let key = self.key_of(td);
        write_decl_key(&mut out, &self.fir.keys, self.names, key);
        uleb(&mut out, refs.len() as u64);
        for r in refs {
            uleb(&mut out, r as u64);
        }
        out
    }

    /// A trait reference encoded self-containedly (its own local type stream),
    /// used only as a sort key. Position-independent by construction.
    fn canon_trait_ref(&self, tr: TraitRefId) -> Vec<u8> {
        let mut sub = Enc::new(
            self.fir,
            self.names,
            self.policy,
            self.self_key,
            self.parent_key,
        );
        let tail = sub.trait_ref_bytes(tr);
        let mut out = Vec::new();
        uleb(&mut out, sub.next as u64);
        out.extend_from_slice(&sub.tys);
        out.extend_from_slice(&tail);
        out
    }

    fn canon_ty(&self, t: TyId) -> Vec<u8> {
        let mut sub = Enc::new(
            self.fir,
            self.names,
            self.policy,
            self.self_key,
            self.parent_key,
        );
        sub.emit_ty(t);
        let mut out = Vec::new();
        uleb(&mut out, sub.next as u64);
        out.extend_from_slice(&sub.tys);
        out
    }

    /// `n` bounds, canonically ordered (§14 Q6).
    fn bound_list_bytes(&mut self, list: TraitRefListId) -> Vec<u8> {
        let bounds = self.fir.sigs.bounds.get(list).to_vec();
        let mut keyed: Vec<(Vec<u8>, TraitRefId)> = bounds
            .iter()
            .map(|&tr| (self.canon_trait_ref(tr), tr))
            .collect();
        if self.policy.sort_bound_lists {
            keyed.sort_by(|x, y| x.0.cmp(&y.0));
        }
        let mut out = Vec::new();
        uleb(&mut out, keyed.len() as u64);
        for (_, tr) in keyed {
            let b = self.trait_ref_bytes(tr);
            out.extend_from_slice(&b);
        }
        out
    }

    fn encode_generics(&mut self, def: DefId) {
        let g = self.fir.sigs.generics(def);
        let n = self.fir.sigs.generics_store.count(g);
        uleb(&mut self.body, n as u64);
        for i in 0..n {
            let p = self.fir.sigs.generics_store.param(g, i);
            let mut chunk = Vec::new();
            chunk.push(p.kind.tag());
            match p.kind {
                GParamKind::Const { ty } | GParamKind::Callable { fn_ty: ty } => {
                    let r = self.emit_ty(ty);
                    uleb(&mut chunk, r as u64);
                }
                GParamKind::Type | GParamKind::Brand => {}
            }
            // §14 Q5: the name is observable only in a message, never in a rule.
            if !self.policy.exclude_gparam_names {
                write_bytes(&mut chunk, self.names.resolve(p.name));
            }
            let bounds = self.bound_list_bytes(p.bounds);
            chunk.extend_from_slice(&bounds);
            self.body.extend_from_slice(&chunk);
        }
    }

    fn encode_constraints(&mut self, def: DefId) {
        let g = self.fir.sigs.generics(def);
        let cl = self.fir.sigs.generics_store.constraints(g);
        let n = self.fir.sigs.constraints.count(cl);
        let mut entries: Vec<(Vec<u8>, (TyId, TraitRefListId))> = Vec::with_capacity(n);
        for i in 0..n {
            let e = self.fir.sigs.constraints.entry(cl, i);
            let mut key = self.canon_ty(e.0);
            let bounds = self.fir.sigs.bounds.get(e.1).to_vec();
            for tr in bounds {
                key.extend_from_slice(&self.canon_trait_ref(tr));
            }
            entries.push((key, e));
        }
        if self.policy.sort_bound_lists {
            entries.sort_by(|x, y| x.0.cmp(&y.0));
        }
        uleb(&mut self.body, n as u64);
        for (_, (subject, bounds)) in entries {
            let r = self.emit_ty(subject);
            uleb(&mut self.body, r as u64);
            let b = self.bound_list_bytes(bounds);
            self.body.extend_from_slice(&b);
        }
    }

    fn encode_fn(&mut self, def: DefId) {
        let f = self.fir.sigs.fn_sig(def);
        if f == NO_FN_SIG {
            uleb(&mut self.body, 0);
            uleb(&mut self.body, 0);
            self.body.push(0);
            self.body.push(NO_SLOT);
            self.body.push(NO_SLOT);
            self.body.extend_from_slice(&0u128.to_le_bytes());
            return;
        }
        let n = self.fir.sigs.fn_sigs.count(f);
        uleb(&mut self.body, n as u64);
        for i in 0..n {
            let p = self.fir.sigs.fn_sigs.param(f, i);
            let r = self.emit_ty(p.ty);
            // R37 makes a label observable, so parameter names are in the hash.
            let name = self.names.resolve(p.name).to_vec();
            write_bytes(&mut self.body, &name);
            self.body.push(p.conv as u8);
            uleb(&mut self.body, r as u64);
        }
        let result = self.fir.sigs.fn_sigs.result(f);
        let r = self.emit_ty(result);
        uleb(&mut self.body, r as u64);
        let raises = self.fir.sigs.fn_sigs.raises(f);
        if raises == NO_TY {
            self.body.push(0);
        } else {
            let r = self.emit_ty(raises);
            self.body.push(1);
            uleb(&mut self.body, r as u64);
        }
        self.body.push(self.fir.sigs.fn_sigs.scoped(f));
        self.body.push(self.fir.sigs.fn_sigs.receiver(f));
        // ch02 R9 makes a contract clause part of the declaration.
        let h = self.fir.sigs.fn_sigs.contract_hash(f);
        self.body.extend_from_slice(&h.to_le_bytes());
    }

    fn encode_fields(&mut self, list: MemberListId) {
        let n = self.fir.sigs.member_store.count(list);
        uleb(&mut self.body, n as u64);
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(list, i);
            let r = self.emit_ty(m.ty);
            let name = self.names.resolve(m.name).to_vec();
            write_bytes(&mut self.body, &name);
            self.body.push(m.vis);
            uleb(&mut self.body, r as u64);
        }
    }

    fn encode_variants(&mut self, list: MemberListId) {
        let n = self.fir.sigs.member_store.count(list);
        uleb(&mut self.body, n as u64);
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(list, i);
            let name = self.names.resolve(m.name).to_vec();
            write_bytes(&mut self.body, &name);
            self.body.push(m.payload as u8);
            match m.payload {
                PayloadKind::None => {}
                PayloadKind::Tuple => {
                    let xs = self.fir.tys.args_vec(m.args);
                    let mut refs = Vec::with_capacity(xs.len());
                    for x in xs {
                        refs.push(self.emit_ty(x));
                    }
                    uleb(&mut self.body, refs.len() as u64);
                    for r in refs {
                        uleb(&mut self.body, r as u64);
                    }
                }
                PayloadKind::Record => self.encode_fields(m.sub),
            }
        }
    }

    /// Trait/impl items, as their declaration keys in source order.
    fn encode_items(&mut self, list: MemberListId) {
        let n = self.fir.sigs.member_store.count(list);
        let items: Vec<Member> = (0..n)
            .map(|i| self.fir.sigs.member_store.get(list, i))
            .filter(|m| m.kind == MemberKind::Item)
            .collect();
        uleb(&mut self.body, items.len() as u64);
        for m in items {
            let key = self.key_of(m.def);
            let mut chunk = Vec::new();
            write_decl_key(&mut chunk, &self.fir.keys, self.names, key);
            self.body.extend_from_slice(&chunk);
        }
    }

    /// A trait's associated-type declarations, or an impl's definitions.
    /// Sorted by name: the set has no source order that any rule observes.
    fn encode_assoc(&mut self, def: DefId, with_rhs: bool) {
        let a = self.fir.sigs.assoc(def);
        let n = self.fir.sigs.assocs.count(a);
        let mut entries: Vec<Assoc> = (0..n).map(|i| self.fir.sigs.assocs.get(a, i)).collect();
        entries.sort_by(|x, y| self.names.resolve(x.name).cmp(self.names.resolve(y.name)));
        uleb(&mut self.body, entries.len() as u64);
        for e in entries {
            let name = self.names.resolve(e.name).to_vec();
            write_bytes(&mut self.body, &name);
            if with_rhs {
                // R2: an impl's `type A = T;` is part of its signature.
                let r = self.emit_ty(e.rhs);
                uleb(&mut self.body, r as u64);
            } else {
                let b = self.bound_list_bytes(e.bounds);
                self.body.extend_from_slice(&b);
            }
        }
    }

    fn encode(&mut self, def: DefId) {
        let kind = self.fir.sigs.kind(def);
        self.body.push(kind as u8);
        self.body.push(self.fir.sigs.flags(def));
        self.encode_generics(def);
        self.encode_constraints(def);
        match kind {
            SigKind::Fn | SigKind::ExternFn => self.encode_fn(def),
            SigKind::Struct => {
                let m = self.fir.sigs.members(def);
                self.encode_fields(m);
            }
            SigKind::Enum => {
                let m = self.fir.sigs.members(def);
                self.encode_variants(m);
            }
            SigKind::Trait => {
                self.encode_assoc(def, false);
                let m = self.fir.sigs.members(def);
                self.encode_items(m);
            }
            SigKind::Impl => {
                let st = self.fir.sigs.self_ty(def);
                let r = if st == NO_TY {
                    u32::MAX
                } else {
                    self.emit_ty(st)
                };
                uleb(&mut self.body, r as u64);
                let tr = self.fir.sigs.trait_ref(def);
                if tr == NO_TRAIT_REF {
                    self.body.push(0);
                } else {
                    let b = self.trait_ref_bytes(tr);
                    self.body.push(1);
                    self.body.extend_from_slice(&b);
                }
                self.encode_assoc(def, true);
                let m = self.fir.sigs.members(def);
                self.encode_items(m);
            }
            SigKind::Const => {
                let ty = self.fir.sigs.const_ty(def);
                let r = if ty == NO_TY {
                    u32::MAX
                } else {
                    self.emit_ty(ty)
                };
                uleb(&mut self.body, r as u64);
                let cv = self.fir.sigs.const_val(def);
                // §14 Q4.
                if self.policy.include_const_value && cv != crate::ty::NO_CONST {
                    let v = self.fir.tys.const_value(cv);
                    self.body.push(1);
                    write_const_value(&mut self.body, self.names, v);
                } else {
                    self.body.push(0);
                }
            }
            SigKind::Poisoned | SigKind::Absent => {}
        }
    }
}

/// The canonical bytes of one declaration's signature under `policy`.
pub fn encode_sig(fir: &Fir, names: &Interner, def: DefId, policy: FingerprintPolicy) -> Vec<u8> {
    let self_key = fir.defs.key_of(def);
    let parent_key = if self_key == NO_DECL_KEY {
        NO_DECL_KEY
    } else {
        fir.keys.parent_of(self_key)
    };
    let mut e = Enc::new(fir, names, policy, self_key, parent_key);
    e.encode(def);
    let mut out = Vec::with_capacity(e.tys.len() + e.body.len() + 8);
    out.extend_from_slice(MAGIC);
    out.push(policy.to_byte());
    uleb(&mut out, e.next as u64);
    out.extend_from_slice(&e.tys);
    out.extend_from_slice(&e.body);
    out
}

// ------------------------------------------------------------------ reading

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DecodeError {
    Truncated,
    BadMagic,
    BadTag(u8),
    BadRef(u32),
    BadUtf8Length,
    /// A length prefix larger than the bytes that remain, or than the pool it
    /// would fill can hold (a function's 255 parameters, a list's `u16`).
    BadCount(u64),
    /// A declaration key nested deeper than any real declaration can be.
    TooDeep,
    /// A byte that violates a store invariant: a projection on a concrete head,
    /// an empty tuple, `iso imm`, an unknown qualifier bit.
    BadShape,
}

type R<T> = Result<T, DecodeError>;

/// Longest list any pool holds (`u16` lengths throughout `sig.rs`/`ty.rs`).
const MAX_LIST: usize = u16::MAX as usize;
/// `FnTys::p_len` and `FnSigStore::p_len` are a byte.
const MAX_FN_PARAMS: usize = u8::MAX as usize;
/// A declaration key's parent chain: an item in an impl in a module. Eight is
/// generous; a stream of `1` marks would otherwise recurse once per byte.
const MAX_KEY_DEPTH: u32 = 8;

struct Dec<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Dec<'a> {
    fn byte(&mut self) -> R<u8> {
        let v = *self.b.get(self.i).ok_or(DecodeError::Truncated)?;
        self.i += 1;
        Ok(v)
    }

    // MARC (verification round): every length prefix goes through here. The
    // previous decoder did `Vec::with_capacity(d.uleb()? as usize)`, so a
    // ten-byte prefix of 2^63 was a capacity-overflow panic and a prefix of
    // 300 on a function type reached `intern_fn_ty`'s `expect("more than 255
    // parameters")`. Malformed bytes are an `Err`, never a panic: a count is
    // rejected when it exceeds `max`, or the bytes left — each counted item
    // is at least one byte, so a larger count cannot be honest.
    fn count(&mut self, max: usize) -> R<usize> {
        let n = self.uleb()?;
        let left = (self.b.len() - self.i) as u64;
        if n > max as u64 || n > left {
            return Err(DecodeError::BadCount(n));
        }
        Ok(n as usize)
    }

    fn ordinal(&mut self) -> R<u16> {
        let v = self.uleb()?;
        u16::try_from(v).map_err(|_| DecodeError::BadCount(v))
    }

    fn uleb(&mut self) -> R<u64> {
        let mut v = 0u64;
        let mut shift = 0u32;
        loop {
            let byte = self.byte()?;
            v |= ((byte & 0x7F) as u64) << shift;
            if byte & 0x80 == 0 {
                return Ok(v);
            }
            shift += 7;
            if shift > 63 {
                return Err(DecodeError::BadUtf8Length);
            }
        }
    }

    fn bytes(&mut self) -> R<&'a [u8]> {
        let n = self.uleb()? as usize;
        let end = self.i.checked_add(n).ok_or(DecodeError::Truncated)?;
        let s = self.b.get(self.i..end).ok_or(DecodeError::Truncated)?;
        self.i = end;
        Ok(s)
    }

    fn u128(&mut self) -> R<u128> {
        let end = self.i + 16;
        let s = self.b.get(self.i..end).ok_or(DecodeError::Truncated)?;
        self.i = end;
        let mut buf = [0u8; 16];
        buf.copy_from_slice(s);
        Ok(u128::from_le_bytes(buf))
    }
}

fn read_decl_key(d: &mut Dec, fir: &mut Fir, names: &mut Interner) -> R<DeclKeyId> {
    read_decl_key_at(d, fir, names, 0)
}

fn read_decl_key_at(d: &mut Dec, fir: &mut Fir, names: &mut Interner, depth: u32) -> R<DeclKeyId> {
    if depth > MAX_KEY_DEPTH {
        return Err(DecodeError::TooDeep);
    }
    let mark = d.byte()?;
    let parent = match mark {
        0 => NO_DECL_KEY,
        1 => read_decl_key_at(d, fir, names, depth + 1)?,
        // MARC (verification round): mark 2 is the encoder's "head with no
        // DeclKey" marker, which only hand-built test types ever produce and
        // which `write_decl_key` already asserts against. The decoder used to
        // accept it and hand `NO_DECL_KEY` to `def_for_key`, whose `DefKeys::
        // bind` then resized its table to index `u32::MAX` — a 16 GB
        // allocation from one byte of a `.fmod`. A real interface file never
        // contains it, so it is malformed input here, not a value.
        2 => return Err(DecodeError::BadShape),
        other => return Err(DecodeError::BadTag(other)),
    };
    let nsegs = d.count(MAX_LIST)?;
    let mut segs: Vec<Symbol> = Vec::with_capacity(nsegs);
    for _ in 0..nsegs {
        let bytes = d.bytes()?.to_vec();
        segs.push(names.intern(&bytes));
    }
    let kind = decl_kind_from_u8(d.byte()?).ok_or(DecodeError::BadTag(0))?;
    let name = match d.byte()? {
        0 => None,
        1 => {
            let bytes = d.bytes()?.to_vec();
            Some(names.intern(&bytes))
        }
        other => return Err(DecodeError::BadTag(other)),
    };
    let disamb = d.uleb()? as u32;
    let module = fir.keys.paths.intern(&segs);
    Ok(fir.keys.intern(DeclKey {
        parent,
        module,
        kind,
        name,
        disamb,
    }))
}

fn read_def(d: &mut Dec, fir: &mut Fir, names: &mut Interner) -> R<DefId> {
    let key = read_decl_key(d, fir, names)?;
    Ok(fir.def_for_key(key))
}

fn read_const_value(d: &mut Dec, names: &mut Interner) -> R<ConstValue> {
    match d.byte()? {
        1 => {
            let n = d.u128()?;
            Ok(ConstValue::I(n as i128))
        }
        2 => Ok(ConstValue::B(d.byte()? != 0)),
        3 => {
            let bytes = d.bytes()?.to_vec();
            Ok(ConstValue::S(names.intern(&bytes)))
        }
        other => Err(DecodeError::BadTag(other)),
    }
}

struct DecCx {
    tys: Vec<TyId>,
    self_def: DefId,
    parent_def: DefId,
}

impl DecCx {
    fn ty(&self, r: u64) -> R<TyId> {
        self.tys
            .get(r as usize)
            .copied()
            .ok_or(DecodeError::BadRef(r as u32))
    }
}

fn read_owner(d: &mut Dec, fir: &mut Fir, names: &mut Interner, cx: &DecCx) -> R<DefId> {
    match d.byte()? {
        0 => {
            let depth = d.uleb()?;
            Ok(if depth == 0 {
                cx.self_def
            } else {
                cx.parent_def
            })
        }
        1 => read_def(d, fir, names),
        other => Err(DecodeError::BadTag(other)),
    }
}

fn read_ty_entry(d: &mut Dec, fir: &mut Fir, names: &mut Interner, cx: &DecCx) -> R<TyId> {
    let tag = d.byte()?;
    let quals = Quals(d.byte()?);
    if quals.0 & !(crate::ty::Q_ISO | crate::ty::Q_IMM | crate::ty::Q_SECRET) != 0
        || !quals.is_consistent()
    {
        return Err(DecodeError::BadShape);
    }
    let base = match tag {
        E_ERROR => crate::ty::TY_ERROR,
        E_UNIT => crate::ty::TY_UNIT,
        E_NEVER => crate::ty::TY_NEVER,
        E_PRIM => {
            let k = PrimKind::from_u8(d.byte()?).ok_or(DecodeError::BadTag(tag))?;
            fir.tys.prim(k)
        }
        E_NOMINAL => {
            let def = read_def(d, fir, names)?;
            let n = d.count(MAX_LIST)?;
            let mut args = Vec::with_capacity(n);
            for _ in 0..n {
                args.push(cx.ty(d.uleb()?)?);
            }
            fir.tys.nominal_of(def, &args)
        }
        E_TUPLE => {
            let n = d.count(MAX_LIST)?;
            if n == 0 {
                return Err(DecodeError::BadShape); // `()` is TY_UNIT, never an empty tuple
            }
            let mut args = Vec::with_capacity(n);
            for _ in 0..n {
                args.push(cx.ty(d.uleb()?)?);
            }
            fir.tys.tuple_of(&args)
        }
        E_FN => {
            let flags = d.byte()?;
            if flags & !(FN_CLOSURE | FN_RAISES) != 0 {
                return Err(DecodeError::BadShape);
            }
            let n = d.count(MAX_FN_PARAMS)?;
            let mut params = Vec::with_capacity(n);
            for _ in 0..n {
                let conv = Conv::from_u8(d.byte()?).ok_or(DecodeError::BadTag(tag))?;
                params.push((conv, cx.ty(d.uleb()?)?));
            }
            let result = cx.ty(d.uleb()?)?;
            let raises = if flags & FN_RAISES != 0 {
                cx.ty(d.uleb()?)?
            } else {
                NO_TY
            };
            let f = fir
                .tys
                .intern_fn_ty(&params, result, raises, flags & FN_CLOSURE != 0);
            fir.tys.fn_ty(f)
        }
        E_DYN => {
            let def = read_def(d, fir, names)?;
            let n = d.count(MAX_LIST)?;
            let mut args = Vec::with_capacity(n);
            for _ in 0..n {
                args.push(cx.ty(d.uleb()?)?);
            }
            let a = fir.tys.intern_args(&args);
            let tr = fir.tys.intern_trait_ref(def, a);
            fir.tys.dyn_ty(tr)
        }
        E_PARAM => {
            let owner = read_owner(d, fir, names, cx)?;
            let ordinal = d.ordinal()?;
            fir.tys.param(owner, ordinal)
        }
        E_PROJ => {
            let head = cx.ty(d.uleb()?)?;
            if !fir.tys.is_rigid(head) {
                return Err(DecodeError::BadShape); // R20: a projection's head is a Param or a Proj
            }
            let def = read_def(d, fir, names)?;
            let n = d.count(MAX_LIST)?;
            let mut args = Vec::with_capacity(n);
            for _ in 0..n {
                args.push(cx.ty(d.uleb()?)?);
            }
            let name_bytes = d.bytes()?.to_vec();
            let name = names.intern(&name_bytes);
            fir.tys.proj_of(head, def, &args, name)
        }
        E_BRAND => {
            let owner = read_owner(d, fir, names, cx)?;
            let ordinal = d.ordinal()?;
            fir.tys.brand_ty(BrandRow::Param { owner, ordinal })
        }
        E_CONSTVAL => {
            let v = read_const_value(d, names)?;
            let ty = cx.ty(d.uleb()?)?;
            fir.tys.const_ty(v, ty)
        }
        other => return Err(DecodeError::BadTag(other)),
    };
    Ok(if quals.is_none() {
        base
    } else {
        fir.tys.qualified(base, quals)
    })
}

fn read_bounds(d: &mut Dec, fir: &mut Fir, names: &mut Interner, cx: &DecCx) -> R<TraitRefListId> {
    let n = d.count(MAX_LIST)?;
    if n == 0 {
        return Ok(NO_BOUNDS);
    }
    let mut trs = Vec::with_capacity(n);
    for _ in 0..n {
        let def = read_def(d, fir, names)?;
        let m = d.count(MAX_LIST)?;
        let mut args = Vec::with_capacity(m);
        for _ in 0..m {
            args.push(cx.ty(d.uleb()?)?);
        }
        let a = fir.tys.intern_args(&args);
        trs.push(fir.tys.intern_trait_ref(def, a));
    }
    Ok(fir.sigs.bounds.intern(&trs))
}

fn read_fields(d: &mut Dec, fir: &mut Fir, names: &mut Interner, cx: &DecCx) -> R<MemberListId> {
    let n = d.count(MAX_LIST)?;
    let mut ms = Vec::with_capacity(n);
    for _ in 0..n {
        let name_bytes = d.bytes()?.to_vec();
        let name = names.intern(&name_bytes);
        let vis = d.byte()?;
        let ty = cx.ty(d.uleb()?)?;
        ms.push(Member::field(name, vis, ty));
    }
    Ok(fir.sigs.member_store.push(&ms))
}

/// Re-interns one encoded signature into `fir`, bottom-up, re-establishing
/// hash-consing (§5.4). `self_key` is the declaration being read — the anchor
/// the relative `Param` markers resolve against.
pub fn decode_sig(
    bytes: &[u8],
    fir: &mut Fir,
    names: &mut Interner,
    self_key: DeclKeyId,
) -> R<DefId> {
    let mut d = Dec { b: bytes, i: 0 };
    for &m in MAGIC {
        if d.byte()? != m {
            return Err(DecodeError::BadMagic);
        }
    }
    let policy = FingerprintPolicy::from_byte(d.byte()?);
    let n_entries = d.count(MAX_LIST)?;

    let self_def = fir.def_for_key(self_key);
    let parent_key = fir.keys.parent_of(self_key);
    let parent_def = if parent_key == NO_DECL_KEY {
        self_def
    } else {
        fir.def_for_key(parent_key)
    };
    let mut cx = DecCx {
        tys: Vec::with_capacity(n_entries),
        self_def,
        parent_def,
    };
    for _ in 0..n_entries {
        let t = read_ty_entry(&mut d, fir, names, &cx)?;
        cx.tys.push(t);
    }

    let kind = SigKind::from_u8(d.byte()?).ok_or(DecodeError::BadTag(0))?;
    let flags = d.byte()?;

    // Generics, then constraint entries.
    let ngp = d.count(MAX_LIST)?;
    let mut gparams: Vec<GParam> = Vec::with_capacity(ngp);
    for i in 0..ngp {
        let kind_tag = d.byte()?;
        let kind = match kind_tag {
            0 => GParamKind::Type,
            1 => GParamKind::Const {
                ty: cx.ty(d.uleb()?)?,
            },
            2 => GParamKind::Brand,
            3 => GParamKind::Callable {
                fn_ty: cx.ty(d.uleb()?)?,
            },
            other => return Err(DecodeError::BadTag(other)),
        };
        // §14 Q5: excluded from the encoding, so not recoverable. A positional
        // placeholder keeps the row well-formed; T0039's message reads the
        // current source's name, never this one.
        let name = if policy.exclude_gparam_names {
            names.intern(format!("_{i}").as_bytes())
        } else {
            let bytes = d.bytes()?.to_vec();
            names.intern(&bytes)
        };
        let bounds = read_bounds(&mut d, fir, names, &cx)?;
        gparams.push(GParam { name, kind, bounds });
    }
    let ncon = d.count(MAX_LIST)?;
    let mut constraints = Vec::with_capacity(ncon);
    for _ in 0..ncon {
        let subject = cx.ty(d.uleb()?)?;
        let bounds = read_bounds(&mut d, fir, names, &cx)?;
        constraints.push((subject, bounds));
    }
    let cl = fir.sigs.constraints.push(&constraints);
    let g = fir.sigs.generics_store.push(&gparams, cl);

    fir.sigs.set_kind(self_def, kind);
    fir.sigs.set_soa(self_def, flags & crate::sig::SIG_SOA != 0);
    fir.sigs.set_generics(self_def, g);

    match kind {
        SigKind::Fn | SigKind::ExternFn => {
            let n = d.count(MAX_FN_PARAMS)?;
            let mut params = Vec::with_capacity(n);
            for _ in 0..n {
                let name_bytes = d.bytes()?.to_vec();
                let name = names.intern(&name_bytes);
                let conv = Conv::from_u8(d.byte()?).ok_or(DecodeError::BadTag(0))?;
                let ty = cx.ty(d.uleb()?)?;
                params.push(crate::sig::Param { name, conv, ty });
            }
            let result = cx.ty(d.uleb()?)?;
            let raises = match d.byte()? {
                0 => NO_TY,
                1 => cx.ty(d.uleb()?)?,
                other => return Err(DecodeError::BadTag(other)),
            };
            let scoped = d.byte()?;
            let receiver = d.byte()?;
            let contract_hash = d.u128()?;
            // The CST node range is build-local and deliberately not in these
            // bytes: a decoded signature is read, never re-checked.
            let f = fir.sigs.fn_sigs.push(
                &params,
                result,
                raises,
                scoped,
                receiver,
                (0, 0),
                contract_hash,
            );
            fir.sigs.set_fn_sig(self_def, f);
        }
        SigKind::Struct => {
            let m = read_fields(&mut d, fir, names, &cx)?;
            fir.sigs.set_members(self_def, m);
        }
        SigKind::Enum => {
            let n = d.count(MAX_LIST)?;
            let mut ms = Vec::with_capacity(n);
            for _ in 0..n {
                let name_bytes = d.bytes()?.to_vec();
                let name = names.intern(&name_bytes);
                let payload = PayloadKind::from_u8(d.byte()?).ok_or(DecodeError::BadTag(0))?;
                let m = match payload {
                    PayloadKind::None => Member::unit_variant(name),
                    PayloadKind::Tuple => {
                        let k = d.count(MAX_LIST)?;
                        let mut args = Vec::with_capacity(k);
                        for _ in 0..k {
                            args.push(cx.ty(d.uleb()?)?);
                        }
                        let a = fir.tys.intern_args(&args);
                        Member::tuple_variant(name, a)
                    }
                    PayloadKind::Record => {
                        let sub = read_fields(&mut d, fir, names, &cx)?;
                        Member::record_variant(name, sub)
                    }
                };
                ms.push(m);
            }
            let list = fir.sigs.member_store.push(&ms);
            fir.sigs.set_members(self_def, list);
        }
        SigKind::Trait => {
            let n = d.count(MAX_LIST)?;
            let mut assocs = Vec::with_capacity(n);
            for _ in 0..n {
                let name_bytes = d.bytes()?.to_vec();
                let name = names.intern(&name_bytes);
                let bounds = read_bounds(&mut d, fir, names, &cx)?;
                assocs.push(Assoc {
                    name,
                    bounds,
                    rhs: NO_TY,
                });
            }
            let a = fir.sigs.assocs.push(&assocs);
            fir.sigs.set_assoc(self_def, a);
            let items = read_items(&mut d, fir, names)?;
            fir.sigs.set_members(self_def, items);
        }
        SigKind::Impl => {
            let r = d.uleb()?;
            let self_ty = if r == u32::MAX as u64 {
                NO_TY
            } else {
                cx.ty(r)?
            };
            fir.sigs.set_self_ty(self_def, self_ty);
            match d.byte()? {
                0 => {}
                1 => {
                    let def = read_def(&mut d, fir, names)?;
                    let m = d.count(MAX_LIST)?;
                    let mut args = Vec::with_capacity(m);
                    for _ in 0..m {
                        args.push(cx.ty(d.uleb()?)?);
                    }
                    let a = fir.tys.intern_args(&args);
                    let tr = fir.tys.intern_trait_ref(def, a);
                    fir.sigs.set_trait_ref(self_def, tr);
                }
                other => return Err(DecodeError::BadTag(other)),
            }
            let n = d.count(MAX_LIST)?;
            let mut assocs = Vec::with_capacity(n);
            for _ in 0..n {
                let name_bytes = d.bytes()?.to_vec();
                let name = names.intern(&name_bytes);
                let rhs = cx.ty(d.uleb()?)?;
                assocs.push(Assoc {
                    name,
                    bounds: NO_BOUNDS,
                    rhs,
                });
            }
            let a = fir.sigs.assocs.push(&assocs);
            fir.sigs.set_assoc(self_def, a);
            let items = read_items(&mut d, fir, names)?;
            fir.sigs.set_members(self_def, items);
        }
        SigKind::Const => {
            let r = d.uleb()?;
            let ty = if r == u32::MAX as u64 {
                NO_TY
            } else {
                cx.ty(r)?
            };
            let val = match d.byte()? {
                0 => crate::ty::NO_CONST,
                1 => {
                    let v = read_const_value(&mut d, names)?;
                    fir.tys.intern_const(v)
                }
                other => return Err(DecodeError::BadTag(other)),
            };
            fir.sigs.set_const(self_def, ty, val);
        }
        SigKind::Poisoned | SigKind::Absent => {}
    }
    Ok(self_def)
}

fn read_items(d: &mut Dec, fir: &mut Fir, names: &mut Interner) -> R<MemberListId> {
    let n = d.count(MAX_LIST)?;
    let mut ms = Vec::with_capacity(n);
    for _ in 0..n {
        let key = read_decl_key(d, fir, names)?;
        let def = fir.def_for_key(key);
        let name = fir.keys.row(key).name.unwrap_or(Symbol(0));
        ms.push(Member::item(name, crate::sig::VIS_PUBLIC, def));
    }
    Ok(fir.sigs.member_store.push(&ms))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decl_kind_bytes_round_trip() {
        for (i, &k) in DECL_KINDS.iter().enumerate() {
            assert_eq!(
                k as usize, i,
                "DECL_KINDS is out of step with DeclKind's order"
            );
            assert_eq!(decl_kind_from_u8(i as u8), Some(k));
        }
        assert_eq!(decl_kind_from_u8(DECL_KINDS.len() as u8), None);
    }

    #[test]
    fn uleb_round_trips() {
        for v in [
            0u64,
            1,
            127,
            128,
            300,
            16383,
            16384,
            u32::MAX as u64,
            u64::MAX >> 1,
        ] {
            let mut out = Vec::new();
            uleb(&mut out, v);
            let mut d = Dec { b: &out, i: 0 };
            assert_eq!(d.uleb().unwrap(), v);
            assert_eq!(d.i, out.len());
        }
    }

    #[test]
    fn policy_byte_round_trips() {
        for bits in 0u8..8 {
            let p = FingerprintPolicy::from_byte(bits);
            assert_eq!(p.to_byte(), bits);
        }
    }
}
