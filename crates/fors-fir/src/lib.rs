//! `fors-fir`: the Fors compiler's type and signature universe (design
//! `docs/design/type-checker.md` §4.1). Depends on `fors-index` only —
//! for `Symbol`, `Interner`, `DeclKind`, the id newtypes and the
//! fingerprint mixer (`hash_bytes`/`splitmix64`) — and knows nothing
//! about the CST, the resolver or diagnostics: this crate's outcomes are
//! plain data (types, signatures, hashes), never a `Diagnostic`, and it
//! must not (a CI test enforces this — see `tests/hygiene.rs`) mention
//! the parser crates (spelled with hyphens in this sentence so the
//! sentence itself does not trip that test), so the checker's dependency
//! on the parser cannot leak into the one crate every future increment treats
//! as ground truth for "is this the same type".
//!
//! Increment I1 (§13) lands: [`ty::TyStore`] with hash-consed interning so
//! type equality is an integer comparison (R9); [`cons::ConsTable`] and the
//! pools; the per-type flags byte that makes [`subst::subst_norm`] one load on
//! a monomorphic type; the [`sig::SigStore`] family; [`defpath::DeclKeyTable`]
//! and [`defpath::HeadKey`]; the canonical index-free signature
//! [`encode::encode_sig`]/[`encode::decode_sig`] with
//! [`encode::sig_hash`]; [`subst::one_way_match`]; and [`constval`].
//!
//! Still to come: `impls.rs` (the sorted impl index and R19 overlap) and
//! `normalise.rs` (R20) in I2/I6 — [`subst::ProjSolver`] is the seam they plug
//! into — `bounds.rs` (R12) in I4, `prelude.rs` in I2, `display.rs` in I3.

#![deny(unsafe_code)]

pub mod cons;
pub mod constval;
pub mod defpath;
pub mod encode;
pub mod impls;
pub mod prelude;
pub mod sig;
pub mod subst;
pub mod ty;

pub use cons::ConsTable;
pub use constval::ConstValue;
pub use defpath::{
    DeclKey, DeclKeyId, DeclKeyTable, DefKeys, HeadKey, ModulePathId, ModulePathTable, NO_DECL_KEY,
    NO_DEF, ROOT_PATH,
};
pub use encode::{
    DecodeError, EncodeScratch, FINGERPRINT_POLICY, FingerprintPolicy, decl_fingerprint,
    decode_sig, encode_sig, encode_sig_into, sig_hash, sig_hash_with,
};
pub use sig::{
    Assoc, AssocListId, AssocStore, ConstraintListId, ConstraintStore, Conv, FnSigId, FnSigStore,
    GParam, GParamKind, GenericsId, GenericsStore, Member, MemberKind, MemberListId, MemberStore,
    NO_ASSOC, NO_BOUNDS, NO_CONSTRAINTS, NO_FN_SIG, NO_GENERICS, NO_MEMBERS, NO_SLOT, NO_TRAIT_REF,
    Param, PayloadKind, SIG_SOA, SigKind, SigStore, TraitRefListId, TraitRefLists, VIS_PRIVATE,
    VIS_PUBLIC,
};
pub use subst::{
    Binding, BindingKey, NeutralOnly, ProjSolver, SubstMemo, one_way_match, one_way_match_with,
    subst_norm, subst_norm_cached, subst_norm_with,
};
pub use ty::{
    ArgsId, BrandId, BrandKind, BrandRow, ConstId, F_BRAND, F_ERROR, F_FRESH, F_OPEN, F_PARAM,
    F_PROJ, FnTyId, FnTys, NO_ARGS, NO_CONST, NO_TY, PrimKind, ProjKeyId, Q_IMM, Q_ISO, Q_SECRET,
    Quals, TY_ERROR, TY_NEVER, TY_UNIT, TraitRefId, TyId, TyStore, TyTag,
};

use fors_index::ids::DefId;

/// The four tables a build's FIR is: types, signatures, declaration keys, and
/// the map between a build's row numbers and those keys.
///
/// They travel together because every interesting operation needs at least
/// three of them (encoding a signature reads a type's nominal head, turns it
/// into a `DefId`, and turns that into key bytes), and because keeping the
/// `SigStore` and the `DefKeys` the same length is an invariant worth having
/// one owner for: [`Fir::def_for_key`] is the only way a `DefId` comes into
/// existence, and it appends to both.
#[derive(Default)]
pub struct Fir {
    pub tys: TyStore,
    pub sigs: SigStore,
    pub keys: DeclKeyTable,
    pub defs: DefKeys,
}

impl Fir {
    pub fn new() -> Fir {
        Fir {
            tys: TyStore::new(),
            sigs: SigStore::new(),
            keys: DeclKeyTable::new(),
            defs: DefKeys::new(),
        }
    }

    /// This build's row for `key`, allocating an [`SigKind::Absent`] row if the
    /// declaration has not been seen. `Absent` is the honest state for a name
    /// that something referred to before (or without) its signature being
    /// lowered — a `.fmod` head, a forward reference, a name that is declared
    /// nowhere at all.
    pub fn def_for_key(&mut self, key: DeclKeyId) -> DefId {
        // MARC (verification round): `NO_DECL_KEY` is `u32::MAX`, and binding
        // a row to it would resize `DefKeys::def` to four billion entries. No
        // caller means that; answer `NO_DEF` and let the debug build shout.
        debug_assert!(key != NO_DECL_KEY, "def_for_key(NO_DECL_KEY)");
        if key == NO_DECL_KEY {
            return NO_DEF;
        }
        let existing = self.defs.def_of(key);
        if existing != NO_DEF {
            return existing;
        }
        let def = self.sigs.push(SigKind::Absent);
        self.defs.bind(def, key);
        debug_assert_eq!(self.defs.defs(), self.sigs.len());
        def
    }

    /// [`Fir::def_for_key`], then sets the row's kind.
    pub fn declare(&mut self, key: DeclKeyId, kind: SigKind) -> DefId {
        let def = self.def_for_key(key);
        self.sigs.set_kind(def, kind);
        def
    }

    /// Computes and stores `SigStore.sig_hash` for `def` (§5.4). Derived, so it
    /// is written after lowering and never read as an input.
    pub fn refresh_sig_hash(&mut self, names: &fors_index::interner::Interner, def: DefId) -> u128 {
        let mut scratch = EncodeScratch::default();
        self.refresh_sig_hash_with(names, def, &mut scratch)
    }

    /// [`Fir::refresh_sig_hash`] with a reusable encoding buffer: what the
    /// freeze phase uses, since it hashes every declaration in the build.
    pub fn refresh_sig_hash_with(
        &mut self,
        names: &fors_index::interner::Interner,
        def: DefId,
        scratch: &mut EncodeScratch,
    ) -> u128 {
        let h = sig_hash_with(self, names, def, scratch);
        self.sigs.set_sig_hash(def, h);
        h
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_index::decl::DeclKind;
    use fors_index::interner::Interner;

    #[test]
    fn def_for_key_keeps_the_two_tables_aligned() {
        let mut names = Interner::new();
        let mut fir = Fir::new();
        let m = {
            let s = names.intern(b"m");
            fir.keys.paths.intern(&[s])
        };
        let name = names.intern(b"S");
        let k = fir.keys.intern(DeclKey {
            parent: NO_DECL_KEY,
            module: m,
            kind: DeclKind::Struct,
            name: Some(name),
            disamb: 0,
        });
        let a = fir.def_for_key(k);
        let b = fir.def_for_key(k);
        assert_eq!(a, b);
        assert_eq!(fir.sigs.kind(a), SigKind::Absent);
        let c = fir.declare(k, SigKind::Struct);
        assert_eq!(c, a);
        assert_eq!(fir.sigs.kind(a), SigKind::Struct);
        assert_eq!(fir.defs.defs(), fir.sigs.len());
    }
}
