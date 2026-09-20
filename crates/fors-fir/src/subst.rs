//! Substitution and the one-way match (design §4.1, `subst.rs`; spec ch09
//! Definitions and R38).
//!
//! `one_way_match(P, A)` walks `P` and `A` in lockstep. An unbound parameter of
//! one of the binding's owners, met in `P`, binds to the facing subterm of `A`;
//! a bound parameter or any constructor must equal it (R9); a subterm of `P`
//! that is a projection on a still-unbound parameter faces anything, binds
//! nothing and is not compared (R38(e) compares it later); nothing in `A` is
//! ever bound. Cost is linear in the size of `P`.
//!
//! `subst_norm` replaces bound parameters and re-interns. Its first act is one
//! load of the flags byte: a monomorphic type is returned unchanged without
//! touching a memo, a pool or the heap.

use std::collections::HashMap;

use fors_index::fingerprint::splitmix64;
use fors_index::ids::DefId;

use crate::ty::{
    ArgsId, BrandId, BrandRow, ConstId, FnTyId, NO_TY, ProjKeyId, TraitRefId, TyId, TyStore, TyTag,
};

/// One owner's slice of the slot vector.
#[derive(Clone, Copy, Debug)]
struct OwnerSlots {
    owner: DefId,
    start: u32,
    len: u16,
}

/// The parameter bindings of one call or one impl selection. Design §7.6 builds
/// a `Binding{owners: [imp]}` per bucket candidate; a generic call (R38) builds
/// one whose owners are the impl or trait reached and then the function itself.
#[derive(Clone, Debug, Default)]
pub struct Binding {
    owners: Vec<OwnerSlots>,
    slots: Vec<TyId>,
}

impl Binding {
    /// `owners` is `(owner DefId, how many own generic parameters it has)`, in
    /// the order R38 visits them.
    pub fn new(owners: &[(DefId, u16)]) -> Binding {
        let mut b = Binding::default();
        for &(owner, len) in owners {
            b.owners.push(OwnerSlots {
                owner,
                start: b.slots.len() as u32,
                len,
            });
            b.slots.resize(b.slots.len() + len as usize, NO_TY);
        }
        b
    }

    pub fn owns(&self, owner: DefId) -> bool {
        self.owners.iter().any(|o| o.owner == owner)
    }

    fn at(&self, owner: DefId, ordinal: u16) -> Option<usize> {
        let o = self.owners.iter().find(|o| o.owner == owner)?;
        if ordinal >= o.len {
            return None;
        }
        Some(o.start as usize + ordinal as usize)
    }

    /// The bound type, or [`NO_TY`] when the slot is unbound or not ours.
    pub fn slot(&self, owner: DefId, ordinal: u16) -> TyId {
        match self.at(owner, ordinal) {
            Some(i) => self.slots[i],
            None => NO_TY,
        }
    }

    /// Binds a slot, or confirms it already holds `ty`. `false` means the slot
    /// is already bound to something else — R38's "a binding is never revised;
    /// a later disagreement is T0026 at that argument".
    pub fn bind(&mut self, owner: DefId, ordinal: u16, ty: TyId) -> bool {
        match self.at(owner, ordinal) {
            None => false,
            Some(i) => {
                if self.slots[i] == NO_TY {
                    self.slots[i] = ty;
                    true
                } else {
                    self.slots[i] == ty
                }
            }
        }
    }

    pub fn is_complete(&self) -> bool {
        self.slots.iter().all(|&s| s != NO_TY)
    }

    pub fn slots(&self) -> &[TyId] {
        &self.slots
    }

    pub fn owner_count(&self) -> usize {
        self.owners.len()
    }

    /// The substitution memo's key (see [`SubstMemo`]): the owners and the slot
    /// values, length-framed and folded through the workspace's SplitMix64
    /// mixer into two independently-salted 64-bit lanes.
    // MARC (verification round): this used to build a `Vec<u8>` and call
    // `hash_bytes` on it — a heap allocation on every memoised substitution,
    // which is the hot path §7.5 exists to keep cheap. The fold below is the
    // same mixer `ConsTable::key_slice` uses for every pool, applied twice with
    // different salts so the key keeps its 128 bits; nothing about the answer
    // depends on allocation size, address or iteration order.
    pub fn key(&self) -> BindingKey {
        BindingKey(((self.fold(KEY_SALT_HI) as u128) << 64) | self.fold(KEY_SALT_LO) as u128)
    }

    fn fold(&self, salt: u64) -> u64 {
        let mut h = splitmix64(salt ^ self.owners.len() as u64);
        for o in &self.owners {
            h = splitmix64(h ^ o.owner.0 as u64);
            h = splitmix64(h ^ o.len as u64);
        }
        h = splitmix64(h ^ self.slots.len() as u64);
        for s in &self.slots {
            h = splitmix64(h ^ s.0 as u64);
        }
        h
    }
}

const KEY_SALT_LO: u64 = 0x4249_4e44_4b45_594c; // "BINDKEYL"
const KEY_SALT_HI: u64 = 0x4249_4e44_4b45_5948; // "BINDKEYH"

/// A binding's content identity.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BindingKey(pub u128);

// MARC: the memo key is `(TyId, BindingKey)`, NOT the `(TyId, TraitRefId)` the
// design writes in §7.5/§4.1. `spikes/fir-normalise` demonstrates that the
// written key returns a WRONG ANSWER: with `impl Iter[C] for Vec[T] { type Item
// = T; }`, normalising `Vec[i32].Item` and then `Vec[u8].Item` presents the
// same right-hand side (`Param(impl, 0)`) under the same `TraitRefId`
// (`Iter[C]`), so the second query is answered `i32`. `impl_lookup` binds slots
// from the self type as well as from the trait arguments, so the BINDING — not
// the trait reference — is what determines the result. The spike shows the
// corrected key keeps every counter linear in chain depth and independent of
// the number of impls per head, i.e. the fix costs nothing. `BindingKey` is a
// 128-bit content hash rather than an interned id for the same reason
// `SigStore.sig_hash` is (§14 Q2): one hash function for the whole compiler.
#[derive(Default)]
pub struct SubstMemo {
    map: HashMap<(TyId, BindingKey), TyId>,
}

impl SubstMemo {
    pub fn new() -> SubstMemo {
        SubstMemo::default()
    }

    pub fn get(&self, ty: TyId, key: BindingKey) -> Option<TyId> {
        self.map.get(&(ty, key)).copied()
    }

    pub fn insert(&mut self, ty: TyId, key: BindingKey, out: TyId) {
        self.map.insert((ty, key), out);
    }

    /// An impl edit bumps `TraitWorldRevision` and clears this wholesale (§9.1).
    pub fn clear(&mut self) {
        self.map.clear();
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// How a projection whose head stopped being rigid is resolved. R20's
/// `normalise_proj` (I6, needing the impl index) plugs in here; I1 has no impl
/// index, so [`NeutralOnly`] is the only implementation in this increment.
pub trait ProjSolver {
    fn solve(&mut self, store: &mut TyStore, head: TyId, key: ProjKeyId) -> Option<TyId>;
}

/// Refuses to reduce a projection on a concrete head. `subst_norm` then returns
/// `None`, which its callers read as "this needs normalisation I cannot do".
pub struct NeutralOnly;

impl ProjSolver for NeutralOnly {
    fn solve(&mut self, _store: &mut TyStore, _head: TyId, _key: ProjKeyId) -> Option<TyId> {
        None
    }
}

/// `subst_norm` with no projection solver (see [`NeutralOnly`]).
pub fn subst_norm(store: &mut TyStore, ty: TyId, b: &Binding) -> Option<TyId> {
    subst_norm_with(store, ty, b, &mut NeutralOnly)
}

pub fn subst_norm_with(
    store: &mut TyStore,
    ty: TyId,
    b: &Binding,
    solver: &mut dyn ProjSolver,
) -> Option<TyId> {
    // The one load the flags byte exists for.
    if store.is_monomorphic(ty) {
        return Some(ty);
    }
    let q = store.quals(ty);
    let base = store.unqual(ty);
    let out = subst_core(store, base, b, solver)?;
    if q.is_none() {
        return Some(out);
    }
    // MARC: a QUALIFIED position takes only an UNQUALIFIED argument. Two
    // reasons, and the second is the one that made this a rule rather than a
    // preference. First, `iso T` with `T := imm Buf` would be `iso imm Buf`,
    // which is not a type at all. Second, qualifier union is idempotent, so
    // `iso T` with `T := iso Buf` substitutes to `iso Buf` — and then nothing
    // can recover `T` from the result: `one_way_match` would bind `T := Buf`,
    // and a signature naming `T` twice, once bare and once qualified, would
    // disagree with itself. Requiring the argument to be unqualified makes
    // substitution injective on qualifiers, which is what makes the match its
    // inverse (`one_way_match_properties` checks exactly that over generated
    // types). ch01 owns qualifier compatibility and I5 reports it at the
    // argument; here it is reported the only way this crate reports anything,
    // as a substitution that could not be completed.
    if !store.quals(out).is_none() {
        return None;
    }
    Some(store.qualified(out, q))
}

/// As [`subst_norm_with`], memoised on `(ty, binding)` — the key the spike
/// corrected. Same answer, fewer walks.
pub fn subst_norm_cached(
    store: &mut TyStore,
    ty: TyId,
    b: &Binding,
    solver: &mut dyn ProjSolver,
    memo: &mut SubstMemo,
) -> Option<TyId> {
    if store.is_monomorphic(ty) {
        return Some(ty);
    }
    let key = b.key();
    if let Some(hit) = memo.get(ty, key) {
        return Some(hit);
    }
    let out = subst_norm_with(store, ty, b, solver)?;
    memo.insert(ty, key, out);
    Some(out)
}

fn subst_core(
    store: &mut TyStore,
    ty: TyId,
    b: &Binding,
    solver: &mut dyn ProjSolver,
) -> Option<TyId> {
    let tag = store.tag(ty);
    let a = store.a(ty);
    let bb = store.b(ty);
    match tag {
        TyTag::Param => {
            let owner = DefId(a);
            if !b.owns(owner) {
                return Some(ty); // a rigid parameter of an enclosing declaration
            }
            let v = b.slot(owner, bb as u16);
            if v == NO_TY { None } else { Some(v) }
        }
        TyTag::Brand => match store.brand(BrandId(bb)) {
            // R40: a brand parameter is bound by identity, like any other slot.
            BrandRow::Param { owner, ordinal } if b.owns(owner) => {
                let v = b.slot(owner, ordinal);
                if v == NO_TY { None } else { Some(v) }
            }
            _ => Some(ty),
        },
        TyTag::Nominal => {
            let xs = subst_args(store, ArgsId(bb), b, solver)?;
            Some(store.nominal_of(DefId(a), &xs))
        }
        TyTag::Tuple => {
            let xs = subst_args(store, ArgsId(bb), b, solver)?;
            Some(store.tuple_of(&xs))
        }
        TyTag::Dyn => {
            let (trait_def, args) = store.trait_ref(TraitRefId(a));
            let xs = subst_args(store, args, b, solver)?;
            let id = store.intern_args(&xs);
            let tr = store.intern_trait_ref(trait_def, id);
            Some(store.dyn_ty(tr))
        }
        TyTag::Fn => {
            let id = FnTyId(a);
            let (convs, tys) = {
                let (c, t) = store.fn_tys().params(id);
                (c.to_vec(), t.to_vec())
            };
            let result = store.fn_tys().result(id);
            let raises = store.fn_tys().raises(id);
            let closure = store.fn_tys().is_closure(id);
            let mut params = Vec::with_capacity(tys.len());
            for (i, t) in tys.into_iter().enumerate() {
                params.push((convs[i], subst_norm_with(store, t, b, solver)?));
            }
            let result = subst_norm_with(store, result, b, solver)?;
            // R7: an absent `raises` is not `raises E` for any E, and stays absent.
            let raises = if raises == NO_TY {
                NO_TY
            } else {
                subst_norm_with(store, raises, b, solver)?
            };
            let f = store.intern_fn_ty(&params, result, raises, closure);
            Some(store.fn_ty(f))
        }
        TyTag::Proj => {
            let (tr, name) = store.proj_key(ProjKeyId(bb));
            let (trait_def, targs) = store.trait_ref(tr);
            let xs = subst_args(store, targs, b, solver)?;
            let id = store.intern_args(&xs);
            let tr2 = store.intern_trait_ref(trait_def, id);
            let key = store.intern_proj_key(tr2, name);
            let head = subst_norm_with(store, TyId(a), b, solver)?;
            if store.is_rigid(head) {
                // Still neutral: equal only to the same (head, trait+args, name).
                Some(store.proj(head, key))
            } else {
                solver.solve(store, head, key)
            }
        }
        TyTag::ConstVal => {
            let t = subst_norm_with(store, TyId(bb), b, solver)?;
            let v = store.const_value(ConstId(a));
            Some(store.const_ty(v, t))
        }
        _ => Some(ty),
    }
}

fn subst_args(
    store: &mut TyStore,
    args: ArgsId,
    b: &Binding,
    solver: &mut dyn ProjSolver,
) -> Option<Vec<TyId>> {
    let mut xs = store.args_vec(args);
    for x in xs.iter_mut() {
        *x = subst_norm_with(store, *x, b, solver)?;
    }
    Some(xs)
}

/// ch09 Definitions' one-way match. `pattern` may mention unbound parameters of
/// `b`'s owners; `target` is complete. A projection in `pattern` whose head is
/// already bound is resolved with [`NeutralOnly`] (see [`one_way_match_with`]).
pub fn one_way_match(store: &mut TyStore, pattern: TyId, target: TyId, b: &mut Binding) -> bool {
    one_way_match_with(store, pattern, target, b, &mut NeutralOnly)
}

/// [`one_way_match`] with the projection solver the caller has (I6's
/// `normalise_proj`): a projection in `pattern` whose head is bound is
/// substituted and normalised through `solver`, then compared (design §7.4).
// MARC (verification round): the previous code returned `false` for every
// projection whose head was bound, on the theory that "a bound projection is
// neutral, so equality was the whole test". That is wrong as soon as the head
// is bound to something other than itself: `fn f[I: Iterator](let it: I, let
// x: I.Item)` called with `it := U` (the caller's own rigid parameter) makes
// the second parameter `U.Item`, which is the target exactly — but the pattern
// row is `I.Item`, a different id, so the old code rejected every such call.
// The design's §7.4 says: head bound => subst_norm, then compare. With I1's
// `NeutralOnly` solver a projection on a concrete head cannot yet be reduced,
// and the match answers `false`; R38(e) re-compares it after the call's
// binding is complete, so nothing is decided wrongly, only later.
//
// R33's "an argument of type `never` binds nothing" is NOT applied here
// although §7.4's pseudo-code lists it: it is a property of a call ARGUMENT,
// not of a `never` nested inside a type argument (`Vec[never].Item` must bind
// `T := never` in `impl_lookup` or it has no impl). It belongs in `call.rs`
// under the `mode` the design gives step (c), on the top-level argument only.
pub fn one_way_match_with(
    store: &mut TyStore,
    pattern: TyId,
    target: TyId,
    b: &mut Binding,
    solver: &mut dyn ProjSolver,
) -> bool {
    // Hash-consing: the common case is one integer comparison.
    if pattern == target {
        return true;
    }
    // Nothing to bind and not equal: nothing to do. One byte load (§7.4's fast
    // path; a Brand parameter carries F_BRAND, a projection F_PROJ).
    if store.flags(pattern) & crate::ty::F_OPEN == 0 {
        return false;
    }
    let tag = store.tag(pattern);
    let a = store.a(pattern);
    let bb = store.b(pattern);
    let pq = store.quals(pattern);
    let aq = store.quals(target);

    if tag == TyTag::Proj {
        // R38: a projection on a still-unbound parameter faces anything —
        // any type, any qualifiers — binds nothing and is not compared; the
        // call's step (e) compares it once the binding is complete. That is
        // decided BEFORE the qualifier test below, or `T.Item` would reject
        // an `iso Buf` it has not looked at yet.
        if proj_head_unbound(store, pattern, b) {
            return true;
        }
        // Head bound: the projection is a type now. Substitute (and normalise,
        // if the solver can) and compare the result, which is the only test a
        // neutral or concrete type admits.
        return match subst_norm_with(store, pattern, b, solver) {
            Some(t) => t == target,
            None => false,
        };
    }

    if tag == TyTag::Param {
        let owner = DefId(a);
        if !b.owns(owner) {
            return false; // rigid: equality was already tested
        }
        // A bare position takes the target whole, qualifiers included
        // (`fn f[T](let x: T)` accepts an `iso Buf`). A qualified position
        // states those qualifiers itself, so the target must carry exactly
        // them and the parameter binds what is underneath — see the note in
        // `subst_norm_with` for why this is exact equality and not a subset
        // test. This is the inverse of substitution, which is the property
        // R38 needs: match, then substitute, gets the target back.
        let value = if pq.is_none() {
            target
        } else {
            if pq != aq {
                return false;
            }
            store.unqual(target)
        };
        return b.bind(owner, bb as u16, value);
    }

    // R9: everything else must agree on qualifiers exactly.
    if pq != aq {
        return false;
    }

    match tag {
        TyTag::Brand => match store.brand(BrandId(bb)) {
            // R40: bound by identity, and only from a receiver or argument.
            BrandRow::Param { owner, ordinal } if b.owns(owner) => b.bind(owner, ordinal, target),
            _ => false,
        },
        TyTag::Nominal => {
            if store.tag(target) != TyTag::Nominal || store.a(target) != a {
                return false;
            }
            match_args(store, ArgsId(bb), ArgsId(store.b(target)), b, solver)
        }
        TyTag::Tuple => {
            if store.tag(target) != TyTag::Tuple {
                return false;
            }
            match_args(store, ArgsId(bb), ArgsId(store.b(target)), b, solver)
        }
        TyTag::Dyn => {
            if store.tag(target) != TyTag::Dyn {
                return false;
            }
            let (pd, pa) = store.trait_ref(TraitRefId(a));
            let (td, ta) = store.trait_ref(TraitRefId(store.a(target)));
            pd == td && match_args(store, pa, ta, b, solver)
        }
        TyTag::Fn => {
            if store.tag(target) != TyTag::Fn {
                return false;
            }
            let p = FnTyId(a);
            let t = FnTyId(store.a(target));
            // R7: a closure type equals no `fn` type. Matching is equality, so
            // the bit is part of it; R10(b)'s coercion is the caller's step.
            if store.fn_tys().is_closure(p) != store.fn_tys().is_closure(t) {
                return false;
            }
            // R7's equality is pairwise on conventions as well as types. The
            // slices are re-borrowed per parameter rather than copied out: a
            // function type is one node and gets no allocation of its own.
            let n = store.fn_tys().params(p).0.len();
            if store.fn_tys().params(t).0.len() != n {
                return false;
            }
            for i in 0..n {
                let (pc, pt) = {
                    let (c, x) = store.fn_tys().params(p);
                    (c[i], x[i])
                };
                let (tc, tt) = {
                    let (c, x) = store.fn_tys().params(t);
                    (c[i], x[i])
                };
                if pc != tc || !one_way_match_with(store, pt, tt, b, solver) {
                    return false;
                }
            }
            let (pr, tr) = (store.fn_tys().result(p), store.fn_tys().result(t));
            if !one_way_match_with(store, pr, tr, b, solver) {
                return false;
            }
            let (pe, te) = (store.fn_tys().raises(p), store.fn_tys().raises(t));
            match (pe == NO_TY, te == NO_TY) {
                (true, true) => true,
                (false, false) => one_way_match_with(store, pe, te, b, solver),
                // R7: absent is distinct from every `raises E`.
                _ => false,
            }
        }
        TyTag::ConstVal => {
            // `[T; N]`-shaped positions: the value must agree and the type
            // position is matched like any other.
            if store.tag(target) != TyTag::ConstVal || store.a(target) != a {
                return false;
            }
            one_way_match_with(store, TyId(bb), TyId(store.b(target)), b, solver)
        }
        // A primitive, unit, never, an error or a rigid parameter: equality
        // was the whole test, and it already failed.
        _ => false,
    }
}

fn match_args(
    store: &mut TyStore,
    p: ArgsId,
    t: ArgsId,
    b: &mut Binding,
    solver: &mut dyn ProjSolver,
) -> bool {
    let n = store.args(p).len();
    if store.args(t).len() != n {
        return false;
    }
    for i in 0..n {
        let (pi, ti) = (store.args(p)[i], store.args(t)[i]);
        if !one_way_match_with(store, pi, ti, b, solver) {
            return false;
        }
    }
    true
}

/// Whether `p` (a `Proj` row) bottoms out in a parameter of `b` that is still
/// unbound. Walks the head chain, which is `Param` or `Proj` all the way down by
/// the store's invariant.
fn proj_head_unbound(store: &TyStore, p: TyId, b: &Binding) -> bool {
    let mut cur = p;
    loop {
        match store.tag(cur) {
            TyTag::Proj => cur = TyId(store.a(cur)),
            TyTag::Param => {
                let owner = DefId(store.a(cur));
                return b.owns(owner) && b.slot(owner, store.b(cur) as u16) == NO_TY;
            }
            _ => return false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::{PrimKind, Quals, TY_UNIT};
    use fors_index::interner::Symbol;

    const IMPL: DefId = DefId(100);

    fn store_and_binding() -> (TyStore, Binding) {
        (TyStore::new(), Binding::new(&[(IMPL, 2)]))
    }

    #[test]
    fn a_slot_binds_once_and_must_agree_after() {
        let (mut s, mut b) = store_and_binding();
        let p = s.param(IMPL, 0);
        let i32_ty = s.prim(PrimKind::I32);
        let u8_ty = s.prim(PrimKind::U8);
        assert!(one_way_match(&mut s, p, i32_ty, &mut b));
        assert_eq!(b.slot(IMPL, 0), i32_ty);
        assert!(one_way_match(&mut s, p, i32_ty, &mut b));
        assert!(!one_way_match(&mut s, p, u8_ty, &mut b));
    }

    #[test]
    fn success_implies_substitution_reproduces_the_target() {
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let t1 = s.param(IMPL, 1);
        let pattern = s.nominal_of(DefId(7), &[t0, t1]);
        let i32_ty = s.prim(PrimKind::I32);
        let str_ty = s.prim(PrimKind::Str);
        let target = s.nominal_of(DefId(7), &[i32_ty, str_ty]);
        assert!(one_way_match(&mut s, pattern, target, &mut b));
        assert!(b.is_complete());
        assert_eq!(subst_norm(&mut s, pattern, &b), Some(target));
    }

    #[test]
    fn a_projection_on_an_unbound_parameter_faces_anything() {
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let name = Symbol(0);
        let proj = s.proj_of(t0, DefId(9), &[], name);
        let i32_ty = s.prim(PrimKind::I32);
        // Skipped, binds nothing (R38(e) compares it later).
        assert!(one_way_match(&mut s, proj, i32_ty, &mut b));
        assert_eq!(b.slot(IMPL, 0), NO_TY);
        // Once the head is bound the projection is a neutral type and only
        // equality will do.
        assert!(one_way_match(&mut s, t0, i32_ty, &mut b));
        assert!(!one_way_match(&mut s, proj, i32_ty, &mut b));
    }

    #[test]
    fn a_projection_on_a_bound_parameter_is_substituted_then_compared() {
        // `fn f[I: Iterator](let it: I, let x: I.Item)` called from inside
        // `fn g[U: Iterator](let u: U)` as `f(u, u.next())`: the first argument
        // binds `I := U`, so the second parameter IS `U.Item` — a different
        // row from the pattern `I.Item`, equal only after substitution.
        let (mut s, mut b) = store_and_binding();
        let i = s.param(IMPL, 0);
        let u = s.param(DefId(200), 0);
        let name = Symbol(0);
        let pat = s.proj_of(i, DefId(9), &[], name);
        let want = s.proj_of(u, DefId(9), &[], name);
        assert!(one_way_match(&mut s, i, u, &mut b));
        assert!(
            one_way_match(&mut s, pat, want, &mut b),
            "I.Item with I := U must match U.Item"
        );
        let other = s.proj_of(u, DefId(9), &[], Symbol(1));
        assert!(
            !one_way_match(&mut s, pat, other, &mut b),
            "...and only U.Item"
        );

        // A projection whose head is bound to a CONCRETE type needs the impl
        // index to reduce; I1's solver cannot, so the answer is `false` and
        // R38(e) compares it after normalisation. It must not bind anything.
        let mut b2 = Binding::new(&[(IMPL, 2)]);
        let i32_ty = s.prim(PrimKind::I32);
        assert!(one_way_match(&mut s, i, i32_ty, &mut b2));
        assert!(!one_way_match(&mut s, pat, i32_ty, &mut b2));
        assert_eq!(b2.slot(IMPL, 1), NO_TY);
    }

    #[test]
    fn an_unbound_projection_faces_a_qualified_target_too() {
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let proj = s.proj_of(t0, DefId(9), &[], Symbol(0));
        let buf = s.nominal_of(DefId(4), &[]);
        let iso_buf = s.qualified(buf, Quals::ISO);
        assert!(one_way_match(&mut s, proj, iso_buf, &mut b));
        assert_eq!(b.slot(IMPL, 0), NO_TY, "a skipped projection binds nothing");
    }

    #[test]
    fn monomorphic_substitution_is_the_identity() {
        let (mut s, b) = store_and_binding();
        let i32_ty = s.prim(PrimKind::I32);
        let mono = s.nominal_of(DefId(3), &[i32_ty]);
        let before = s.len();
        assert_eq!(subst_norm(&mut s, mono, &b), Some(mono));
        assert_eq!(subst_norm(&mut s, TY_UNIT, &b), Some(TY_UNIT));
        assert_eq!(
            s.len(),
            before,
            "substituting a monomorphic type interned nothing"
        );
    }

    #[test]
    fn an_unbound_slot_makes_substitution_fail() {
        let (mut s, b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let open = s.nominal_of(DefId(3), &[t0]);
        assert_eq!(subst_norm(&mut s, open, &b), None);
    }

    #[test]
    fn a_qualified_position_wants_exactly_its_qualifiers() {
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let iso_t0 = s.qualified(t0, Quals::ISO);
        let buf = s.nominal_of(DefId(4), &[]);
        let iso_buf = s.qualified(buf, Quals::ISO);
        let iso_secret_buf = s.qualified(iso_buf, Quals::SECRET);

        // `iso T` against `iso Buf` binds `T := Buf` — and substituting it back
        // reproduces the target, which is the property that matters.
        assert!(one_way_match(&mut s, iso_t0, iso_buf, &mut b));
        assert_eq!(b.slot(IMPL, 0), buf);
        assert_eq!(subst_norm(&mut s, iso_t0, &b), Some(iso_buf));

        // `iso T` does NOT match `iso secret Buf`: that type comes from the
        // position `iso secret T`, not from this one.
        let mut b2 = Binding::new(&[(IMPL, 2)]);
        assert!(!one_way_match(&mut s, iso_t0, iso_secret_buf, &mut b2));
    }

    #[test]
    fn a_bare_position_takes_the_qualifiers_with_it() {
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let buf = s.nominal_of(DefId(4), &[]);
        let iso_buf = s.qualified(buf, Quals::ISO);
        assert!(one_way_match(&mut s, t0, iso_buf, &mut b));
        assert_eq!(b.slot(IMPL, 0), iso_buf);
        assert_eq!(subst_norm(&mut s, t0, &b), Some(iso_buf));
    }

    #[test]
    fn a_qualified_position_refuses_an_already_qualified_argument() {
        // `iso T` with `T := imm Buf` is `iso imm Buf`, which is not a type;
        // `iso T` with `T := iso Buf` is `iso Buf`, from which `T` could never
        // be recovered. Both are "no substitution".
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let iso_t0 = s.qualified(t0, Quals::ISO);
        let buf = s.nominal_of(DefId(4), &[]);
        let imm_buf = s.qualified(buf, Quals::IMM);
        assert!(b.bind(IMPL, 0, imm_buf));
        assert_eq!(subst_norm(&mut s, iso_t0, &b), None);

        let mut b2 = Binding::new(&[(IMPL, 2)]);
        let iso_buf = s.qualified(buf, Quals::ISO);
        assert!(b2.bind(IMPL, 0, iso_buf));
        assert_eq!(subst_norm(&mut s, iso_t0, &b2), None);
    }

    #[test]
    fn the_memo_key_separates_two_bindings_the_trait_ref_cannot() {
        // The spike's witness, at the level of the key itself: one owner, one
        // trait ref, two different slot values.
        let mut s = TyStore::new();
        let i32_ty = s.prim(PrimKind::I32);
        let u8_ty = s.prim(PrimKind::U8);
        let mut b1 = Binding::new(&[(IMPL, 1)]);
        let mut b2 = Binding::new(&[(IMPL, 1)]);
        b1.bind(IMPL, 0, i32_ty);
        b2.bind(IMPL, 0, u8_ty);
        assert_ne!(b1.key(), b2.key());

        let rhs = s.param(IMPL, 0);
        let mut memo = SubstMemo::new();
        assert_eq!(
            subst_norm_cached(&mut s, rhs, &b1, &mut NeutralOnly, &mut memo),
            Some(i32_ty)
        );
        assert_eq!(
            subst_norm_cached(&mut s, rhs, &b2, &mut NeutralOnly, &mut memo),
            Some(u8_ty)
        );
        assert_eq!(memo.len(), 2);
    }

    #[test]
    fn function_types_match_pairwise_on_conventions_and_raises() {
        use crate::sig::Conv;
        let (mut s, mut b) = store_and_binding();
        let t0 = s.param(IMPL, 0);
        let i32_ty = s.prim(PrimKind::I32);
        let pf = s.intern_fn_ty(&[(Conv::Let, t0)], TY_UNIT, NO_TY, false);
        let p = s.fn_ty(pf);
        let tf = s.intern_fn_ty(&[(Conv::Let, i32_ty)], TY_UNIT, NO_TY, false);
        let t = s.fn_ty(tf);
        assert!(one_way_match(&mut s, p, t, &mut b));
        assert_eq!(b.slot(IMPL, 0), i32_ty);

        // A different convention is a different type (R7).
        let mut b2 = Binding::new(&[(IMPL, 2)]);
        let wf = s.intern_fn_ty(&[(Conv::Inout, i32_ty)], TY_UNIT, NO_TY, false);
        let w = s.fn_ty(wf);
        assert!(!one_way_match(&mut s, p, w, &mut b2));

        // And `raises E` is distinct from absent (R7).
        let mut b3 = Binding::new(&[(IMPL, 2)]);
        let rf = s.intern_fn_ty(&[(Conv::Let, i32_ty)], TY_UNIT, i32_ty, false);
        let r = s.fn_ty(rf);
        assert!(!one_way_match(&mut s, p, r, &mut b3));
    }
}
