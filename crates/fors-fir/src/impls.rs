//! `ImplIndex` (design §4.1, §5.2) and R19's overlap test.
//!
//! Three lookup paths over one sorted, struct-of-arrays row table:
//!
//! * `exact(trait, self_ty)` — the exact `(trait, self TyId)` probe §17
//!   amendment 3 requires. The spike's shape Z (k impls in one
//!   `(trait, HeadKey)` bucket, distinguished only deep in the self type)
//!   costs k²/2 match steps per query without it; with it every impl whose
//!   self type is written out in full is one binary search.
//! * `bucket(trait, head)` — the generic heads that the exact probe cannot
//!   answer, already narrowed to one trait and one head (ch08 R21 bounds a
//!   bucket's source modules to two).
//! * `inherent(head)` — the inherent impls of a head, for member lookup and
//!   R48's clash test.

use fors_index::ids::DefId;

use crate::defpath::{HeadKey, NO_DEF};
use crate::sig::{GParamKind, SigStore};
use crate::ty::{ArgsId, TyId, TyStore, TyTag, NO_ARGS, NO_TY};

/// One impl as the index stores it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ImplRow {
    /// The impl declaration's own `DefId`.
    pub def: DefId,
    /// The trait it implements, or [`NO_DEF`] when it is inherent OR when the
    /// written trait did not resolve — `inherent` is what tells the two
    /// apart, and nothing may read `trait_def == NO_DEF` as "inherent" on its
    /// own (package `std` writes `impl io.Writer for File` in a build whose
    /// `std` is not itself a module, which the resolver defers).
    pub trait_def: DefId,
    /// Written without `for`.
    pub inherent: bool,
    /// The trait's arguments (`As` in `impl Tr[As] for S`), `Self` excluded.
    pub trait_args: ArgsId,
    /// The self type `S`, with `Self` already replaced (R8).
    pub self_ty: TyId,
    /// `self_ty`'s head, the bucket's second column.
    pub head: HeadKey,
    /// Source order within the build: `(module bytes rank, declaration
    /// index)`, already flattened by the builder. R19 reports at the LATER
    /// impl, which is the one with the greater `order`.
    pub order: u32,
}

/// The sorted impl table (design §4.1 `impls.rs`).
#[derive(Default)]
pub struct ImplIndex {
    rows: Vec<ImplRow>,
    /// `(trait_def, head, row)` sorted — the bucket scan.
    by_head: Vec<(u32, u64, u32)>,
    /// `(trait_def, self_ty, row)` sorted — §17 amendment 3's exact probe.
    by_self: Vec<(u32, u32, u32)>,
}

impl ImplIndex {
    pub fn new() -> ImplIndex {
        ImplIndex::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn row(&self, i: u32) -> ImplRow {
        self.rows[i as usize]
    }

    pub fn rows(&self) -> &[ImplRow] {
        &self.rows
    }

    /// Appends one impl. Call [`Self::finish`] once every impl is in.
    pub fn push(&mut self, row: ImplRow) -> u32 {
        let i = self.rows.len() as u32;
        self.by_head.push((row.trait_def.0, row.head.as_u64(), i));
        self.by_self.push((row.trait_def.0, row.self_ty.0, i));
        self.rows.push(row);
        i
    }

    /// Sorts both indexes. Idempotent.
    pub fn finish(&mut self) {
        self.by_head.sort_unstable();
        self.by_self.sort_unstable();
    }

    /// Every impl of `trait_def` whose self type's head is `head`, in index
    /// order. `trait_def` is [`NO_DEF`] for the inherent impls.
    pub fn bucket(&self, trait_def: DefId, head: HeadKey) -> Vec<u32> {
        let k = (trait_def.0, head.as_u64());
        let lo = self.by_head.partition_point(|&(t, h, _)| (t, h) < k);
        let hi = lo + self.by_head[lo..].partition_point(|&(t, h, _)| (t, h) == k);
        self.by_head[lo..hi].iter().map(|&(_, _, r)| r).collect()
    }

    /// The impls of `trait_def` whose self type is EXACTLY `self_ty` (§17
    /// amendment 3). At most one, by R19 — more than one is exactly what R19
    /// rejects, so the builder uses this same probe to find the clash.
    pub fn exact(&self, trait_def: DefId, self_ty: TyId) -> Vec<u32> {
        let k = (trait_def.0, self_ty.0);
        let lo = self.by_self.partition_point(|&(t, s, _)| (t, s) < k);
        let hi = lo + self.by_self[lo..].partition_point(|&(t, s, _)| (t, s) == k);
        self.by_self[lo..hi].iter().map(|&(_, _, r)| r).collect()
    }

    /// The inherent impls of `head`.
    pub fn inherent(&self, head: HeadKey) -> Vec<u32> {
        self.bucket(NO_DEF, head)
    }
}

/// Whether `t` is a generic parameter of `owner` — a variable, for R19's
/// first-order unification.
fn is_var(tys: &TyStore, t: TyId, owners: &[DefId]) -> Option<(DefId, u16)> {
    if tys.tag(t) != TyTag::Param && tys.tag(t) != TyTag::Brand {
        return None;
    }
    match tys.tag(t) {
        TyTag::Param => {
            let owner = DefId(tys.a(t));
            owners.contains(&owner).then(|| (owner, tys.b(t) as u16))
        }
        // A brand parameter of the impl is a variable too (R19 renames every
        // generic parameter apart, whatever its kind).
        TyTag::Brand => match tys.brand(crate::ty::BrandId(tys.b(t))) {
            crate::ty::BrandRow::Param { owner, ordinal } => owners.contains(&owner).then_some((owner, ordinal)),
            crate::ty::BrandRow::Fresh { .. } => None,
        },
        _ => None,
    }
}

/// A first-order substitution over the two impls' parameters.
#[derive(Default)]
struct Unifier {
    slots: Vec<((u32, u16), TyId)>,
}

impl Unifier {
    fn get(&self, k: (u32, u16)) -> Option<TyId> {
        self.slots.iter().find(|&&(s, _)| s == k).map(|&(_, t)| t)
    }
    fn set(&mut self, k: (u32, u16), t: TyId) {
        self.slots.push((k, t));
    }
}

/// R19's first-order unification with an occurs check. Bounds are ignored,
/// associated types are never read.
fn unify(tys: &TyStore, a: TyId, b: TyId, owners: &[DefId], u: &mut Unifier, fuel: &mut u32) -> bool {
    if *fuel == 0 {
        return false;
    }
    *fuel -= 1;
    if a == b {
        return true;
    }
    if let Some((o, i)) = is_var(tys, a, owners) {
        let k = (o.0, i);
        return match u.get(k) {
            Some(prev) => unify(tys, prev, b, owners, u, fuel),
            None => {
                if occurs(tys, k, b, owners, u, &mut 4096) {
                    return false;
                }
                u.set(k, b);
                true
            }
        };
    }
    if is_var(tys, b, owners).is_some() {
        return unify(tys, b, a, owners, u, fuel);
    }
    if tys.tag(a) != tys.tag(b) || tys.quals(a) != tys.quals(b) {
        return false;
    }
    match tys.tag(a) {
        TyTag::Nominal => {
            if tys.a(a) != tys.a(b) {
                return false;
            }
            unify_args(tys, ArgsId(tys.b(a)), ArgsId(tys.b(b)), owners, u, fuel)
        }
        TyTag::Tuple => unify_args(tys, ArgsId(tys.b(a)), ArgsId(tys.b(b)), owners, u, fuel),
        TyTag::Dyn => tys.a(a) == tys.a(b),
        // R18 forbids a projection in an impl head, and every other tag is a
        // ground constant whose `TyId` equality was already tested above.
        _ => false,
    }
}

fn unify_args(tys: &TyStore, a: ArgsId, b: ArgsId, owners: &[DefId], u: &mut Unifier, fuel: &mut u32) -> bool {
    let xs = tys.args_vec(a);
    let ys = tys.args_vec(b);
    if xs.len() != ys.len() {
        return false;
    }
    xs.iter().zip(ys.iter()).all(|(&x, &y)| unify(tys, x, y, owners, u, fuel))
}

fn occurs(tys: &TyStore, k: (u32, u16), t: TyId, owners: &[DefId], u: &Unifier, fuel: &mut u32) -> bool {
    if *fuel == 0 {
        return true;
    }
    *fuel -= 1;
    if let Some((o, i)) = is_var(tys, t, owners) {
        if (o.0, i) == k {
            return true;
        }
        return match u.get((o.0, i)) {
            Some(prev) => occurs(tys, k, prev, owners, u, fuel),
            None => false,
        };
    }
    match tys.tag(t) {
        TyTag::Nominal | TyTag::Tuple => {
            let args = if tys.tag(t) == TyTag::Nominal { ArgsId(tys.b(t)) } else { ArgsId(tys.b(t)) };
            tys.args_vec(args).iter().any(|&x| occurs(tys, k, x, owners, u, fuel))
        }
        _ => false,
    }
}

/// Whether two impls of the same trait overlap (R19): rename their parameters
/// apart (they already are — a `Param` row carries its owner `DefId`), treat
/// them as variables and unify `(trait arguments, self type)` first-order,
/// ignoring bounds. Associated types play no part.
pub fn overlap(tys: &TyStore, sigs: &SigStore, a: &ImplRow, b: &ImplRow) -> bool {
    if a.trait_def != b.trait_def || a.def == b.def {
        return false;
    }
    let owners = [a.def, b.def];
    // A const parameter is a variable for the unifier too; a brand parameter
    // already is (see `is_var`). Nothing else in an impl head can vary.
    let _ = sigs;
    let mut u = Unifier::default();
    let mut fuel = 1 << 16;
    if !unify(tys, a.self_ty, b.self_ty, &owners, &mut u, &mut fuel) {
        return false;
    }
    let xa = if a.trait_args == NO_ARGS { Vec::new() } else { tys.args_vec(a.trait_args) };
    let xb = if b.trait_args == NO_ARGS { Vec::new() } else { tys.args_vec(b.trait_args) };
    if xa.len() != xb.len() {
        return false;
    }
    xa.iter().zip(xb.iter()).all(|(&x, &y)| unify(tys, x, y, &owners, &mut u, &mut fuel))
}

/// Whether every generic parameter of `def` occurs in `head_tys` (R18's
/// "unconstrained impl parameter"): returns the ordinal of the first that does
/// not, or `None`.
pub fn first_unconstrained(tys: &mut TyStore, sigs: &SigStore, def: DefId, head_tys: &[TyId]) -> Option<u16> {
    let g = sigs.generics(def);
    let n = sigs.generics_store.count(g);
    for o in 0..n {
        let want = match sigs.generics_store.param(g, o).kind {
            GParamKind::Brand => tys.brand_ty(crate::ty::BrandRow::Param { owner: def, ordinal: o as u16 }),
            _ => tys.param(def, o as u16),
        };
        if !head_tys.iter().any(|&h| mentions(tys, h, want, &mut (1 << 16))) {
            return Some(o as u16);
        }
    }
    None
}

/// Whether `hay` mentions `needle` at any depth.
pub fn mentions(tys: &TyStore, hay: TyId, needle: TyId, fuel: &mut u32) -> bool {
    if *fuel == 0 {
        return false;
    }
    *fuel -= 1;
    if hay == needle || tys.unqual(hay) == needle {
        return true;
    }
    match tys.tag(hay) {
        TyTag::Nominal | TyTag::Tuple => tys.args_vec(ArgsId(tys.b(hay))).iter().any(|&x| mentions(tys, x, needle, fuel)),
        TyTag::Proj => mentions(tys, TyId(tys.a(hay)), needle, fuel),
        TyTag::Fn => {
            let id = crate::ty::FnTyId(tys.a(hay));
            let (_, ps) = tys.fn_tys().params(id);
            let ps: Vec<TyId> = ps.to_vec();
            let r = tys.fn_tys().result(id);
            let e = tys.fn_tys().raises(id);
            ps.iter().any(|&x| mentions(tys, x, needle, fuel))
                || mentions(tys, r, needle, fuel)
                || (e != NO_TY && mentions(tys, e, needle, fuel))
        }
        _ => false,
    }
}

/// Whether `t` contains a projection at any depth (R18: an impl head MUST NOT
/// contain one).
pub fn contains_proj(tys: &TyStore, t: TyId) -> bool {
    tys.flags(t) & crate::ty::F_PROJ != 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sig::SigKind;
    use crate::ty::PrimKind;
    use crate::Fir;
    use fors_index::decl::DeclKind;
    use fors_index::interner::Interner;

    /// A tiny build: one module, `n` declarations named `T0..`, plus the
    /// impls the test pushes.
    fn build(n: usize) -> (Fir, Interner, Vec<DefId>) {
        let mut names = Interner::new();
        let mut fir = Fir::new();
        let m = {
            let s = names.intern(b"m");
            fir.keys.paths.intern(&[s])
        };
        let mut defs = Vec::new();
        for i in 0..n {
            let nm = names.intern(format!("T{i}").as_bytes());
            let k = fir.keys.intern(crate::defpath::DeclKey {
                parent: crate::defpath::NO_DECL_KEY,
                module: m,
                kind: DeclKind::Struct,
                name: Some(nm),
                disamb: 0,
            });
            defs.push(fir.declare(k, SigKind::Struct));
        }
        (fir, names, defs)
    }

    fn row(def: DefId, trait_def: DefId, self_ty: TyId, head: HeadKey, order: u32) -> ImplRow {
        ImplRow { def, trait_def, inherent: trait_def == NO_DEF, trait_args: NO_ARGS, self_ty, head, order }
    }

    #[test]
    fn the_exact_probe_finds_a_concrete_impl_without_a_bucket_scan() {
        let (mut fir, _n, defs) = build(4);
        let tr = defs[0];
        let mut index = ImplIndex::new();
        // Four impls of one trait, all with head `Nominal(defs[1])`, told
        // apart only by their argument: §17 amendment 3's shape Z.
        let mut selves = Vec::new();
        for i in 0..4u32 {
            let arg = fir.tys.prim(match i {
                0 => PrimKind::I8,
                1 => PrimKind::I16,
                2 => PrimKind::I32,
                _ => PrimKind::I64,
            });
            let ty = fir.tys.nominal_of(defs[1], &[arg]);
            selves.push(ty);
            index.push(row(defs[2], tr, ty, fir.tys.head_key(ty), i));
        }
        index.finish();
        let head = fir.tys.head_key(selves[0]);
        assert_eq!(index.bucket(tr, head).len(), 4, "all four share one bucket");
        for s in &selves {
            assert_eq!(index.exact(tr, *s).len(), 1, "the exact probe answers in one step");
        }
    }

    #[test]
    fn overlap_unifies_a_generic_head_with_a_concrete_one() {
        let (mut fir, _n, defs) = build(4);
        let (tr, pair, a, b) = (defs[0], defs[1], defs[2], defs[3]);
        let t = fir.tys.param(a, 0);
        let generic = fir.tys.nominal_of(pair, &[t]);
        let i32ty = fir.tys.prim(PrimKind::I32);
        let concrete = fir.tys.nominal_of(pair, &[i32ty]);
        let x = row(a, tr, generic, fir.tys.head_key(generic), 0);
        let y = row(b, tr, concrete, fir.tys.head_key(concrete), 1);
        assert!(overlap(&fir.tys, &fir.sigs, &x, &y));
        assert!(overlap(&fir.tys, &fir.sigs, &y, &x), "overlap is symmetric");
    }

    #[test]
    fn overlap_is_false_for_two_concrete_heads_that_differ() {
        let (mut fir, _n, defs) = build(4);
        let (tr, pair, a, b) = (defs[0], defs[1], defs[2], defs[3]);
        let i32ty = fir.tys.prim(PrimKind::I32);
        let u8ty = fir.tys.prim(PrimKind::U8);
        let x_ty = fir.tys.nominal_of(pair, &[i32ty]);
        let y_ty = fir.tys.nominal_of(pair, &[u8ty]);
        let x = row(a, tr, x_ty, fir.tys.head_key(x_ty), 0);
        let y = row(b, tr, y_ty, fir.tys.head_key(y_ty), 1);
        assert!(!overlap(&fir.tys, &fir.sigs, &x, &y));
    }

    #[test]
    fn overlap_needs_the_same_trait() {
        let (mut fir, _n, defs) = build(4);
        let i32ty = fir.tys.prim(PrimKind::I32);
        let x = row(defs[2], defs[0], i32ty, fir.tys.head_key(i32ty), 0);
        let y = row(defs[3], defs[1], i32ty, fir.tys.head_key(i32ty), 1);
        assert!(!overlap(&fir.tys, &fir.sigs, &x, &y));
    }

    #[test]
    fn the_occurs_check_stops_t_against_pair_of_t() {
        let (mut fir, _n, defs) = build(4);
        let (tr, pair, a, b) = (defs[0], defs[1], defs[2], defs[3]);
        let t = fir.tys.param(a, 0);
        // `impl[T] Tr for T` is R18's error, but the unifier must still
        // terminate on it: `T = Pair[T]` fails the occurs check.
        let nested = fir.tys.nominal_of(pair, &[t]);
        let x = row(a, tr, t, HeadKey::Param, 0);
        let y = row(b, tr, nested, fir.tys.head_key(nested), 1);
        // `T` is `a`'s parameter and occurs in `y`'s self type only through
        // `a`'s own row, so the two unify; the point is that it returns.
        let _ = overlap(&fir.tys, &fir.sigs, &x, &y);
    }

    #[test]
    fn inherent_impls_live_in_their_own_bucket() {
        let (mut fir, _n, defs) = build(3);
        let i32ty = fir.tys.prim(PrimKind::I32);
        let mut index = ImplIndex::new();
        index.push(row(defs[1], NO_DEF, i32ty, fir.tys.head_key(i32ty), 0));
        index.push(row(defs[2], defs[0], i32ty, fir.tys.head_key(i32ty), 1));
        index.finish();
        assert_eq!(index.inherent(fir.tys.head_key(i32ty)).len(), 1);
        assert_eq!(index.bucket(defs[0], fir.tys.head_key(i32ty)).len(), 1);
    }
}
