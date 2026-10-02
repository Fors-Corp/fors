//! R20's normalisation (design §7.5, increment I6):
//! `normalise_proj(head, trait_ref, name)` and the [`ProjSolver`] the rest of
//! the checker plugs into [`fors_fir::subst`].
//!
//! Three properties, in the order they matter:
//!
//! * **R20's neutrality is not here.** A projection whose head is a rigid
//!   parameter, or another neutral projection, never reaches this module:
//!   `subst_core`'s `Proj` arm tests [`fors_fir::ty::TyStore::is_rigid`]
//!   (`Param | Proj`) and re-interns the projection itself. Equality on the
//!   interned id is then R20's "a neutral projection matches only itself",
//!   and nothing here can weaken it. [`Normaliser::solve`] is reached only
//!   for a head that is a type — a nominal, a primitive, a tuple, a `dyn`,
//!   an `fn` — which is exactly where an impl may answer.
//! * **The exact impl index first** (§17 amendment 3). A head written out in
//!   full is one binary search over `(trait, self TyId)`; the bucket scan
//!   runs only for genuinely generic impl heads. Only an impl with NO
//!   parameters can answer through the exact probe — a generic impl's
//!   `self_ty` mentions its own parameters and so cannot equal a concrete
//!   head — which is why the probe needs no match step at all.
//! * **A per-query work budget** (§17 amendment 2). The spike's shape Y
//!   (one chain asked under a widening set of trait arguments) is Θ(depth²)
//!   in DISTINCT questions, so no memo can flatten it; `NORMALISE_DEPTH_MAX`
//!   does not bound it because each individual question's depth is fine.
//!   [`NormState::budget_max`] counts memo MISSES per top-level
//!   normalisation and reports T0020 asking for the chain to be split rather
//!   than grinding.
//!
//! The memo key is `(head, trait_ref, name)` — §7.5's own key, and sound
//! here for the reason §17 amendment 1 gives for the SUBSTITUTION memo being
//! unsound under `(TyId, TraitRefId)`: what identifies this question is the
//! substituted HEAD, which the key carries. `Vec[i32].Item` and
//! `Vec[u8].Item` are two keys, so the second never reads the first's
//! answer.

use std::collections::HashMap;

use fors_fir::Fir;
use fors_fir::defpath::NO_DEF;
use fors_fir::impls::ImplIndex;
use fors_fir::sig::SigStore;
use fors_fir::subst::{Binding, MatchMode, ProjSolver};
use fors_fir::ty::{ArgsId, NO_TY, ProjKeyId, TY_ERROR, TraitRefId, TyId, TyStore};
use fors_index::Symbol;
use fors_index::ids::DefId;

use crate::wf::Wf;

/// §7.5's depth counter: a violated premise (an impl whose right-hand side is
/// not a strict subterm of its head, which R18 plus R61(d) forbid) becomes a
/// refusal to answer, never a hang.
pub const NORMALISE_DEPTH_MAX: u32 = 256;

/// §17 amendment 2's per-query work budget: memo MISSES inside one top-level
/// normalisation. Deliberately far above anything the conformance corpus
/// reaches (the measurement in `scale.rs` reports the peak), so the budget
/// diagnostic is a report about a pathological program, never about a
/// program this checker merely finds awkward.
pub const NORMALISE_BUDGET_MAX: u32 = 4096;

/// The normalisation memo and its counters. One per build, cleared wholesale
/// when `TraitWorldRevision` bumps (design §9.1) — the cost of which is I6's
/// second MEASUREMENT.
pub struct NormState {
    /// Impl buckets R20's lookup probed, parked for `Wf::close_query` to hand
    /// to the body's `check_body` in-edge set (design §9.1's `impls_for`).
    pub probed: Vec<(u32, u64)>,
    /// §7.5's memo, negative entries included.
    memo: HashMap<(TyId, TraitRefId, Symbol), Option<TyId>>,
    /// Every projection question asked of the solver.
    pub proj_queries: u64,
    /// The questions the memo could not answer.
    pub memo_misses: u64,
    /// `one_way_match` calls spent scanning impl buckets.
    pub match_steps: u64,
    /// The last `NoImpl` outcome: `(head, trait_ref)`. The CALLER reports it
    /// as T0012 at the site (§7.5, §8's R20 row: "NoImpl → T0012 at the
    /// site"), because only the caller knows which node to point at.
    pub no_impl: Option<(TyId, TraitRefId)>,
    /// Misses inside the current top-level normalisation, and the largest
    /// such count this build has seen (the measurement reads the peak).
    pub budget_used: u32,
    pub budget_peak: u32,
    /// Set when a top-level normalisation exceeded `budget_max`; the caller
    /// turns it into one T0020.
    pub budget_exceeded: bool,
    /// [`NORMALISE_BUDGET_MAX`], lowered by the unit tests so the budget path
    /// is exercised without building a 4096-deep chain.
    pub budget_max: u32,
    /// Set when `NORMALISE_DEPTH_MAX` was hit: an internal-error condition,
    /// reported as silence (the type simply does not normalise).
    pub depth_exceeded: bool,
    depth: u32,
}

impl Default for NormState {
    fn default() -> NormState {
        NormState {
            probed: Vec::new(),
            memo: HashMap::new(),
            proj_queries: 0,
            memo_misses: 0,
            match_steps: 0,
            no_impl: None,
            budget_used: 0,
            budget_peak: 0,
            budget_exceeded: false,
            budget_max: NORMALISE_BUDGET_MAX,
            depth_exceeded: false,
            depth: 0,
        }
    }
}

impl NormState {
    pub fn new() -> NormState {
        NormState::default()
    }

    /// An impl edit bumps `TraitWorldRevision`, which clears this wholesale
    /// (§9.1). The counters are NOT cleared: they count a build's work.
    pub fn clear(&mut self) {
        self.memo.clear();
    }

    pub fn len(&self) -> usize {
        self.memo.len()
    }

    pub fn is_empty(&self) -> bool {
        self.memo.is_empty()
    }
}

/// §7.5's `normalise_proj`, as a [`ProjSolver`]. Borrows the three tables it
/// needs separately from the [`TyStore`] the walk writes to, which is why
/// [`Wf`]'s wrappers below split the borrow of `Fir` by field.
pub struct Normaliser<'a> {
    pub sigs: &'a SigStore,
    pub impls: &'a ImplIndex,
    pub state: &'a mut NormState,
}

impl ProjSolver for Normaliser<'_> {
    fn solve(&mut self, store: &mut TyStore, head: TyId, key: ProjKeyId) -> Option<TyId> {
        let (tref, name) = store.proj_key(key);
        self.state.proj_queries += 1;
        if let Some(&hit) = self.state.memo.get(&(head, tref, name)) {
            if hit.is_none() {
                self.note_no_impl(store, head, tref);
            }
            return hit;
        }
        self.state.memo_misses += 1;
        self.state.budget_used += 1;
        if self.state.budget_used > self.state.budget_max {
            // §17 amendment 2: stop, and let the caller say so. Nothing is
            // memoised: the answer was never computed.
            self.state.budget_exceeded = true;
            return None;
        }
        if self.state.depth >= NORMALISE_DEPTH_MAX {
            self.state.depth_exceeded = true;
            return None;
        }
        let out = self.normalise_uncached(store, head, tref, name);
        if out.is_none() && (self.state.budget_exceeded || self.state.depth_exceeded) {
            // A guard fired somewhere below this question: the answer was
            // never computed, so there is nothing to remember. Memoising
            // `None` here would turn one T0020 into a permanent, silent
            // `NoImpl` for every later site asking the same question.
            return None;
        }
        self.state.memo.insert((head, tref, name), out);
        if out.is_none() {
            self.note_no_impl(store, head, tref);
        }
        out
    }
}

impl Normaliser<'_> {
    /// `NoImpl` is recorded only when the head genuinely has no impl of the
    /// trait. A head that did not lower, a trait that is not in this build,
    /// and an impl whose right-hand side is itself an error are all silence:
    /// a diagnostic for them would be a second report of someone else's
    /// root cause (design §7.10).
    fn note_no_impl(&mut self, store: &TyStore, head: TyId, tref: TraitRefId) {
        if head == TY_ERROR || head == NO_TY || store.is_error(head) {
            return;
        }
        let (trait_def, _) = store.trait_ref(tref);
        if trait_def == NO_DEF {
            return;
        }
        self.state
            .probed
            .push((trait_def.0, store.head_key(head).as_u64()));
        if !self
            .impls
            .bucket(trait_def, store.head_key(head))
            .is_empty()
            || !self.impls.exact(trait_def, head).is_empty()
        {
            // An impl for this head exists but did not answer (a missing or
            // poisoned `type A = ...`, which R17 already reported at the
            // impl). Silence.
            return;
        }
        self.state.no_impl = Some((head, tref));
    }

    fn normalise_uncached(
        &mut self,
        store: &mut TyStore,
        head: TyId,
        tref: TraitRefId,
        name: Symbol,
    ) -> Option<TyId> {
        if head == TY_ERROR || head == NO_TY || store.is_error(head) {
            return None;
        }
        let (trait_def, want_args) = store.trait_ref(tref);
        if trait_def == NO_DEF {
            return None;
        }
        let (imp, ib) = self.impl_lookup(store, trait_def, want_args, head)?;
        let rhs = self.assoc_rhs(imp, name)?;
        // The recursion is on a STRICT SUBTERM of `head` (R18 plus R61(d)),
        // so it descends; `NORMALISE_DEPTH_MAX` catches a violated premise.
        self.state.depth += 1;
        let out = fors_fir::subst::subst_norm_with(store, rhs, &ib, self);
        self.state.depth -= 1;
        out
    }

    /// §7.6's `impl_lookup`, specialised to a head that is a type: the exact
    /// `(trait, self TyId)` probe (§17 amendment 3) and then the
    /// `(trait, HeadKey)` bucket scan. At most one impl answers, by R19.
    fn impl_lookup(
        &mut self,
        store: &mut TyStore,
        trait_def: DefId,
        want_args: ArgsId,
        head: TyId,
    ) -> Option<(DefId, Binding)> {
        for r in self.impls.exact(trait_def, head) {
            let row = self.impls.row(r);
            if row.trait_args != want_args {
                continue;
            }
            let arity = self.arity(row.def);
            // Only a parameter-free impl can answer here: a generic impl's
            // `self_ty` mentions its own parameters, so it never equals a
            // head written out in full. One probe, no match step.
            if arity == 0 {
                return Some((row.def, Binding::new(&[(row.def, 0)])));
            }
        }
        let hk = store.head_key(head);
        self.state.probed.push((trait_def.0, hk.as_u64()));
        for r in self.impls.bucket(trait_def, hk) {
            let row = self.impls.row(r);
            let arity = self.arity(row.def);
            let mut b = Binding::new(&[(row.def, arity as u16)]);
            self.state.match_steps += 1;
            if !fors_fir::subst::one_way_match_mode(
                store,
                row.self_ty,
                head,
                &mut b,
                &mut fors_fir::subst::NeutralOnly,
                MatchMode::Strict,
            ) {
                continue;
            }
            if !self.match_trait_args(store, row.trait_args, want_args, &mut b) {
                continue;
            }
            if b.is_complete() {
                return Some((row.def, b));
            }
        }
        None
    }

    fn match_trait_args(
        &mut self,
        store: &mut TyStore,
        row_args: ArgsId,
        want_args: ArgsId,
        b: &mut Binding,
    ) -> bool {
        let ra = store.args_vec(row_args);
        let wa = store.args_vec(want_args);
        if ra.len() != wa.len() {
            return false;
        }
        for (x, y) in ra.iter().zip(wa.iter()) {
            self.state.match_steps += 1;
            if !fors_fir::subst::one_way_match_mode(
                store,
                *x,
                *y,
                b,
                &mut fors_fir::subst::NeutralOnly,
                MatchMode::Strict,
            ) {
                return false;
            }
        }
        true
    }

    fn arity(&self, def: DefId) -> usize {
        self.sigs.generics_store.count(self.sigs.generics(def))
    }

    /// `assoc_def(imp, name)`: the impl's own `type A = ...`. `None` when the
    /// impl does not define it (R17 reported that at the impl) or the
    /// right-hand side did not lower.
    fn assoc_rhs(&self, imp: DefId, name: Symbol) -> Option<TyId> {
        let a = self.sigs.assoc(imp);
        for i in 0..self.sigs.assocs.count(a) {
            let row = self.sigs.assocs.get(a, i);
            if row.name == name {
                if row.rhs == NO_TY || row.rhs == TY_ERROR {
                    return None;
                }
                return Some(row.rhs);
            }
        }
        None
    }
}

impl Wf<'_> {
    /// Runs `f` with the type store and a live [`Normaliser`]. The borrow is
    /// split by FIELD: `fir.tys` is written to while `fir.sigs`, `impls` and
    /// `norm` are read, which is the only reason the solver is a separate
    /// struct rather than `&mut Wf`.
    fn with_norm<R>(&mut self, f: impl FnOnce(&mut TyStore, &mut Normaliser) -> R) -> R {
        let Fir { tys, sigs, .. } = &mut *self.fir;
        let mut n = Normaliser {
            sigs,
            impls: &self.impls,
            state: &mut self.norm,
        };
        f(tys, &mut n)
    }

    /// Opens a top-level normalisation: the per-query budget starts at zero
    /// and `no_impl` is cleared, so what the caller reads afterwards belongs
    /// to this query alone.
    fn open_query(&mut self) {
        self.norm.budget_used = 0;
        self.norm.no_impl = None;
        // A guard flag a previous caller did not take (the lookup's
        // `normalise(recv)` asks and moves on) must not leak into this
        // query: it would suppress memoisation here and be reported at
        // whichever later site happens to read it.
        self.norm.budget_exceeded = false;
        self.norm.depth_exceeded = false;
    }

    fn close_query(&mut self) {
        self.norm.budget_peak = self.norm.budget_peak.max(self.norm.budget_used);
        // R20's own impl-bucket probes belong to whoever asked: hand them to
        // the body's `check_body` in-edge set (design §9.1). `Normaliser`
        // cannot reach `Wf`, so it parks them here and this is the drain.
        let probed = std::mem::take(&mut self.norm.probed);
        for (tr, head) in probed {
            self.note_bucket_raw(tr, head);
        }
    }

    /// `subst_norm` with R20's normalisation: design §7.4's
    /// substitute-and-normalise, the only place a projection collapses.
    pub(crate) fn subst_norm_n(&mut self, ty: TyId, b: &Binding) -> Option<TyId> {
        self.open_query();
        let out = self.with_norm(|tys, n| fors_fir::subst::subst_norm_with(tys, ty, b, n));
        self.close_query();
        out
    }

    /// R20 over a type with nothing to substitute: every projection on a
    /// concrete head inside `ty` collapses, every neutral one stays. Used
    /// wherever a type that was built before the impl index was complete
    /// re-enters the checker (member types, `for`-element types, the
    /// receiver of a method lookup).
    pub(crate) fn normalise(&mut self, ty: TyId) -> TyId {
        if self.fir.tys.is_monomorphic(ty) {
            return ty;
        }
        let b = Binding::new(&[]);
        self.subst_norm_n(ty, &b).unwrap_or(ty)
    }

    /// §7.5's `normalise_proj(head, trait_ref, name)` asked directly, for
    /// the callers that already hold the three pieces (R31's `for`-element
    /// type from `Item`, R43's member lookup). `None` is "no answer": the
    /// caller decides between `TY_ERROR` and a report, reading
    /// [`Wf::take_no_impl`].
    pub(crate) fn norm_proj(&mut self, head: TyId, tref: TraitRefId, name: Symbol) -> Option<TyId> {
        self.open_query();
        let out = self.with_norm(|tys, n| {
            let key = tys.intern_proj_key(tref, name);
            n.solve(tys, head, key)
        });
        self.close_query();
        out
    }

    /// `one_way_match` with the normalising solver (design §7.4: "head bound
    /// => normalise, then compare").
    pub(crate) fn match_n(&mut self, pattern: TyId, target: TyId, b: &mut Binding) -> bool {
        self.match_n_mode(pattern, target, b, MatchMode::Strict)
    }

    pub(crate) fn match_n_mode(
        &mut self,
        pattern: TyId,
        target: TyId,
        b: &mut Binding,
        mode: MatchMode,
    ) -> bool {
        self.open_query();
        let out = self.with_norm(|tys, n| {
            fors_fir::subst::one_way_match_mode(tys, pattern, target, b, n, mode)
        });
        self.close_query();
        out
    }

    /// The `NoImpl` the last normalisation reported, taken (so one cause is
    /// reported once).
    pub(crate) fn take_no_impl(&mut self) -> Option<(TyId, TraitRefId)> {
        self.norm.no_impl.take()
    }

    /// Whether the last normalisation ran out of §17 amendment 2's budget,
    /// taken.
    pub(crate) fn take_budget_exceeded(&mut self) -> bool {
        std::mem::take(&mut self.norm.budget_exceeded)
    }

    /// R20's `NoImpl`, as T0012 at the site that asked (design §8's R20 row).
    pub(crate) fn emit_no_impl(
        &mut self,
        cx: &mut crate::body::BodyCx,
        node: usize,
        head: TyId,
        tref: TraitRefId,
    ) {
        let subject = self.show(head);
        let (tdef, _) = self.fir.tys.trait_ref(tref);
        let tr = self.head_name(tdef);
        self.bemit(
            cx,
            node,
            12,
            20,
            format!("`{subject}` does not implement `{tr}`, so the projection on it has no type"),
        );
    }

    /// §17 amendment 2's report: the chain is too wide to normalise, so ask
    /// for it to be split rather than grinding. Emitted with R20's own code
    /// at R20's site.
    pub(crate) fn emit_budget(&mut self, cx: &mut crate::body::BodyCx, node: usize) {
        self.bemit(
            cx,
            node,
            20,
            20,
            format!(
                "normalising the projections here needs more than {} steps; split the chain by naming an intermediate type",
                self.norm.budget_max
            ),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_fir::defpath::{DeclKey, HeadKey, NO_DECL_KEY};
    use fors_fir::impls::ImplRow;
    use fors_fir::sig::{Assoc, GParam, GParamKind, NO_BOUNDS, NO_CONSTRAINTS, SigKind};
    use fors_fir::ty::{NO_ARGS, PrimKind};
    use fors_index::Interner;
    use fors_index::decl::DeclKind;

    /// A synthetic trait world, exactly the one §7.5 is written against:
    ///
    /// ```text
    /// trait Iter { type Item; }
    /// struct Base;        impl Iter for Base    { type Item = i64; }
    /// struct W[T];        impl[T] Iter for W[T] { type Item = T.Item; }
    /// ```
    ///
    /// `W[W[...[Base]]].Item` then costs one memo miss per level, which is
    /// what the budget counts and what the depth guard bounds.
    struct World {
        fir: Fir,
        impls: ImplIndex,
        iter: DefId,
        item: fors_index::Symbol,
        w: DefId,
        ask: DefId,
        base_ty: TyId,
        i64_ty: TyId,
    }

    fn world() -> World {
        let mut names = Interner::new();
        let mut fir = Fir::new();
        let m = {
            let s = names.intern(b"m");
            fir.keys.paths.intern(&[s])
        };
        let declare = |fir: &mut Fir, names: &mut Interner, n: &[u8], k: DeclKind, s: SigKind| {
            let nm = names.intern(n);
            let key = fir.keys.intern(DeclKey {
                parent: NO_DECL_KEY,
                module: m,
                kind: k,
                name: Some(nm),
                disamb: 0,
            });
            fir.declare(key, s)
        };
        let iter = declare(
            &mut fir,
            &mut names,
            b"Iter",
            DeclKind::Trait,
            SigKind::Trait,
        );
        let base = declare(
            &mut fir,
            &mut names,
            b"Base",
            DeclKind::Struct,
            SigKind::Struct,
        );
        let w = declare(
            &mut fir,
            &mut names,
            b"W",
            DeclKind::Struct,
            SigKind::Struct,
        );
        let imp_base = declare(&mut fir, &mut names, b"i0", DeclKind::Impl, SigKind::Impl);
        let imp_w = declare(&mut fir, &mut names, b"i1", DeclKind::Impl, SigKind::Impl);
        // The asking function: `fn ask[X](..) -> X.Item`. A projection's
        // head is ALWAYS written on a parameter (`TyStore::proj` asserts
        // R20's premise), so a concrete head only ever arises by
        // SUBSTITUTION — which is the path under test.
        let ask = declare(&mut fir, &mut names, b"ask", DeclKind::Fn, SigKind::Fn);

        let item = names.intern(b"Item");
        let i64_ty = fir.tys.prim(PrimKind::I64);
        let base_ty = fir.tys.nominal(base, NO_ARGS);

        // `trait Iter { type Item; }` — `Self` is ordinal 0 of its generics.
        let tname = names.intern(b"Self");
        let g = fir.sigs.generics_store.push(
            &[GParam {
                name: tname,
                kind: GParamKind::Type,
                bounds: NO_BOUNDS,
            }],
            NO_CONSTRAINTS,
        );
        fir.sigs.set_generics(iter, g);
        let a = fir.sigs.assocs.push(&[Assoc {
            name: item,
            bounds: NO_BOUNDS,
            rhs: NO_TY,
        }]);
        fir.sigs.set_assoc(iter, a);

        // `impl Iter for Base { type Item = i64; }` — no parameters, so the
        // exact probe answers it.
        let a0 = fir.sigs.assocs.push(&[Assoc {
            name: item,
            bounds: NO_BOUNDS,
            rhs: i64_ty,
        }]);
        fir.sigs.set_assoc(imp_base, a0);

        // `impl[T] Iter for W[T] { type Item = T.Item; }`
        let pname = names.intern(b"T");
        let gw = fir.sigs.generics_store.push(
            &[GParam {
                name: pname,
                kind: GParamKind::Type,
                bounds: NO_BOUNDS,
            }],
            NO_CONSTRAINTS,
        );
        fir.sigs.set_generics(imp_w, gw);
        let t = fir.tys.param(imp_w, 0);
        let w_t = fir.tys.nominal_of(w, &[t]);
        let own = fir.tys.intern_trait_ref(iter, NO_ARGS);
        let pk = fir.tys.intern_proj_key(own, item);
        let rhs = fir.tys.proj(t, pk);
        let a1 = fir.sigs.assocs.push(&[Assoc {
            name: item,
            bounds: NO_BOUNDS,
            rhs,
        }]);
        fir.sigs.set_assoc(imp_w, a1);

        let mut impls = ImplIndex::new();
        let hk_base = fir.tys.head_key(base_ty);
        impls.push(ImplRow {
            def: imp_base,
            trait_def: iter,
            inherent: false,
            trait_args: NO_ARGS,
            self_ty: base_ty,
            head: hk_base,
            order: 0,
        });
        let hk_w: HeadKey = fir.tys.head_key(w_t);
        impls.push(ImplRow {
            def: imp_w,
            trait_def: iter,
            inherent: false,
            trait_args: NO_ARGS,
            self_ty: w_t,
            head: hk_w,
            order: 1,
        });
        impls.finish();

        let xname = names.intern(b"X");
        let gask = fir.sigs.generics_store.push(
            &[GParam {
                name: xname,
                kind: GParamKind::Type,
                bounds: NO_BOUNDS,
            }],
            NO_CONSTRAINTS,
        );
        fir.sigs.set_generics(ask, gask);

        World {
            fir,
            impls,
            iter,
            item,
            w,
            ask,
            base_ty,
            i64_ty,
        }
    }

    impl World {
        /// `W[W[...[Base]]]`, `depth` wrappers deep.
        fn chain(&mut self, depth: usize) -> TyId {
            let mut t = self.base_ty;
            for _ in 0..depth {
                t = self.fir.tys.nominal_of(self.w, &[t]);
            }
            t
        }

        /// `X.Item` with `X := t`, normalised with `state` — §7.4's
        /// substitute-and-normalise, the only way a concrete head reaches
        /// the solver.
        fn normalise(&mut self, state: &mut NormState, t: TyId) -> Option<TyId> {
            let own = self.fir.tys.intern_trait_ref(self.iter, NO_ARGS);
            let pk = self.fir.tys.intern_proj_key(own, self.item);
            let x = self.fir.tys.param(self.ask, 0);
            let p = self.fir.tys.proj(x, pk);
            let mut b = Binding::new(&[(self.ask, 1)]);
            b.bind(self.ask, 0, t);
            state.budget_used = 0;
            state.no_impl = None;
            let Fir { tys, sigs, .. } = &mut self.fir;
            let mut n = Normaliser {
                sigs,
                impls: &self.impls,
                state,
            };
            fors_fir::subst::subst_norm_with(tys, p, &b, &mut n)
        }
    }

    #[test]
    fn a_chain_collapses_by_structural_descent_and_costs_one_miss_per_level() {
        let mut w = world();
        let mut st = NormState::new();
        for depth in [0usize, 1, 2, 4, 8] {
            st.clear();
            st.memo_misses = 0;
            let t = w.chain(depth);
            let out = w.normalise(&mut st, t);
            assert_eq!(out, Some(w.i64_ty), "depth {depth} must reach i64");
            assert_eq!(
                st.memo_misses,
                depth as u64 + 1,
                "depth {depth}: one memo miss per level, no more"
            );
            assert_eq!(st.budget_used, depth as u32 + 1);
        }
    }

    #[test]
    fn the_memo_answers_the_second_identical_question_for_free() {
        let mut w = world();
        let mut st = NormState::new();
        let t = w.chain(6);
        assert_eq!(w.normalise(&mut st, t), Some(w.i64_ty));
        let after_first = st.memo_misses;
        assert_eq!(w.normalise(&mut st, t), Some(w.i64_ty));
        assert_eq!(
            st.memo_misses, after_first,
            "the second ask costs no miss at all"
        );
    }

    #[test]
    fn the_per_query_work_budget_refuses_rather_than_grinding() {
        // §17 amendment 2: the budget counts memo MISSES in one top-level
        // normalisation. A chain deeper than the budget is refused, and the
        // caller turns that into one T0020 asking for it to be split.
        let mut w = world();
        let mut st = NormState::new();
        st.budget_max = 3;
        let t = w.chain(8);
        assert_eq!(w.normalise(&mut st, t), None);
        assert!(st.budget_exceeded, "the budget must say why it stopped");
        assert!(
            st.budget_used <= st.budget_max + 1,
            "and must stop AT the budget, not after the whole chain"
        );
        // The same world under the real budget answers.
        let mut st2 = NormState::new();
        assert_eq!(w.normalise(&mut st2, t), Some(w.i64_ty));
        assert!(!st2.budget_exceeded);
    }

    #[test]
    fn an_exhausted_budget_poisons_no_memo_entry() {
        // Verifier's probe: the frames ABOVE the one that ran out of budget
        // also return `None`, and must not remember that as `NoImpl`. The
        // SAME state, asked again with the budget lifted, must answer — the
        // entries the partial run did complete are kept, the rest are
        // recomputed.
        let mut w = world();
        let mut st = NormState::new();
        st.budget_max = 3;
        let t = w.chain(8);
        assert_eq!(w.normalise(&mut st, t), None);
        assert!(st.budget_exceeded);
        st.budget_exceeded = false;
        st.budget_max = NORMALISE_BUDGET_MAX;
        assert_eq!(
            w.normalise(&mut st, t),
            Some(w.i64_ty),
            "a refused question is not a negative answer"
        );
        assert!(!st.budget_exceeded);
        assert!(st.no_impl.is_none(), "and never reported as NoImpl");
    }

    #[test]
    fn a_head_without_an_impl_is_no_impl_and_is_memoised_negatively() {
        let mut w = world();
        let mut st = NormState::new();
        let plain = w.fir.tys.prim(PrimKind::U8);
        assert_eq!(w.normalise(&mut st, plain), None);
        let (head, tref) = st.no_impl.expect("the caller needs the pair for T0012");
        assert_eq!(head, plain);
        assert_eq!(w.fir.tys.trait_ref(tref).0, w.iter);
        let misses = st.memo_misses;
        assert_eq!(w.normalise(&mut st, plain), None);
        assert_eq!(st.memo_misses, misses, "the negative answer is cached too");
        assert!(st.no_impl.is_some(), "and is still reported on a memo hit");
    }

    #[test]
    fn a_rigid_head_stays_neutral_and_never_reaches_the_solver() {
        // R20: the projection on a rigid parameter is re-interned as itself
        // by `subst_core`, so the solver is never asked. Nothing in this
        // module can weaken that; the counter proves it was not asked.
        let mut w = world();
        let mut st = NormState::new();
        let rigid = w.fir.tys.param(w.iter, 0);
        let out = w
            .normalise(&mut st, rigid)
            .expect("a neutral projection is a type");
        assert_eq!(w.fir.tys.tag(out), fors_fir::ty::TyTag::Proj);
        assert_eq!(st.proj_queries, 0, "the solver was never consulted");
        // And it equals only itself: the same question gives the same id,
        // a different head a different one.
        let again = w.normalise(&mut st, rigid).unwrap();
        assert_eq!(out, again);
        let other = w.chain(1);
        assert_ne!(w.normalise(&mut st, other).unwrap(), out);
    }
}
