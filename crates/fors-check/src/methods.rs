//! Method-call resolution: ch09 R43-R46, I4's typing side (design §13).
//!
//! I4 owns the half that needs no trait search over projections and no
//! inference: the receiver's head is a concrete nominal type, a PRIMITIVE
//! (R43 says "`S`'s head", and a primitive carries inherent impls and
//! prelude-trait impls like any other head) or a rigid parameter, and
//! every candidate method is non-generic (methods with parameters to
//! determine stay [`LookupError::Silent`] for I5).
//!
//! Tiers (R43): (1) receiver methods in the head's inherent impls whose
//! self type matches; (2) receiver methods of each candidate trait the
//! receiver implements — for a rigid parameter exactly its bounds, for a
//! concrete head the prelude traits plus the traits with an impl for the
//! head in the defining, current or directly-used module (ch08 R7, walked
//! over [`Wf::mod_edges`]). The first non-empty tier answers; more than
//! one candidate in it is R44's error. Provided methods count exactly
//! like required ones (R43: `Iterator`'s adaptors need no blanket impl).
//!
//! Silence contract: anything this increment does not own — a projection
//! receiver, a generic method, a qualified head that is not a nominal
//! type, or a primitive head whose table this build does not have (see
//! [`Wf::prim_table_incomplete`]) — answers [`LookupError::Silent`],
//! never a diagnostic, so pending rows stay quiet until their increment
//! deletes them.

use fors_fir::sig::{Conv, SigKind};
use fors_fir::subst::{Binding, one_way_match};
use fors_fir::ty::{ArgsId, NO_ARGS, NO_TY, TyId, TyTag};
use fors_index::Symbol;
use fors_index::diag::Code;
use fors_index::ids::{DefId, ModuleId};

use crate::body::BodyCx;
use crate::facts::MemberTarget;
use crate::wf::{Holds, Wf};

/// ch03's language-known methods of the numeric primitives, declared by no
/// file: Rule 4's `wrap_`/`sat_`/`unchecked_` counterpart of each of Rule
/// 2's trapping operators (`+ - * / %`, both shifts, and unary `-`), plus
/// Rule 6's three lossy conversions. The stand-in for ch03's surface until
/// I10 declares it ([`Wf::prim_table_incomplete`]); a name outside this
/// list is an ordinary R43 miss on a primitive.
const CH03_PRIM_METHODS: &[&[u8]] = &[
    b"wrap_add",
    b"wrap_sub",
    b"wrap_mul",
    b"wrap_div",
    b"wrap_rem",
    b"wrap_shl",
    b"wrap_shr",
    b"wrap_neg",
    b"sat_add",
    b"sat_sub",
    b"sat_mul",
    b"sat_div",
    b"sat_rem",
    b"sat_shl",
    b"sat_shr",
    b"sat_neg",
    b"unchecked_add",
    b"unchecked_sub",
    b"unchecked_mul",
    b"unchecked_div",
    b"unchecked_rem",
    b"unchecked_shl",
    b"unchecked_shr",
    b"unchecked_neg",
    b"wrap_as",
    b"sat_as",
    b"trunc_as",
];

/// A resolved method call: the method, where it was found, and the
/// receiver convention R46 reads.
#[derive(Clone, Copy, Debug)]
pub struct MethodHit {
    /// The method's `fn` item.
    pub def: DefId,
    /// The inherent impl or trait that supplied it (for R46's diagnostic
    /// and the dependency edge).
    pub owner: DefId,
    /// [`fors_fir::NO_DEF`] for an inherent method, else the trait.
    pub trait_def: DefId,
    /// The convention of the receiver parameter.
    pub conv: Conv,
    /// The receiver parameter's slot in the method's signature.
    pub recv_slot: u8,
    /// The receiver's type as looked up (for R46's copy/move decision).
    pub recv_ty: TyId,
    /// `true` when the call named the receiver as an ordinary first
    /// argument (R45's qualified form) rather than in method position.
    pub receiver_is_arg: bool,
}

/// A named method considered as a call candidate.
enum Candidate {
    /// Resolved: I4 types the call.
    Hit(MethodHit),
    /// A method with parameters to determine: I5's inference owns it, so
    /// it counts as PRESENT for tier purposes (R43 stops at the first
    /// non-empty tier) and as a candidate for ambiguity (R44), but a tier
    /// with no better answer stays silent rather than erroring.
    Generic { owner: DefId },
    /// Not a candidate (wrong self type, associated function in method
    /// position, foreign private after its diagnostic).
    No,
}

/// Why a lookup produced no method.
#[derive(Clone, Debug)]
pub enum LookupError {
    /// Not this increment's: stay silent (I5/I6 own it).
    Silent,
    /// R43: no candidate. Carries the rendered receiver and method name.
    None { recv: String, name: String },
    /// R44: several candidates in the answering tier. Carries one
    /// `Owner.method` line per candidate, in lookup order.
    Ambiguous {
        name: String,
        candidates: Vec<String>,
    },
}

impl Wf<'_> {
    /// Resolves `name` on `recv` (qualifiers already stripped by the
    /// caller) for a call at `node` in method position. Memoised by
    /// (requesting module, receiver, name, position): the module matters
    /// because R43's candidate traits come from the module graph (ch08 R7),
    /// so the same `(TyId, Symbol)` resolves differently in different
    /// modules.
    pub fn lookup_method(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Result<MethodHit, LookupError> {
        let bare = self.fir.tys.unqual(recv);
        let cur_mod = self.module_of(cx.owner);
        let key = (cur_mod.0, bare, name, true);
        if let Some(cached) = self.method_memo.get(&key).cloned() {
            self.replay_method_deps(bare, &cached);
            return cached;
        }
        let ans = match self.fir.tys.tag(bare) {
            // A primitive head carries a method table exactly like a
            // nominal one (R43 says "`S`'s head", not "`S`'s declaration"):
            // `impl Str { pub fn len(let self) }` is an inherent impl whose
            // head key is `HeadKey::Prim(Str)`, and the prelude traits are
            // tier (2) for it as for any other head. R43's `.count()` on
            // the `usize` that an inherent `take` re-routed to is this case.
            TyTag::Nominal | TyTag::Prim => self.lookup_on_head(cx, node, bare, name, true),
            TyTag::Param => self.lookup_on_param(cx, node, bare, name),
            // Projections are I6's; anything else has no method table this
            // increment owns. Silent.
            _ => Err(LookupError::Silent),
        };
        self.method_memo.insert(key, ans.clone());
        ans
    }

    /// Replays the dependency edges a memoised lookup found, into the
    /// current body's `DepSet` (design §9: every body records what it read).
    /// The full consulted set (every impl/trait scanned) is recorded on the
    /// miss; a hit replays the answer's own edges, which is what
    /// invalidation reads.
    fn replay_method_deps(&mut self, recv: TyId, ans: &Result<MethodHit, LookupError>) {
        if self.fir.tys.tag(recv) == TyTag::Nominal {
            let head = DefId(self.fir.tys.a(recv));
            self.dep(head);
        }
        if let Ok(hit) = ans {
            self.dep(hit.def);
            self.dep(hit.owner);
            if hit.trait_def != fors_fir::NO_DEF {
                self.dep(hit.trait_def);
            }
        }
    }

    /// Tier (1)+(2) for a concrete nominal or primitive receiver.
    /// `method_position` is false for R45's qualified form, where
    /// associated functions answer too and every parameter is an
    /// ordinary argument.
    fn lookup_on_head(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
        method_position: bool,
    ) -> Result<MethodHit, LookupError> {
        // A primitive head has no declaration in this build: nothing to
        // depend on, and no DEFINING module, so R43's module scope for it
        // is the current module and its direct edges only (ch08 R7).
        let head = (self.fir.tys.tag(recv) == TyTag::Nominal).then(|| DefId(self.fir.tys.a(recv)));
        if let Some(h) = head {
            self.dep(h);
        }
        let key = self.fir.tys.head_key(recv);
        let mut tier1: Vec<Candidate> = Vec::new();
        for r in self.impls.inherent(key) {
            let row = self.impls.row(r);
            self.dep(row.def);
            for (mname, mdef) in self.impl_method_names(row.def) {
                if mname != name {
                    continue;
                }
                self.consider(cx, node, mdef, row.def, recv, method_position, &mut tier1);
            }
        }
        if !tier1.is_empty() {
            // R43 stops at the first non-empty tier: a generic same-name
            // method makes tier 1 non-empty even when nothing in it
            // resolves, so tier 2 is never consulted.
            return Self::answer(self, name, tier1);
        }
        let mut seen = Vec::new();
        let mut tier2: Vec<Candidate> = Vec::new();
        let mut saw_generic = false;
        // The prelude traits first (stable order: `traits` array order),
        // then the scoped impl traits in impl-row order. Both are
        // deterministic across runs and hosts.
        for &trait_def in self.prelude.traits.iter() {
            if trait_def == fors_fir::NO_DEF || seen.contains(&trait_def) {
                continue;
            }
            seen.push(trait_def);
            self.trait_candidates(
                cx,
                node,
                recv,
                name,
                trait_def,
                method_position,
                &mut tier2,
                &mut saw_generic,
            );
        }
        let head_mod = head.map(|h| self.module_of(h));
        let cur_mod = self.module_of(cx.owner);
        let edges = self.edges_from(cur_mod);
        for r in 0..self.impls.len() {
            let row = self.impls.row(r as u32);
            if row.trait_def == fors_fir::NO_DEF || seen.contains(&row.trait_def) {
                continue;
            }
            if self.fir.tys.head_key(row.self_ty) != key {
                continue;
            }
            let impl_mod = self.module_of(row.def);
            if Some(impl_mod) != head_mod && impl_mod != cur_mod && !edges.contains(&impl_mod) {
                continue;
            }
            seen.push(row.trait_def);
            self.dep(row.def);
            self.trait_candidates(
                cx,
                node,
                recv,
                name,
                row.trait_def,
                method_position,
                &mut tier2,
                &mut saw_generic,
            );
        }
        if tier2.is_empty() {
            // A generic method was in the running, or the receiver hides
            // a projection normalization could reveal: I5/I6 own the
            // call, so no tier answers and there is nothing to report.
            // Otherwise the table is complete and R43 reports.
            if saw_generic
                || self.recv_hides_projection(recv)
                || self.prim_table_incomplete(recv, name)
            {
                return Err(LookupError::Silent);
            }
            return Err(LookupError::None {
                recv: self.show(recv),
                name: self.sym(name),
            });
        }
        Self::answer(self, name, tier2)
    }

    /// R45's qualified lookup over a nominal head: same tiers, but
    /// associated functions answer and the receiver stays an argument.
    /// Memoised alongside [`Self::lookup_method`] with `method_position`
    /// false, so a qualified and an unqualified lookup for the same
    /// `(module, receiver, name)` never share an entry.
    pub fn lookup_qualified(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Result<MethodHit, LookupError> {
        let bare = self.fir.tys.unqual(recv);
        let cur_mod = self.module_of(cx.owner);
        let key = (cur_mod.0, bare, name, false);
        if let Some(cached) = self.method_memo.get(&key).cloned() {
            self.replay_method_deps(bare, &cached);
            return cached;
        }
        let ans = match self.lookup_on_head(cx, node, bare, name, false) {
            Ok(mut hit) => {
                hit.receiver_is_arg = true;
                Ok(hit)
            }
            Err(e) => Err(e),
        };
        self.method_memo.insert(key, ans.clone());
        ans
    }

    /// R43's rigid case: the candidate traits are exactly the bounds.
    /// An empty tier stays silent: bound-trait declarations (especially
    /// the prelude's opaque rows) need not list every method yet, so
    /// absence proves nothing. Ambiguity still reports.
    fn lookup_on_param(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Result<MethodHit, LookupError> {
        let owner = DefId(self.fir.tys.a(recv));
        let ord = self.fir.tys.b(recv) as usize;
        let gid = self.fir.sigs.generics(owner);
        if ord >= self.fir.sigs.generics_store.count(gid) {
            return Err(LookupError::Silent);
        }
        let bounds = self.fir.sigs.generics_store.param(gid, ord).bounds;
        let mut tier: Vec<Candidate> = Vec::new();
        for r in self.fir.sigs.bounds.get(bounds).to_vec() {
            let trait_def = self.fir.tys.trait_ref(r).0;
            if trait_def == fors_fir::NO_DEF {
                continue;
            }
            self.dep(trait_def);
            for (mname, mdef) in self.trait_method_defs(trait_def) {
                if mname != name {
                    continue;
                }
                self.consider(cx, node, mdef, trait_def, recv, true, &mut tier);
            }
        }
        if tier.is_empty() {
            // Rigid silence: bound-trait declarations (especially the
            // prelude's opaque rows) need not list every method yet, so
            // an empty tier proves nothing. Ambiguity still reports.
            let _ = recv;
            return Err(LookupError::Silent);
        }
        Self::answer(self, name, tier)
    }

    /// Whether a MISS on a primitive head is an artifact of a surface this
    /// increment does not model, rather than R43's "no candidate".
    ///
    /// A primitive's method table has three contributors, and only one of
    /// them is in a checker build: the prelude traits and the in-scope
    /// trait impls (tier (2), consulted above). The other two are not:
    ///
    /// - **ch03 Rules 4 and 6's family.** `wrap_<op>`, `sat_<op>` and
    ///   `unchecked_<op>` for each of Rule 2's trapping operators, and
    ///   Rule 6's `wrap_as`/`sat_as`/`trunc_as`, are LANGUAGE-known
    ///   methods of every numeric primitive, declared by no file at all;
    ///   §13 reaches ch03 at I10. The family is FINITE and listed in
    ///   [`CH03_PRIM_METHODS`]: exactly those names are an absence this
    ///   increment cannot prove (`03-numerics/{sat-add-saturates,wrap-add-
    ///   no-trap}` call them in a build with no `std`); `wrap_foo` is not
    ///   in the family and reports like any other miss. I10 replaces the
    ///   table with the real declarations.
    /// - **`std`'s inherent impls.** Of the 15 primitives only `Str`
    ///   carries one in `std` (`impl Str`, `std/mem/text.fors`, ch10 Rule
    ///   26), and a build without `std` sources does not have it
    ///   (`10-std/str-{index-is-bytes,slice-non-boundary-raises}`). The
    ///   carve-out is therefore by EVIDENCE, not by receiver: `Str` and
    ///   `rawptr` (whose accessors no file declares either) are silent
    ///   only while the build has NO inherent impl for that head; once
    ///   `impl Str` is in the build the tiers above are the whole table
    ///   and R43 reports. Every other primitive has no inherent impl
    ///   anywhere, so for those the tiers always are the whole table.
    fn prim_table_incomplete(&self, recv: TyId, name: Symbol) -> bool {
        use fors_fir::ty::PrimKind;
        if self.fir.tys.tag(recv) != TyTag::Prim {
            return false;
        }
        let kind = PrimKind::from_u8(self.fir.tys.a(recv) as u8);
        if matches!(kind, Some(PrimKind::Str) | Some(PrimKind::RawPtr) | None) {
            let key = self.fir.tys.head_key(recv);
            return self.impls.inherent(key).is_empty();
        }
        let n = self.names.resolve(name);
        CH03_PRIM_METHODS.contains(&n)
    }

    /// Whether `recv` mentions a projection anywhere in its arguments: a
    /// call on it may resolve after I6's normalization, so an empty tier
    /// stays silent rather than reporting R43.
    fn recv_hides_projection(&self, recv: TyId) -> bool {
        fors_fir::impls::contains_proj(&self.fir.tys, recv)
    }

    /// Sorts one named method into its tier.
    fn consider(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        mdef: DefId,
        owner: DefId,
        recv: TyId,
        method_position: bool,
        tier: &mut Vec<Candidate>,
    ) {
        match self.concrete_candidate(cx, node, mdef, owner, recv, method_position) {
            Candidate::Hit(hit) => tier.push(Candidate::Hit(hit)),
            Candidate::Generic { owner } => tier.push(Candidate::Generic { owner }),
            Candidate::No => {}
        }
    }

    /// One candidate, or R44's error. Inherent-before-trait is the only
    /// precedence; nothing is ever ranked. A generic same-name method counts
    /// as present: one hit plus any generics (or two hits) is ambiguous;
    /// generics alone stay silent for I5.
    fn answer(wf: &mut Wf, name: Symbol, tier: Vec<Candidate>) -> Result<MethodHit, LookupError> {
        let mut hits = Vec::new();
        let mut generic_owners = Vec::new();
        for c in tier {
            match c {
                Candidate::Hit(hit) => hits.push(hit),
                Candidate::Generic { owner } => generic_owners.push(owner),
                Candidate::No => {}
            }
        }
        if hits.is_empty() {
            // Every same-name method needs I5's inference: the tier is
            // non-empty (it blocks the next one) but has nothing to call.
            return Err(LookupError::Silent);
        }
        if hits.len() == 1 && generic_owners.is_empty() {
            let hit = hits.pop().unwrap();
            wf.dep(hit.def);
            wf.dep(hit.owner);
            if hit.trait_def != fors_fir::NO_DEF {
                wf.dep(hit.trait_def);
            }
            return Ok(hit);
        }
        let mut candidates: Vec<String> = hits
            .iter()
            .map(|h| {
                let o = wf.head_name(h.owner);
                format!("{o}.{}", wf.sym(name))
            })
            .collect();
        for owner in generic_owners {
            let o = wf.head_name(owner);
            candidates.push(format!("{o}.{}", wf.sym(name)));
        }
        Err(LookupError::Ambiguous {
            name: wf.sym(name),
            candidates,
        })
    }

    /// A named method as a call candidate: non-generic (I5 owns parameters
    /// to determine), with a receiver slot whose self type matches `recv`.
    /// A foreign private method is R49's diagnostic and no candidate — but
    /// only once the method is known to be this increment's: a generic
    /// (I5-owned) method stays silent even when it is foreign-private.
    fn concrete_candidate(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        mdef: DefId,
        owner: DefId,
        recv: TyId,
        method_position: bool,
    ) -> Candidate {
        if self.arity(mdef) > 0 {
            return Candidate::Generic { owner };
        }
        // A trait's `Self` is supplied by the receiver, so a trait
        // method's container never withholds it; an impl's parameters
        // are I5's inference.
        if self.container_arity(mdef) > 0 && !self.container_is_trait(mdef) {
            return Candidate::Generic { owner };
        }
        let sig = self.fir.sigs.fn_sig(mdef);
        if sig == fors_fir::NO_FN_SIG {
            return Candidate::No;
        }
        let slot = self.fir.sigs.fn_sigs.receiver(sig);
        if slot == fors_fir::sig::NO_SLOT {
            // An associated function, not a method: only R45's qualified
            // form may call it, with every parameter an ordinary argument.
            // The "receiver" convention is the first parameter's own.
            if method_position {
                return Candidate::No;
            }
            // A generic signature is I5's even in qualified form: silence
            // before visibility, like the method path. Every parameter is
            // an ordinary argument here (no receiver slot to skip).
            if self.sig_mentions_any_var(sig) {
                return Candidate::Generic { owner };
            }
            if !self.method_visible(cx, owner, mdef) {
                let m = self.sym(self.method_name(owner, mdef));
                let h = self.head_name(owner);
                self.bemit_code(
                    cx,
                    node,
                    Code::N(11),
                    49,
                    format!("the method `{m}` of `{h}` is not `pub`"),
                );
                return Candidate::No;
            }
            let n = self.fir.sigs.fn_sigs.count(sig);
            let conv = if n > 0 {
                self.fir.sigs.fn_sigs.param(sig, 0).conv
            } else {
                Conv::Let
            };
            return Candidate::Hit(MethodHit {
                def: mdef,
                owner,
                trait_def: if self.fir.sigs.kind(owner) == SigKind::Trait {
                    owner
                } else {
                    fors_fir::NO_DEF
                },
                conv,
                recv_slot: 0,
                recv_ty: recv,
                receiver_is_arg: true,
            });
        }
        let p = self.fir.sigs.fn_sigs.param(sig, slot as usize);
        if self.fir.tys.tag(recv) != TyTag::Param && !self.self_matches(owner, p.ty, recv) {
            return Candidate::No;
        }
        // The result, raises and non-receiver parameters must be free of
        // parameters and projections: anything mentioning them needs
        // I5's instantiation (Self := receiver) or I6's normalization,
        // so a tier with no better answer stays silent. This check comes
        // before visibility: an I5-owned generic method is silent even
        // when foreign-private.
        if self.sig_mentions_var(sig, slot) {
            return Candidate::Generic { owner };
        }
        if !self.method_visible(cx, owner, mdef) {
            let m = self.sym(self.method_name(owner, mdef));
            let h = self.head_name(owner);
            self.bemit_code(
                cx,
                node,
                Code::N(11),
                49,
                format!("the method `{m}` of `{h}` is not `pub`"),
            );
            return Candidate::No;
        }
        Candidate::Hit(MethodHit {
            def: mdef,
            owner,
            trait_def: if self.fir.sigs.kind(owner) == SigKind::Trait {
                owner
            } else {
                fors_fir::NO_DEF
            },
            conv: p.conv,
            recv_slot: slot,
            recv_ty: recv,
            receiver_is_arg: false,
        })
    }

    /// Whether a method signature mentions a generic parameter or a
    /// projection outside its receiver slot (two levels: the type itself
    /// and a nominal/tuple's immediate arguments). Such a call needs
    /// instantiation or normalization and stays silent here.
    fn sig_mentions_var(&self, sig: fors_fir::sig::FnSigId, recv_slot: u8) -> bool {
        let n = self.fir.sigs.fn_sigs.count(sig);
        for i in 0..n {
            if i as u8 == recv_slot {
                continue;
            }
            if self.ty_mentions_var(self.fir.sigs.fn_sigs.param(sig, i).ty) {
                return true;
            }
        }
        let r = self.fir.sigs.fn_sigs.result(sig);
        if self.ty_mentions_var(r) {
            return true;
        }
        let e = self.fir.sigs.fn_sigs.raises(sig);
        e != NO_TY && self.ty_mentions_var(e)
    }

    /// Whether a signature mentions a generic parameter or a projection in
    /// ANY parameter (no receiver slot to skip), the result or `raises`.
    /// For R45's qualified associated functions, where the "receiver" is
    /// an ordinary first argument.
    fn sig_mentions_any_var(&self, sig: fors_fir::sig::FnSigId) -> bool {
        let n = self.fir.sigs.fn_sigs.count(sig);
        for i in 0..n {
            if self.ty_mentions_var(self.fir.sigs.fn_sigs.param(sig, i).ty) {
                return true;
            }
        }
        let r = self.fir.sigs.fn_sigs.result(sig);
        if self.ty_mentions_var(r) {
            return true;
        }
        let e = self.fir.sigs.fn_sigs.raises(sig);
        e != NO_TY && self.ty_mentions_var(e)
    }

    fn ty_mentions_var(&self, ty: TyId) -> bool {
        let bare = self.fir.tys.unqual(ty);
        match self.fir.tys.tag(bare) {
            TyTag::Param | TyTag::Proj | TyTag::Brand | TyTag::Fn | TyTag::Dyn => true,
            TyTag::Nominal | TyTag::Tuple => {
                let args = self.fir.tys.args(ArgsId(self.fir.tys.b(bare)));
                args.iter().any(|&a| {
                    let u = self.fir.tys.unqual(a);
                    matches!(
                        self.fir.tys.tag(u),
                        TyTag::Param | TyTag::Proj | TyTag::Brand | TyTag::Fn | TyTag::Dyn
                    )
                })
            }
            _ => false,
        }
    }

    /// Whether the method's declared self type accepts `recv`: identical
    /// heads, or the trait's own `Self` (which the receiver supplies).
    fn self_matches(&mut self, owner: DefId, self_ty: TyId, recv: TyId) -> bool {
        if self.fir.tys.unqual(self_ty) == self.fir.tys.unqual(recv) {
            return true;
        }
        self.fir.tys.tag(self_ty) == TyTag::Param
            && DefId(self.fir.tys.a(self_ty)) == owner
            && self.fir.sigs.kind(owner) == SigKind::Trait
    }

    fn container_is_trait(&self, mdef: DefId) -> bool {
        match self.defs.get(mdef).map(|r| r.parent) {
            Some(p) if p != fors_fir::NO_DEF => self.fir.sigs.kind(p) == SigKind::Trait,
            _ => false,
        }
    }

    /// Tier (2) contribution of one trait: every method it declares under
    /// `name` (required or provided alike) when the receiver implements
    /// the trait. A trait with an in-scope impl for the head that declares
    /// `name`, but which the argument-blind probe below cannot confirm,
    /// marks `saw_generic`: the miss is a trait-argument matching artifact
    /// (I5's), not an absence.
    fn trait_candidates(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
        trait_def: DefId,
        method_position: bool,
        tier: &mut Vec<Candidate>,
        saw_generic: &mut bool,
    ) {
        let want = self.fir.tys.intern_trait_ref(trait_def, NO_ARGS);
        if !matches!(self.holds(recv, want), Holds::Yes) {
            if self.scope_declares(cx, recv, trait_def, name) {
                *saw_generic = true;
            }
            return;
        }
        self.dep(trait_def);
        for (mname, mdef) in self.trait_method_defs(trait_def) {
            if mname != name {
                continue;
            }
            self.consider(cx, node, mdef, trait_def, recv, method_position, tier);
        }
    }

    /// Whether `trait_def` has an impl for `recv` in R43's module scope that
    /// declares `name` at all: then a missed probe is a trait-argument
    /// matching artifact, not an absence. Narrowed to impls whose self type
    /// UNIFIES with the receiver (the same one-way match `holds` uses): a
    /// same-head/different-args impl (e.g. the sole `Tagged` impl is for
    /// `Box2[i64]` while the receiver is `Box2[i32]`) must NOT suppress a
    /// concrete T0043.
    fn scope_declares(&mut self, cx: &BodyCx, recv: TyId, trait_def: DefId, name: Symbol) -> bool {
        if self.fir.tys.tag(recv) != TyTag::Nominal {
            return false;
        }
        let head = DefId(self.fir.tys.a(recv));
        let key = self.fir.tys.head_key(recv);
        if !self
            .trait_method_defs(trait_def)
            .iter()
            .any(|&(n, _)| n == name)
        {
            return false;
        }
        let head_mod = self.module_of(head);
        let cur_mod = self.module_of(cx.owner);
        let edges = self.edges_from(cur_mod);
        for r in 0..self.impls.len() {
            let row = self.impls.row(r as u32);
            if row.trait_def != trait_def {
                continue;
            }
            if self.fir.tys.head_key(row.self_ty) != key {
                continue;
            }
            let impl_mod = self.module_of(row.def);
            if impl_mod != head_mod && impl_mod != cur_mod && !edges.contains(&impl_mod) {
                continue;
            }
            let arity = self
                .fir
                .sigs
                .generics_store
                .count(self.fir.sigs.generics(row.def));
            let mut b = Binding::new(&[(row.def, arity as u16)]);
            if one_way_match(&mut self.fir.tys, row.self_ty, recv, &mut b) {
                return true;
            }
        }
        false
    }

    fn trait_method_defs(&self, trait_def: DefId) -> Vec<(Symbol, DefId)> {
        let ms = self.fir.sigs.members(trait_def);
        let n = self.fir.sigs.member_store.count(ms);
        (0..n)
            .map(|i| self.fir.sigs.member_store.get(ms, i))
            .filter(|m| m.kind == fors_fir::sig::MemberKind::Item)
            .map(|m| (m.name, m.def))
            .collect()
    }

    fn method_name(&self, owner: DefId, mdef: DefId) -> Symbol {
        self.impl_method_names(owner)
            .into_iter()
            .find(|&(_, d)| d == mdef)
            .map(|(n, _)| n)
            .unwrap_or(Symbol(0))
    }

    fn method_visible(&self, cx: &BodyCx, owner: DefId, mdef: DefId) -> bool {
        let ms = self.fir.sigs.members(owner);
        let n = self.fir.sigs.member_store.count(ms);
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind != fors_fir::sig::MemberKind::Item || m.def != mdef {
                continue;
            }
            return m.vis != fors_fir::sig::VIS_PRIVATE || self.same_module(owner, cx.owner);
        }
        true
    }

    fn module_of(&self, def: DefId) -> ModuleId {
        self.defs.get(def).map(|r| r.module).unwrap_or(ModuleId(0))
    }

    fn edges_from(&self, from: ModuleId) -> Vec<ModuleId> {
        let start = self.mod_edges.partition_point(|&(f, _)| f < from);
        let end = start + self.mod_edges[start..].partition_point(|&(f, _)| f == from);
        self.mod_edges[start..end]
            .iter()
            .map(|&(_, to)| to)
            .collect()
    }

    /// Records a resolved method on a call's callee node (D4): the owner
    /// head and the method's index in its member list, so lowering sees
    /// method calls where it used to see fields. Overwrites: on a 3+-
    /// segment greedy-path callee (`outer.inner.m()`) the intermediate
    /// field was already recorded first-wins by path resolution.
    pub fn record_method_member(&mut self, cx: &mut BodyCx, node: usize, hit: &MethodHit) {
        let ms = self.fir.sigs.members(hit.owner);
        let n = self.fir.sigs.member_store.count(ms);
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind == fors_fir::sig::MemberKind::Item && m.def == hit.def {
                cx.facts.overwrite_member(
                    node as u32,
                    MemberTarget::Field {
                        head: hit.owner,
                        index: i as u32,
                    },
                );
                return;
            }
        }
    }
}
