//! Method-call resolution: ch09 R43-R46, I4's typing side (design §13).
//!
//! I4 owns the half that needs no trait search over projections and no
//! inference: the receiver's head is a concrete nominal type or a rigid
//! parameter, and every candidate method is non-generic (methods with
//! parameters to determine stay [`LookupError::Silent`] for I5).
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
//! or non-nominal receiver, a generic method, a qualified head that is
//! not a nominal type — answers [`LookupError::Silent`], never a
//! diagnostic, so pending rows stay quiet until their increment deletes
//! them.

use fors_fir::sig::{Conv, SigKind};
use fors_fir::ty::{ArgsId, NO_ARGS, NO_TY, TyId, TyTag};
use fors_index::Symbol;
use fors_index::diag::Code;
use fors_index::ids::{DefId, ModuleId};

use crate::body::BodyCx;
use crate::facts::MemberTarget;
use crate::wf::{Holds, Wf};

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
    /// a tier with no better answer stays silent rather than erroring.
    Generic,
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
    /// caller) for a call at `node` in method position.
    pub fn lookup_method(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Result<MethodHit, LookupError> {
        let bare = self.fir.tys.unqual(recv);
        match self.fir.tys.tag(bare) {
            TyTag::Nominal => self.lookup_on_head(cx, node, bare, name, true),
            TyTag::Param => self.lookup_on_param(cx, node, bare, name),
            // Projections are I6's; anything else has no method table this
            // increment owns. Silent.
            _ => Err(LookupError::Silent),
        }
    }

    /// Tier (1)+(2) for a concrete nominal receiver. `method_position`
    /// is false for R45's qualified form, where associated functions
    /// answer too and every parameter is an ordinary argument.
    fn lookup_on_head(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
        method_position: bool,
    ) -> Result<MethodHit, LookupError> {
        let head = DefId(self.fir.tys.a(recv));
        self.dep(head);
        let key = self.fir.tys.head_key(recv);
        let mut tier1 = Vec::new();
        let mut saw_generic = false;
        for r in self.impls.inherent(key) {
            let row = self.impls.row(r);
            self.dep(row.def);
            for (mname, mdef) in self.impl_method_names(row.def) {
                if mname != name {
                    continue;
                }
                self.consider(
                    cx,
                    node,
                    mdef,
                    row.def,
                    recv,
                    method_position,
                    &mut tier1,
                    &mut saw_generic,
                );
            }
        }
        if !tier1.is_empty() {
            return Self::answer(self, name, tier1);
        }
        let mut seen = Vec::new();
        let mut tier2 = Vec::new();
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
        let head_mod = self.module_of(head);
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
            if impl_mod != head_mod && impl_mod != cur_mod && !edges.contains(&impl_mod) {
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
            if saw_generic || self.recv_hides_projection(recv) {
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
    pub fn lookup_qualified(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Result<MethodHit, LookupError> {
        match self.lookup_on_head(cx, node, recv, name, false) {
            Ok(mut hit) => {
                hit.receiver_is_arg = true;
                Ok(hit)
            }
            Err(e) => Err(e),
        }
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
        let mut tier = Vec::new();
        let mut saw_generic = false;
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
                self.consider(
                    cx,
                    node,
                    mdef,
                    trait_def,
                    recv,
                    true,
                    &mut tier,
                    &mut saw_generic,
                );
            }
        }
        if tier.is_empty() {
            // Rigid silence: bound-trait declarations (especially the
            // prelude's opaque rows) need not list every method yet, so
            // an empty tier proves nothing. Ambiguity still reports.
            let _ = (saw_generic, recv);
            return Err(LookupError::Silent);
        }
        Self::answer(self, name, tier)
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
        tier: &mut Vec<MethodHit>,
        saw_generic: &mut bool,
    ) {
        match self.concrete_candidate(cx, node, mdef, owner, recv, method_position) {
            Candidate::Hit(hit) => tier.push(hit),
            Candidate::Generic => *saw_generic = true,
            Candidate::No => {}
        }
    }

    /// One candidate, or R44's error. Inherent-before-trait is the only
    /// precedence; nothing is ever ranked.
    fn answer(
        wf: &mut Wf,
        name: Symbol,
        mut tier: Vec<MethodHit>,
    ) -> Result<MethodHit, LookupError> {
        if tier.len() == 1 {
            let hit = tier.pop().unwrap();
            wf.dep(hit.def);
            wf.dep(hit.owner);
            if hit.trait_def != fors_fir::NO_DEF {
                wf.dep(hit.trait_def);
            }
            return Ok(hit);
        }
        let candidates = tier
            .iter()
            .map(|h| {
                let o = wf.head_name(h.owner);
                format!("{o}.{}", wf.sym(name))
            })
            .collect();
        Err(LookupError::Ambiguous {
            name: wf.sym(name),
            candidates,
        })
    }

    /// A named method as a call candidate: non-generic (I5 owns parameters
    /// to determine), with a receiver slot whose self type matches `recv`.
    /// A foreign private method is R49's diagnostic and no candidate.
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
            return Candidate::Generic;
        }
        // A trait's `Self` is supplied by the receiver, so a trait
        // method's container never withholds it; an impl's parameters
        // are I5's inference.
        if self.container_arity(mdef) > 0 && !self.container_is_trait(mdef) {
            return Candidate::Generic;
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
        // The result, raises and non-receiver parameters must be free of
        // parameters and projections: anything mentioning them needs
        // I5's instantiation (Self := receiver) or I6's normalization,
        // so a tier with no better answer stays silent.
        if self.sig_mentions_var(sig, slot) {
            return Candidate::Generic;
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
        tier: &mut Vec<MethodHit>,
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
            self.consider(
                cx,
                node,
                mdef,
                trait_def,
                recv,
                method_position,
                tier,
                saw_generic,
            );
        }
    }

    /// Whether `trait_def` has an impl for `recv`'s head in R43's module
    /// scope that declares `name` at all: then a missed probe is an
    /// argument-matching artifact, not an absence.
    fn scope_declares(&self, cx: &BodyCx, recv: TyId, trait_def: DefId, name: Symbol) -> bool {
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
            if impl_mod == head_mod || impl_mod == cur_mod || edges.contains(&impl_mod) {
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
    /// method calls where it used to see fields.
    pub fn record_method_member(&mut self, cx: &mut BodyCx, node: usize, hit: &MethodHit) {
        let ms = self.fir.sigs.members(hit.owner);
        let n = self.fir.sigs.member_store.count(ms);
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind == fors_fir::sig::MemberKind::Item && m.def == hit.def {
                cx.facts.set_member(
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
