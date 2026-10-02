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
use fors_fir::ty::{ArgsId, NO_ARGS, TraitRefId, TyId, TyTag};
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
    /// I10b (R38(a) on the container): the trait's OWN arguments — `Self`
    /// excluded — as the impl that answered supplies them, already
    /// substituted for this receiver. [`NO_ARGS`] for an inherent method and
    /// for a trait that declares no parameters of its own.
    ///
    /// R38(b) binds only `Self` from the receiver, so without this a call to
    /// a method of `Conv[T]`/`Index[I]`/`Allocator[A]` had no source for the
    /// trait's own slots and the call either reported T0039 or — before the
    /// lookup answered at all — absorbed into a silent `TY_ERROR`. R19 makes
    /// the source unambiguous: at most one impl matches a given
    /// (trait, self type), so its arguments ARE the trait's arguments here.
    pub trait_args: ArgsId,
    /// I10b (R38(a)/R45): the head was written with its generic arguments
    /// (`Bag[i64].of(1)`), so [`MethodHit::recv_ty`] is the INSTANTIATED head
    /// and R38 step (b) must bind the container's parameters from it. For a
    /// bare `Bag.of(1)` the head stands for its own parameters and step (c)
    /// does that work instead, so this stays `false`.
    pub explicit_head: bool,
}

/// A named method considered as a call candidate.
enum Candidate {
    /// Resolved: the call is typed, and R38 determines whatever parameters
    /// the method or its container still has.
    ///
    /// I10a removed the third arm, `Generic { owner }` — "a method with
    /// parameters to determine, which I5's inference owns, silent". I6 took
    /// the method case; this increment took the last one (R45's generic
    /// ASSOCIATED function, `Buffer.empty()`), so no candidate is withheld
    /// any more and a non-empty tier always has something to call.
    Hit(MethodHit),
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
        // I6: R20 first. A receiver whose type still mentions a projection
        // is normalised before anything is looked up on it, so `Vec[i32].Item`
        // is `i32` here and `Box2[I.Item]` is itself (neutral: R20 plus R59 —
        // nothing is learnt from what `I` might become).
        let recv = self.normalise(recv);
        let bare = self.fir.tys.unqual(recv);
        let cur_mod = self.module_of(cx.owner);
        let key = (cur_mod.0, bare, name, true, self.memo_scope(bare));
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
            // R43's two rigid cases: a parameter's candidate traits are its
            // bounds; a NEUTRAL projection's are the trait's declared bounds
            // for the associated type (R16) plus the constraint entries in
            // scope (R62) — which is exactly what `declared_bounds` answers,
            // and nothing from any impl (R57).
            TyTag::Param | TyTag::Proj => self.lookup_on_rigid(cx, node, bare, name),
            // Anything else has no method table. Silent.
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

    /// The scope component of the lookup memo's key: the declaration being
    /// typed when the answer can depend on it, `0` otherwise. R62's
    /// constraint entries live on a declaration's own generics, so two
    /// functions in one module can see different bounds on the SAME neutral
    /// projection — and a memo keyed by module alone would hand the second
    /// the first's answer. Only a receiver that mentions a projection is
    /// affected, so every other lookup keeps one entry per module.
    fn memo_scope(&self, recv: TyId) -> u32 {
        if self.fir.tys.tag(recv) == TyTag::Proj
            || fors_fir::impls::contains_proj(&self.fir.tys, recv)
        {
            self.cur_scope.0
        } else {
            0
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
        self.note_bucket(fors_fir::NO_DEF, key);
        let mut tier1: Vec<Candidate> = Vec::new();
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
                    NO_ARGS,
                    &mut tier1,
                );
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
            // I6: a receiver that still mentions a projection is NOT a
            // reason for silence any more. Normalisation ran before the
            // lookup, so what is left is neutral, and R59 says nothing is
            // learnt from what the parameter might become: the tiers above
            // are the whole table (`neutral-projection-does-not-match-
            // concrete-impl-rejected`).
            if saw_generic
                || self.prim_table_incomplete(recv, name)
                || self.prelude_head_table_incomplete(recv, name)
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
        let key = (cur_mod.0, bare, name, false, self.memo_scope(bare));
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

    /// R43's rigid cases (a `Param`, or a neutral `Proj`): the candidate
    /// traits are exactly the type's declared bounds.
    /// An empty tier is T0043 when every candidate trait is declared in this
    /// build (a `trait` item, whose member table is complete), and silence
    /// when a PRELUDE trait is among them: the prelude's opaque rows need not
    /// list every method yet (an `Iterator`'s adaptors live in `std`), so
    /// absence there proves nothing. Ambiguity still reports.
    fn lookup_on_rigid(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Result<MethodHit, LookupError> {
        let bounds = self.declared_bounds(recv);
        let mut tier: Vec<Candidate> = Vec::new();
        // A parameter whose bound did not RESOLVE (ch10 R2's std names are
        // `PreludeEntity::Opaque` in a build without `std`: `L: Allocator[A]`
        // under `needs { }`) carries no bound in the signature store at all,
        // so an empty table proves nothing about it. Pass A recorded that
        // as `GKind::Unknown`.
        let mut table_incomplete = self.fir.tys.tag(recv) == TyTag::Param
            && self
                .shapes
                .gkinds(DefId(self.fir.tys.a(recv)))
                .get(self.fir.tys.b(recv) as usize)
                == Some(&crate::lower::GKind::Unknown);
        for r in bounds {
            let trait_def = self.fir.tys.trait_ref(r).0;
            if trait_def == fors_fir::NO_DEF {
                table_incomplete = true;
                continue;
            }
            if self.prelude.trait_index(trait_def).is_some() {
                table_incomplete = true;
            }
            self.dep(trait_def);
            for (mname, mdef) in self.trait_method_defs(trait_def) {
                if mname != name {
                    continue;
                }
                // NO_ARGS, not the bound's own arguments: a rigid receiver
                // already determines the trait's parameters through R38
                // step (c) (the expected type), and the brand `A` of
                // `Allocator[A]` is interned differently in a `Self` bound
                // than in the body that writes `Block[A]` — seeding from the
                // bound would decide the slot with the wrong one and turn
                // `std/mem/alloc.fors`'s provided `create`/`deinit` into
                // T0026. The impl head is the only source this increment
                // solves from (see `impl_trait_ref`).
                self.consider(cx, node, mdef, trait_def, recv, true, NO_ARGS, &mut tier);
            }
        }
        if tier.is_empty() {
            if table_incomplete {
                return Err(LookupError::Silent);
            }
            // R43: for a rigid receiver the candidate traits are EXACTLY its
            // bounds (a parameter's declared ones; a neutral projection's
            // declared ones plus the constraint entries in scope), every one
            // of them a declaration in this build with a complete member
            // table. No candidate is T0043, not silence.
            return Err(LookupError::None {
                recv: self.show(recv),
                name: self.sym(name),
            });
        }
        Self::answer(self, name, tier)
    }

    /// Whether a trait declares generic parameters of its own beyond the
    /// implicit `Self` at ordinal 0 (`Index[I]` does, `Tagged` does not).
    fn trait_has_params(&self, trait_def: DefId) -> bool {
        self.fir
            .sigs
            .generics_store
            .count(self.fir.sigs.generics(trait_def))
            > 1
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

    /// ch10 R2's counterpart of [`Self::prim_table_incomplete`] for a
    /// prelude GENERIC head (`Arena`, `Own`, `Ref`, `Array`, ...). The
    /// language declares the head; its method surface is package `std`'s
    /// (`a.alloc(..)` on an `Arena`), and a build without `std` has none
    /// of it, so an empty tier proves nothing.
    ///
    /// The carve-out is by EVIDENCE, not by receiver, exactly as the
    /// primitive one is: silence holds only while the build has NO
    /// inherent impl for that head AND no inherent impl anywhere in the
    /// build declares a method of that NAME. Once the name is declared
    /// somewhere inherent, the writer plainly meant a method this build
    /// knows and the miss is real — which is what makes
    /// `no-auto-deref-own-rejected` (`peek` is `Builder`'s, reached
    /// through an `Own[Builder, A]`) still T0043.
    fn prelude_head_table_incomplete(&mut self, recv: TyId, name: Symbol) -> bool {
        if self.fir.tys.tag(recv) != TyTag::Nominal {
            return false;
        }
        let def = DefId(self.fir.tys.a(recv));
        if self.prelude.generic_index(def).is_none() {
            return false;
        }
        let key = self.fir.tys.head_key(recv);
        if !self.impls.inherent(key).is_empty() {
            return false;
        }
        let inherent: Vec<DefId> = (0..self.impls.len() as u32)
            .map(|r| self.impls.row(r))
            .filter(|row| row.inherent)
            .map(|row| row.def)
            .collect();
        !inherent
            .into_iter()
            .any(|d| self.impl_method_names(d).iter().any(|&(n, _)| n == name))
    }

    /// Sorts one named method into its tier. `trait_args` is the owner
    /// trait's own arguments for this receiver ([`NO_ARGS`] for an inherent
    /// impl and for a trait with no parameters of its own).
    fn consider(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        mdef: DefId,
        owner: DefId,
        recv: TyId,
        method_position: bool,
        trait_args: ArgsId,
        tier: &mut Vec<Candidate>,
    ) {
        match self.concrete_candidate(cx, node, mdef, owner, recv, method_position, trait_args) {
            Candidate::Hit(hit) => tier.push(Candidate::Hit(hit)),
            Candidate::No => {}
        }
    }

    /// One candidate, or R44's error. Inherent-before-trait is the only
    /// precedence; nothing is ever ranked. Since I10a no candidate is
    /// withheld for another increment, so a non-empty tier with no hit can
    /// only mean every same-name method was refused outright (an empty tier
    /// never reaches here) — and `Silent` stays the honest answer for it.
    fn answer(wf: &mut Wf, name: Symbol, tier: Vec<Candidate>) -> Result<MethodHit, LookupError> {
        let mut hits = Vec::new();
        for c in tier {
            match c {
                Candidate::Hit(hit) => hits.push(hit),
                Candidate::No => {}
            }
        }
        if hits.is_empty() {
            return Err(LookupError::Silent);
        }
        if hits.len() == 1 {
            let hit = hits.pop().unwrap();
            wf.dep(hit.def);
            wf.dep(hit.owner);
            if hit.trait_def != fors_fir::NO_DEF {
                wf.dep(hit.trait_def);
            }
            return Ok(hit);
        }
        let candidates: Vec<String> = hits
            .iter()
            .map(|h| {
                let o = wf.head_name(h.owner);
                // A parameterised trait's candidates are told apart by the
                // arguments the impl supplied (`Conv[i64].conv` beside
                // `Conv[u8].conv`), which is also R45's qualified spelling.
                let args = if h.trait_args == NO_ARGS {
                    String::new()
                } else {
                    let xs: Vec<String> = wf
                        .fir
                        .tys
                        .args(h.trait_args)
                        .to_vec()
                        .into_iter()
                        .map(|t| wf.show(t))
                        .collect();
                    format!("[{}]", xs.join(", "))
                };
                format!("{o}{args}.{}", wf.sym(name))
            })
            .collect();
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
        trait_args: ArgsId,
    ) -> Candidate {
        // I6 (design §7.4): a method with parameters to determine is no
        // longer withheld. Its container's gparams (a trait's `Self` at
        // ordinal 0) and then its own become R38's slots, which
        // `call.rs`'s `Shape::owners` carries; the receiver binds the
        // container's in step (b) and the arguments bind the rest. I10a
        // extends the same reading to R45's generic ASSOCIATED function
        // (`Buffer.empty()`), where there is no receiver to bind with and
        // step (c)'s expected type does the work instead.
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
            // I10a: a generic signature is no longer withheld here either.
            // This was I5's last `Candidate::Generic`, and it made
            // `Buffer.empty()` — an associated function of a GENERIC impl,
            // the single most common constructor shape in `std` — answer
            // `LookupError::Silent`, so the call node carried `TY_ERROR`
            // with no diagnostic and no callee fact. The call's own R38 has
            // everything it needs: `call_owners` puts the impl's parameters
            // and then the function's own in the `Binding`, step (c) binds
            // them from the expected type, and R39 reports when nothing
            // does. Every parameter is an ordinary argument here (no
            // receiver slot to skip).
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
                trait_args,
                explicit_head: false,
            });
        }
        let p = self.fir.sigs.fn_sigs.param(sig, slot as usize);
        if !self.self_accepts(mdef, owner, p.ty, recv) {
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
            trait_args,
            explicit_head: false,
        })
    }

    /// Whether the method's declared self type ACCEPTS `recv` — design
    /// §7.4 step (b), run here as a filter with the container's parameters
    /// free to bind. Identical types, the trait's own `Self` (which the
    /// receiver supplies), or a one-way match that binds the container's
    /// gparams: `impl[T] Foo for Vec[T] { fn get(let self: Vec[T]) }`
    /// accepts a `Vec[i32]` receiver. The binding is thrown away — the
    /// call rebuilds it in `type_call`, where it belongs.
    fn self_accepts(&mut self, mdef: DefId, owner: DefId, self_ty: TyId, recv: TyId) -> bool {
        if self.fir.tys.unqual(self_ty) == self.fir.tys.unqual(recv) {
            return true;
        }
        if self.fir.tys.tag(self_ty) == TyTag::Param
            && DefId(self.fir.tys.a(self_ty)) == owner
            && self.fir.sigs.kind(owner) == SigKind::Trait
        {
            return true;
        }
        // A RIGID receiver (a parameter, or a neutral projection) reaches a
        // method only through its bounds, where the self type is the trait's
        // own `Self` — the branch above. Anything else about it is R59's
        // "nothing is learnt", so the probe does not refuse it here; the
        // call's own step (b) decides.
        if matches!(self.fir.tys.tag(recv), TyTag::Param | TyTag::Proj) {
            return true;
        }
        let owners = self.call_owners(owner, mdef);
        if owners.is_empty() {
            return false;
        }
        let mut b = Binding::new(&owners);
        self.match_n(self_ty, recv, &mut b)
    }

    /// Design §7.4's "parameters to determine" for a method: the owner
    /// container's gparams (a trait's implicit `Self` is ordinal 0 of them)
    /// and then the method's own. `Binding` holds at most two owners, which
    /// is exactly this list.
    /// `owner` is the inherent impl or the trait the lookup answered from,
    /// which is where the container's parameters live. It is read from the
    /// SIGNATURE store rather than from the declaration table, because the
    /// prelude's traits (`Iterator`, `Index`, ...) have signatures and
    /// generics but no declaration row at all — `Self` is ordinal 0 of a
    /// trait's generics there exactly as lowering writes it for a user trait.
    pub(crate) fn call_owners(&self, owner: DefId, mdef: DefId) -> Vec<(DefId, u16)> {
        let mut out: Vec<(DefId, u16)> = Vec::new();
        if owner != fors_fir::NO_DEF {
            let n = self
                .fir
                .sigs
                .generics_store
                .count(self.fir.sigs.generics(owner));
            if n > 0 {
                out.push((owner, n as u16));
            }
        }
        let own = self.arity(mdef);
        if own > 0 {
            out.push((mdef, own as u16));
        }
        out
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
        let mut h = self.holds(recv, want);
        // I10b (R43 tier (2) for a PARAMETERISED trait). `holds` was asked
        // with no trait arguments, and for a trait that declares its own
        // (`Conv[T]`, `Index[I]`, `Allocator[A]`) that question can never be
        // answered `Yes`: every impl row carries arguments, so R12's compare
        // sees a length mismatch and says `No`. The lookup then turned the
        // miss into `LookupError::Silent` and the whole call absorbed — the
        // `s.conv()`/`b.conv()`/`self.free(move b)` family. R19 makes the
        // arguments recoverable: at most one impl matches a given
        // (trait, self type), so the impl head SUPPLIES them (R38(a)), and
        // R12 is then asked the complete question.
        // I10b verification: EVERY in-scope impl whose self type matches
        // supplies a candidate, not the first one. R19 forbids two impls
        // that UNIFY on (trait arguments, self type), so `impl Conv[i64]
        // for S` beside `impl Conv[u8] for S` is legal, and `s.conv()`
        // then has two candidates in tier (2) — R44's error, listing them —
        // never a silent choice of the earlier impl.
        let mut solved_args: Vec<ArgsId> = Vec::new();
        if h != Holds::Yes && self.trait_has_params(trait_def) {
            for solved in self.impl_trait_refs(cx, recv, trait_def) {
                if self.holds(recv, solved) == Holds::Yes {
                    h = Holds::Yes;
                    solved_args.push(self.fir.tys.trait_ref(solved).1);
                }
            }
        }
        if h != Holds::Yes {
            // `holds` was asked with NO trait arguments. For a trait WITH
            // parameters (`Index[I]`) a `No` may therefore be an artifact of
            // the missing arguments, and an impl in scope that declares the
            // name keeps the lookup silent. For a trait WITHOUT parameters
            // the question was complete and R12's `No` is the answer: the
            // impl that unified was refused by its own bounds (`impl[T:
            // Copyable] Tagged for Box2[T]` for a `Box2[I.Item]`), and the
            // receiver does not implement the trait, so it is no candidate
            // (R43). `Unknown` stays silent either way.
            if (h == Holds::Unknown || self.trait_has_params(trait_def))
                && self.scope_declares(cx, recv, trait_def, name)
            {
                *saw_generic = true;
            }
            return;
        }
        self.dep(trait_def);
        if solved_args.is_empty() {
            solved_args.push(NO_ARGS);
        }
        for trait_args in solved_args {
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
                    trait_args,
                    tier,
                );
            }
        }
    }

    /// R38(a) on the container: the trait arguments each in-scope impl for
    /// `recv` supplies, as complete `TraitRef`s to ask R12 with, in impl-row
    /// order and without duplicates.
    ///
    /// Same scan and same module scope as [`Self::scope_declares`] (ch08 R7,
    /// the defining, current or directly-used module), and the same one-way
    /// match `holds` uses, so an impl for a different argument list
    /// (`Tagged for Box2[i64]` against a `Box2[i32]` receiver) supplies
    /// nothing. R19 bounds the answer to one impl PER argument list, not
    /// one per trait: `impl Conv[i64] for S` and `impl Conv[u8] for S` do
    /// not unify and both answer, which is what makes `s.conv()` R44's
    /// ambiguity rather than a silent pick. Empty when no impl in scope
    /// matches.
    fn impl_trait_refs(&mut self, cx: &BodyCx, recv: TyId, trait_def: DefId) -> Vec<TraitRefId> {
        let mut out: Vec<TraitRefId> = Vec::new();
        if self.fir.tys.tag(recv) != TyTag::Nominal {
            return out;
        }
        let key = self.fir.tys.head_key(recv);
        let head_mod = self.module_of(DefId(self.fir.tys.a(recv)));
        let cur_mod = self.module_of(cx.owner);
        let edges = self.edges_from(cur_mod);
        for r in 0..self.impls.len() {
            let row = self.impls.row(r as u32);
            if row.trait_def != trait_def || row.trait_args == NO_ARGS {
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
            if !one_way_match(&mut self.fir.tys, row.self_ty, recv, &mut b) {
                continue;
            }
            let tref = self.fir.tys.intern_trait_ref(trait_def, row.trait_args);
            if let Some(t) = self.subst_trait_ref(tref, &b) {
                self.dep(row.def);
                if !out.contains(&t) {
                    out.push(t);
                }
            }
        }
        out
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
