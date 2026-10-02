//! Calls, struct literals and variant construction (design §7.4).
//!
//! I3 lands the half of R38 with NOTHING to determine: a call to a
//! non-generic function, a struct literal of a non-generic struct, a
//! non-generic variant construction, and a call of a value of `fn` or
//! closure type. I4 adds [`Callee::Method`] (R43-R46) and, for a generic
//! callee, R12's bounds at the call WITHOUT typing it.
//!
//! I5 replaces that provisional path with R38 proper: [`Wf::type_call`]
//! runs steps (a)-(f) literally over a [`Binding`] that is a stack local
//! of the call and is dropped when it returns. I6 brought generic METHODS
//! into it and I10a the last surface it did not reach, R45's qualified
//! call on a GENERIC head (`Buffer.empty()`): no candidate is withheld
//! from R38 any more, and I10a also records the arguments R38 determined
//! on `BodyFacts` (D2), which is what lowering monomorphises
//! from. Projections on a bound head still need R20
//! (`normalise_proj`, I6): a parameter type whose every slot is bound but
//! whose substitution still fails is left silent and absorbing — the
//! difference between "undetermined" (T0039, this increment) and "not
//! normalised" (I6) is [`fors_fir::subst::first_unbound`].

use fors_fir::sig::{Conv, GParamKind, MemberKind, PayloadKind, SigKind, VIS_PRIVATE};
use fors_fir::subst::{Binding, MatchMode, first_unbound};
use fors_fir::ty::{ArgsId, FnTyId, NO_ARGS, NO_TY, TY_ERROR, TY_NEVER, TY_UNIT, TyId, TyTag};
use fors_index::Symbol;
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::target::{Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::{BodyCx, LocalKind, Slot};
use crate::diag::t;
use crate::facts::FactCallee;
use crate::methods::{LookupError, MethodHit};
use crate::tape::{Cause, Seg, UseKind};
use crate::wf::Wf;

/// What a call's callee turned out to be. `Undecided` is the honest state
/// for everything this increment does not type.
enum Callee {
    /// A function, generic or not: `arity > 0` makes its own parameters
    /// R38's slots.
    Fn(DefId),
    /// A tuple variant: `(enum def, member index, explicit head)`. The
    /// enum's own parameters are R38's slots; the head is the WRITTEN
    /// `Enum[args]` of R38(a)'s explicit form (`Opt2[i64].s(1)`), which
    /// seeds them, or [`NO_TY`] for a bare `Opt2.s(1)` / `some(1)`.
    Variant(DefId, usize, TyId),
    /// A value of `fn` or closure type (R7).
    Value(FnTyId),
    /// A resolved method (I4, R43-R46), with nothing to determine.
    Method(MethodHit),
    Undecided,
}

/// What R38 has to work with once the callee is known: the slots to
/// determine (the container's then the callee's own), the declared
/// parameter row, and the declared result and `raises`.
struct Shape {
    /// `(owner, own gparam count)`, in the order R38(a) names them. Empty
    /// for a callee with nothing to determine.
    owners: Vec<(DefId, u16)>,
    /// The declaration whose OWN parameters explicit `[...]` arguments
    /// supply (R38(a)).
    gdef: DefId,
    params: Vec<(Symbol, Conv, TyId)>,
    result: TyId,
    raises: TyId,
    /// Whether R39's argument-count rule applies: the callee's parameter
    /// row is the whole truth (not a method whose receiver was removed,
    /// and not a signature that failed to lower).
    counted: bool,
    /// Whether ch01 Rule 2's markers apply to the arguments. They apply
    /// to a call whose callee DECLARES conventions — a `fn`, a method, a
    /// value of `fn` type — and not to a variant construction, whose
    /// payload slots have no written convention at all (ch01 Rule 22d(i)
    /// lists "a variant payload" beside "a struct-literal field" as a
    /// discharge of its own, with no marker).
    marked: bool,
    /// I10b: slots R38(a) already knows, bound before step (a) runs —
    /// `(owner, ordinal, type)`. The one producer is a method found through a
    /// trait that declares parameters of its own: R38(b) binds the trait's
    /// `Self` from the receiver and nothing else, so `Conv[T]`'s `T`,
    /// `Index[I]`'s `I` and `Allocator[A]`'s `A` come from the impl that
    /// answered the lookup (R19: at most one matches), carried here as
    /// [`MethodHit::trait_args`].
    seed: Vec<(DefId, u16, TyId)>,
}

impl Shape {
    fn slots(&self) -> usize {
        self.owners.iter().map(|&(_, n)| n as usize).sum()
    }
}

/// One call's syntax, as R38 reads it: the call node, the explicit `[...]`
/// arguments, the receiver pair (declared self type, receiver type) when
/// the call is in method form, and the argument nodes.
#[derive(Clone, Copy)]
struct Site<'a> {
    node: usize,
    explicit: &'a [usize],
    receiver: Option<(TyId, TyId)>,
    args: &'a [usize],
}

impl Wf<'_> {
    /// A diagnostic whose code is another chapter's (R49 reports ch08 R11
    /// with ch08's own code).
    pub fn bemit_code(&mut self, cx: &mut BodyCx, node: usize, code: Code, site: u16, msg: String) {
        if cx.quiet > 0 {
            return;
        }
        if cx.mark_pub(node) {
            return;
        }
        let range = cx.range(node);
        let file = cx.file;
        self.sink.emit(file, range, code, site, msg);
        self.spoke_at(cx.home);
    }

    /// R38 for a call with zero parameters to determine, plus R36's
    /// handler and R37's named-argument rule.
    ///
    /// I3.5: records the decided type (D1) — the `?`-operand call in both
    /// judgements reaches `call_expr` directly, bypassing the
    /// `check`/`synth` wrappers, so this wrapper is the node's only
    /// record. The classification (D2) and argument conventions (D3) are
    /// recorded inside.
    pub fn call_expr(&mut self, cx: &mut BodyCx, node: usize, expected: Option<TyId>) -> TyId {
        let t = self.call_expr_inner(cx, node, expected);
        cx.facts.record(node as u32, t);
        t
    }

    fn call_expr_inner(&mut self, cx: &mut BodyCx, node: usize, expected: Option<TyId>) -> TyId {
        let kids = cx.kids(node);
        let Some(&callee_node) = kids.first() else {
            return TY_ERROR;
        };
        let handler = kids
            .iter()
            .copied()
            .find(|&c| cx.kind(c) == NodeKind::Handler);
        let args: Vec<usize> = kids
            .iter()
            .copied()
            .skip(1)
            .filter(|&c| cx.kind(c) != NodeKind::Handler)
            .collect();

        let try_node = cx.under_try.take();
        let (callee, explicit) = self.classify_callee(cx, callee_node);
        // I3.5 (D2): the classification, before the match moves it. I4
        // refines `Undecided` into method resolutions; I5 adds arguments.
        cx.facts.set_callee(
            node as u32,
            match &callee {
                Callee::Fn(def) => FactCallee::Direct(*def),
                Callee::Variant(en, i, _) => FactCallee::Variant {
                    en: *en,
                    index: *i as u32,
                },
                Callee::Value(_) => FactCallee::ValueFn,
                Callee::Method(hit) => FactCallee::Method {
                    def: hit.def,
                    owner: hit.owner,
                },
                Callee::Undecided => FactCallee::Undecided,
            },
        );
        let mut receiver: Option<(TyId, TyId)> = None;
        let shape = match callee {
            Callee::Fn(def) => {
                let sig = self.fir.sigs.fn_sig(def);
                if sig == fors_fir::NO_FN_SIG {
                    Shape {
                        owners: Vec::new(),
                        gdef: def,
                        params: Vec::new(),
                        result: TY_ERROR,
                        raises: NO_TY,
                        counted: false,
                        marked: true,
                        seed: Vec::new(),
                    }
                } else {
                    let n = self.fir.sigs.fn_sigs.count(sig);
                    let mut ps = Vec::with_capacity(n);
                    for i in 0..n {
                        let p = self.fir.sigs.fn_sigs.param(sig, i);
                        ps.push((p.name, p.conv, p.ty));
                    }
                    let arity = self.arity(def) as u16;
                    Shape {
                        owners: if arity == 0 {
                            Vec::new()
                        } else {
                            vec![(def, arity)]
                        },
                        gdef: def,
                        params: ps,
                        result: self.fir.sigs.fn_sigs.result(sig),
                        raises: self.fir.sigs.fn_sigs.raises(sig),
                        counted: true,
                        marked: true,
                        seed: Vec::new(),
                    }
                }
            }
            Callee::Variant(def, i, head) => {
                let ms = self.fir.sigs.members(def);
                let m = self.fir.sigs.member_store.get(ms, i);
                let xs = self.fir.tys.args(m.args).to_vec();
                let ps = xs.into_iter().map(|t| (Symbol(0), Conv::Sink, t)).collect();
                let arity = self.arity(def) as u16;
                let owners = if arity == 0 {
                    Vec::new()
                } else {
                    vec![(def, arity)]
                };
                let result = if arity == 0 {
                    self.fir.tys.nominal(def, NO_ARGS)
                } else {
                    // The enum applied to its OWN parameters: R38 then
                    // substitutes it, which is what makes `some(1)` with an
                    // expected `Option[u8]` bind `T := u8` in step (c).
                    let xs = self.own_args(def);
                    self.fir.tys.nominal_of(def, &xs)
                };
                // R38(a)'s explicit form on the enum: `Opt2[i64].s(1)` binds
                // the enum's slots from the written head before (c)/(d).
                let seed: Vec<(DefId, u16, TyId)> = if head == NO_TY || arity == 0 {
                    Vec::new()
                } else {
                    let bare = self.fir.tys.unqual(head);
                    self.fir
                        .tys
                        .args(fors_fir::ty::ArgsId(self.fir.tys.b(bare)))
                        .to_vec()
                        .into_iter()
                        .enumerate()
                        .filter(|&(_, t)| t != TY_ERROR && t != NO_TY)
                        .map(|(o, t)| (def, o as u16, t))
                        .collect()
                };
                Shape {
                    owners,
                    gdef: def,
                    params: ps,
                    result,
                    raises: NO_TY,
                    counted: true,
                    marked: false,
                    seed,
                }
            }
            Callee::Value(id) => {
                let (convs, tys) = self.fir.tys.fn_tys().params(id);
                let ps = convs
                    .iter()
                    .copied()
                    .zip(tys.iter().copied())
                    .map(|(c, t)| (Symbol(0), c, t))
                    .collect();
                Shape {
                    owners: Vec::new(),
                    gdef: fors_fir::NO_DEF,
                    params: ps,
                    result: self.fir.tys.fn_tys().result(id),
                    raises: self.fir.tys.fn_tys().raises(id),
                    counted: true,
                    marked: true,
                    seed: Vec::new(),
                }
            }
            Callee::Undecided => {
                self.undecided_args(cx, &args);
                for &e in &explicit {
                    cx.facts.record(e as u32, TY_ERROR);
                }
                self.handler(cx, handler, TY_ERROR, TY_ERROR, false);
                return TY_ERROR;
            }
            Callee::Method(hit) => {
                let sig = self.fir.sigs.fn_sig(hit.def);
                if sig == fors_fir::NO_FN_SIG {
                    Shape {
                        owners: Vec::new(),
                        gdef: hit.def,
                        params: Vec::new(),
                        result: TY_ERROR,
                        raises: NO_TY,
                        counted: false,
                        marked: true,
                        seed: Vec::new(),
                    }
                } else {
                    // I4 (D2/D3): the resolution lowering reads, recorded
                    // before the match below moves on to the arguments.
                    cx.facts.set_callee(
                        node as u32,
                        FactCallee::Method {
                            def: hit.def,
                            owner: hit.owner,
                        },
                    );
                    cx.facts.set_recv_conv(node as u32, hit.conv);
                    self.record_method_member(cx, callee_node, &hit);
                    let n = self.fir.sigs.fn_sigs.count(sig);
                    let mut ps = Vec::with_capacity(n);
                    for i in 0..n {
                        if !hit.receiver_is_arg && i as u8 == hit.recv_slot {
                            // R46: in method position the receiver is not
                            // an argument. (R45's qualified form keeps it
                            // as args[0], an ordinary first argument.)
                            continue;
                        }
                        let p = self.fir.sigs.fn_sigs.param(sig, i);
                        ps.push((p.name, p.conv, p.ty));
                    }
                    if hit.receiver_is_arg && hit.explicit_head {
                        // R38(a)+(b) for R45's EXPLICIT head: the head was
                        // written with its arguments, so the container's
                        // parameters come from it and not from step (c).
                        let own_self = self.fir.sigs.self_ty(hit.owner);
                        if own_self != NO_TY && own_self != TY_ERROR {
                            receiver = Some((own_self, hit.recv_ty));
                        }
                    }
                    if !hit.receiver_is_arg {
                        self.recv_use(cx, node, callee_node, &hit);
                        // R38(b): the receiver's type faces the declared
                        // self type. A method this increment resolves has
                        // nothing to determine, so the match binds nothing
                        // — but the pair is carried so step (b) is written
                        // where the design puts it.
                        let p = self.fir.sigs.fn_sigs.param(sig, hit.recv_slot as usize);
                        receiver = Some((p.ty, hit.recv_ty));
                    }
                    // I10b (R38(a) on the container): a trait with
                    // parameters of its own has no other source for them —
                    // the receiver binds `Self` (ordinal 0) and nothing
                    // else — so the impl that answered the lookup supplies
                    // them, at ordinals 1.. of the trait's generics.
                    let seed: Vec<(DefId, u16, TyId)> = if hit.trait_args == NO_ARGS {
                        Vec::new()
                    } else {
                        self.fir
                            .tys
                            .args(hit.trait_args)
                            .to_vec()
                            .into_iter()
                            .enumerate()
                            .filter(|&(_, t)| t != TY_ERROR && t != NO_TY)
                            .map(|(i, t)| (hit.owner, i as u16 + 1, t))
                            .collect()
                    };
                    Shape {
                        // I6 (design §7.4): the owner container's gparams
                        // (a trait's `Self` at ordinal 0) then the method's
                        // own. The receiver binds the container's in step
                        // (b), which is what makes a method returning
                        // `Self.A` or `I.Item` typable at all.
                        owners: self.call_owners(hit.owner, hit.def),
                        gdef: hit.def,
                        params: ps,
                        result: self.fir.sigs.fn_sigs.result(sig),
                        raises: self.fir.sigs.fn_sigs.raises(sig),
                        counted: true,
                        marked: true,
                        seed,
                    }
                }
            }
        };
        let (params, raises) = (shape.params.clone(), shape.raises);
        // I3.5 (D3, rest): the parameter convention each typed argument
        // was checked against, in order, one row per typed call (possibly
        // empty). Extra arguments (R39) are synthesised and carry no
        // convention.
        cx.facts.set_arg_convs(
            node as u32,
            params.iter().take(args.len()).map(|&(_, c, _)| c).collect(),
        );
        // R36: `call?` requires the callee to raise, and somewhere for the
        // error to go: the enclosing function's `raises` type, or the `fn`
        // type a CHECK-mode closure is checked against. (Whether the two
        // error types agree, or an `ErrorFrom` impl bridges them, is R12's
        // lookup: I4.)
        if let Some(t) = try_node {
            if raises == NO_TY {
                self.bemit(
                    cx,
                    t as usize,
                    36,
                    36,
                    "`?` applies only to a call of a `raises` function; this call does not raise"
                        .to_string(),
                );
            } else if cx.raises == NO_TY && cx.result != NO_TY {
                if cx.closures > 0 && cx.in_synth_closure() {
                    self.bemit(cx, t as usize, 35, 35, "`?` inside a closure in SYNTH mode: a closure raises only when checked against a `fn ... raises E` type".to_string());
                } else {
                    self.bemit(cx, t as usize, 36, 36, "`?` propagates an error, but the enclosing function does not declare `raises`; add `raises` or handle it with `else |e| { }`".to_string());
                }
            }
        }

        let site = Site {
            node,
            explicit: &explicit,
            receiver,
            args: &args,
        };
        let (result, raises) = self.type_call(cx, &site, &shape, expected);
        self.handler(cx, handler, result, raises, true);
        match expected {
            Some(w) => self.subsume(cx, node, result, w),
            None => result,
        }
    }

    // ------------------------------------------------- R38, steps (a)-(f)

    /// R38 over one call, literally (design §7.4). The [`Binding`] is a
    /// stack local: it is created here, never stored, and dropped when
    /// this returns, so a nested call in an argument recurses with its own
    /// (R38(f), "no variable survives the call").
    ///
    /// Returns the call's result type and its `raises` type, both fully
    /// substituted. Subsumption in CHECK mode is the caller's last step.
    fn type_call(
        &mut self,
        cx: &mut BodyCx,
        site: &Site,
        shape: &Shape,
        expected: Option<TyId>,
    ) -> (TyId, TyId) {
        self.live_bindings += 1;
        let out = self.type_call_inner(cx, site, shape, expected);
        self.live_bindings -= 1;
        out
    }

    fn type_call_inner(
        &mut self,
        cx: &mut BodyCx,
        site: &Site,
        shape: &Shape,
        expected: Option<TyId>,
    ) -> (TyId, TyId) {
        let Site {
            node,
            explicit,
            receiver,
            args,
        } = *site;
        let slots = shape.slots();
        let mut b = Binding::new(&shape.owners);
        self.bindings_created += 1;
        // I10b: the slots R38(a) already knows (see [`Shape::seed`]). Bound
        // before step (a) so an explicit `[...]` argument list, the receiver
        // and the arguments all see them.
        for &(owner, ord, t) in &shape.seed {
            b.bind(owner, ord, t);
        }
        // One root cause per call: once a slot or a comparison has been
        // reported, the rest of the procedure runs for its side effects
        // (every argument is still visited) and says nothing more.
        let mut bad = false;
        // Set when something this increment does not own left the call
        // undecidable: a projection R20 would normalise (I6), an explicit
        // argument that is not a plain type name, an unbound BRAND slot
        // (ch01 R15b's inference). The call is then absorbing and silent.
        let mut unowned = false;

        // (a) explicit `[...]` arguments: all of the callee's OWN
        // parameters, in order, each of the declared kind.
        if !explicit.is_empty() {
            let want = if shape.gdef == fors_fir::NO_DEF {
                0
            } else {
                self.arity(shape.gdef)
            };
            if want == 0 || want != explicit.len() {
                let f = self.head_name(shape.gdef);
                self.bemit(
                    cx,
                    node,
                    39,
                    39,
                    format!(
                        "`{f}` declares {want} generic argument(s), {} written",
                        explicit.len()
                    ),
                );
                bad = true;
            } else {
                for (o, &arg) in explicit.iter().enumerate() {
                    let t = self.explicit_arg(cx, arg, shape.gdef, o);
                    cx.facts.record(arg as u32, t);
                    if t == TY_ERROR || t == NO_TY {
                        unowned = true;
                        continue;
                    }
                    b.bind(shape.gdef, o as u16, t);
                }
            }
        }

        // (b) the receiver, matched one-way against the self parameter.
        if let Some((self_ty, recv_ty)) = receiver
            && slots > 0
            && recv_ty != TY_ERROR
            && recv_ty != NO_TY
        {
            self.match_n(self_ty, recv_ty, &mut b);
        }

        // (c) the expected type, in NoFail mode: brand positions are
        // skipped (R40) and a structural mismatch binds nothing and is not
        // yet an error — so the attempt runs on a copy and is adopted only
        // when it succeeds.
        if slots > 0
            && let Some(w) = expected
            && w != TY_ERROR
            && w != NO_TY
            && !b.is_complete()
        {
            let mut probe = b.clone();
            let ok = self.match_n_mode(shape.result, w, &mut probe, MatchMode::NoFail);
            if ok {
                b = probe;
            }
        }

        // (d) the arguments, left to right.
        let mut pending: Vec<(usize, usize, TyId)> = Vec::new();
        for (i, &arg) in args.iter().enumerate() {
            let Some(&(name, conv, p)) = shape.params.get(i) else {
                // R39's argument count is reported once, below; the extra
                // argument is still typed so nothing is left unvisited.
                let value = self.arg_value(cx, arg);
                if !self.check_only_form(cx, value) {
                    self.synth(cx, value);
                }
                continue;
            };
            self.named_label(cx, arg, name, i);
            let value = self.arg_value(cx, arg);
            // R41: a closure argument for a `fn`-shaped or callable
            // parameter takes its parameter types from that signature.
            if slots > 0 && cx.kind(value) == NodeKind::Closure {
                match self.closure_argument(cx, node, value, (i, conv, p), &mut b, shape.marked) {
                    Some(true) => continue,
                    Some(false) => {
                        // The signature needs R20's normalisation (I6).
                        // The closure is left unvisited rather than
                        // SYNTHesised into an R35 error it does not owe.
                        unowned = true;
                        continue;
                    }
                    None => {}
                }
            }
            match self.subst_now(p, &b) {
                Some(t) => {
                    cx.site(NodeKind::CallExpr, Slot::Argument);
                    self.check(cx, value, t);
                    self.arg_tape(cx, node, value, (i, conv, t), shape.marked);
                }
                None => {
                    if first_unbound(&self.fir.tys, p, &b).is_none() {
                        // Every slot is bound and the substitution still
                        // failed: R20. I6 owns it — `NoImpl` is T0012 at
                        // the site, an exhausted work budget is T0020.
                        if !bad && self.report_norm_failure(cx, value) {
                            bad = true;
                        } else {
                            unowned = true;
                        }
                        if !self.check_only_form(cx, value) {
                            self.synth(cx, value);
                        }
                        continue;
                    }
                    let s = self.synth(cx, value);
                    if s == TY_ERROR || s == NO_TY {
                        // The argument already failed (or is a form another
                        // increment leaves open): it binds nothing, and a
                        // slot it alone would have determined must not
                        // become a second, T0039 diagnostic for one cause
                        // (design §7.10: `TY_ERROR` absorbs).
                        unowned = true;
                        continue;
                    }
                    // R33: an argument of type `never` binds nothing.
                    if s != TY_NEVER {
                        self.match_n(p, s, &mut b);
                    }
                    pending.push((i, value, s));
                }
            }
        }
        // R39: the argument count is checked at the call.
        if shape.counted && args.len() != shape.params.len() && !bad {
            self.bemit(
                cx,
                node,
                39,
                39,
                format!(
                    "this call passes {} argument(s), but the callee declares {}",
                    args.len(),
                    shape.params.len()
                ),
            );
            bad = true;
        }

        // (e) every synthesised argument's parameter type, substituted in
        // full, compared once; then R12's bounds and constraint entries.
        for (i, value, s) in pending {
            let p = shape.params[i].2;
            match self.subst_now(p, &b) {
                Some(t) => {
                    if bad {
                        continue;
                    }
                    let got = self.subsume(cx, value, s, t);
                    if got == TY_ERROR && t != TY_ERROR {
                        bad = true;
                    } else {
                        self.arg_tape(cx, node, value, (i, shape.params[i].1, t), shape.marked);
                    }
                }
                None => match first_unbound(&self.fir.tys, p, &b) {
                    Some((_, _, true)) => unowned = true,
                    Some((owner, ord, false)) => {
                        if !bad && !unowned {
                            self.cannot_infer(cx, value, shape.gdef, owner, ord);
                            bad = true;
                        }
                    }
                    None => {
                        if !bad && self.report_norm_failure(cx, value) {
                            bad = true;
                        } else {
                            unowned = true;
                        }
                    }
                },
            }
        }
        // R39 over the WHOLE binding: a parameter that occurs in no
        // argument's type and not in the result (`fn make[T]() -> i32`, or
        // the `U` of `F: fn(..) -> U` with nothing to bind it) is still
        // "undetermined after Rule 38(d)". Reported at the call, naming the
        // first such slot. A brand slot is the one carve-out (see
        // [`Wf::unbound_slot`]).
        if !bad && !unowned {
            match self.unbound_slot(&shape.owners, &b) {
                Some((_, _, true)) => unowned = true,
                Some((owner, ord, false)) => {
                    self.cannot_infer(cx, node, shape.gdef, owner, ord);
                    bad = true;
                }
                None => {}
            }
        }
        if !bad && !unowned && slots > 0 {
            self.check_bounds(cx, node, shape.gdef, &shape.owners, &b);
        }

        // D2 (rest, I10a): the determined generic arguments, in R38(a)'s
        // order — the container's slots then the callee's own, exactly as
        // `shape.owners` lists them — each normalised (R20) so lowering
        // never sees a projection the checker already collapsed. Recorded
        // for every typed call, empty when there was nothing to determine.
        let determined: Vec<TyId> = b
            .slots()
            .to_vec()
            .into_iter()
            .map(|t| if t == NO_TY { NO_TY } else { self.normalise(t) })
            .collect();
        cx.facts.set_generic_args(node as u32, determined);

        // (f) the result, fully substituted.
        let raises = if shape.raises == NO_TY {
            NO_TY
        } else {
            self.subst_now(shape.raises, &b).unwrap_or(TY_ERROR)
        };
        if bad {
            return (TY_ERROR, raises);
        }
        match self.subst_now(shape.result, &b) {
            Some(t) => (t, raises),
            None => {
                match first_unbound(&self.fir.tys, shape.result, &b) {
                    Some((owner, ord, false)) if !unowned => {
                        self.cannot_infer(cx, node, shape.gdef, owner, ord)
                    }
                    None if !unowned => {
                        self.report_norm_failure(cx, node);
                    }
                    _ => {}
                }
                (TY_ERROR, raises)
            }
        }
    }

    /// The first slot of `b` still unbound once every argument has been
    /// visited, as `(owner, ordinal, is_brand)`.
    ///
    /// A BRAND slot is answered as `is_brand` and the caller leaves it
    /// silent rather than T0039: R40 binds a brand "only from a receiver
    /// or argument type", and the one source of a fresh brand that reaches
    /// a callee without an argument naming it — `one.alloc(Node { val: 1 })`,
    /// whose literal takes `A` from `alloc`'s receiver-bound `T` — needs an
    /// expected type this step does not have, so a T0039 here would be the
    /// checker's gap, not the writer's.
    fn unbound_slot(&self, owners: &[(DefId, u16)], b: &Binding) -> Option<(DefId, u16, bool)> {
        let (owner, ord) = b.first_unbound_slot()?;
        debug_assert!(owners.iter().any(|&(o, _)| o == owner));
        let g = self.fir.sigs.generics(owner);
        let is_brand = (ord as usize) < self.fir.sigs.generics_store.count(g)
            && self.fir.sigs.generics_store.param(g, ord as usize).kind == GParamKind::Brand;
        Some((owner, ord, is_brand))
    }

    /// R39's message: "cannot infer `T`; write `f[T](...)`".
    fn cannot_infer(&mut self, cx: &mut BodyCx, at: usize, gdef: DefId, owner: DefId, ord: u16) {
        let g = self.fir.sigs.generics(owner);
        let p = if (ord as usize) < self.fir.sigs.generics_store.count(g) {
            self.sym(self.fir.sigs.generics_store.param(g, ord as usize).name)
        } else {
            "_".to_string()
        };
        let f = self.head_name(gdef);
        self.bemit(
            cx,
            at,
            39,
            39,
            format!("cannot infer `{p}`; write `{f}[{p}](...)` with the argument given explicitly"),
        );
    }

    /// `subst_norm` over the call's binding, counted like every other
    /// substitution the body performs.
    fn subst_now(&mut self, ty: TyId, b: &Binding) -> Option<TyId> {
        if b.owner_count() == 0 {
            return Some(ty);
        }
        self.subst_calls += 1;
        self.subst_norm_n(ty, b)
    }

    /// R20's outcome for a substitution that failed although every slot it
    /// mentions is bound (design §7.5, §8's R20 row). `NoImpl` is T0012 at
    /// the site that asked; §17 amendment 2's exhausted work budget is
    /// T0020 asking for the chain to be split. `false` means the
    /// normalisation failed for a reason nothing reports (an error type, a
    /// trait not in this build), which is silence.
    fn report_norm_failure(&mut self, cx: &mut BodyCx, at: usize) -> bool {
        if self.take_budget_exceeded() {
            self.emit_budget(cx, at);
            return true;
        }
        if let Some((head, tref)) = self.take_no_impl() {
            self.emit_no_impl(cx, at, head, tref);
            return true;
        }
        false
    }

    /// ch01 Rule 2 at a call site (design §8's inherited-obligation row
    /// "ch01 R2 | convention markers at call sites (`&x`, `move x`,
    /// `&out x`); receiver exception | `call::conv_marker` (O0002)" — the
    /// half I5 left behind when it took R39's three T0039 sites).
    ///
    /// A non-`let` argument MUST carry its marker and a `let` one MUST
    /// NOT. The single exception is the RECEIVER of a method call, which
    /// never reaches here: `recv_use` records it instead (ch09 Rule 46).
    /// In the qualified form `T.m(move x)` the receiver IS an ordinary
    /// argument and is checked like any other, which is exactly what
    /// `qualified-call-sink-receiver-needs-move-rejected` asserts.
    fn conv_marker(
        &mut self,
        cx: &mut BodyCx,
        call: usize,
        value: usize,
        conv: Conv,
        ty: TyId,
        i: usize,
    ) {
        let arg = match arg_node(cx, call, i) {
            Some(a) => a,
            None => value,
        };
        let written = marker_of(cx, arg, value);
        let want = match conv {
            Conv::Let => None,
            Conv::Inout => Some(Marker::Inout),
            Conv::Set => Some(Marker::Set),
            Conv::Sink => Some(Marker::Move),
        };
        if written == want {
            return;
        }
        // R2: "`move` marks a place expression (binding or projection
        // path); an rvalue argument (literal, call result) to a `sink`
        // parameter carries no marker." A `Copyable` place is copied and
        // never moved (ch01 R4a's last sentence, ch09 R23), so there is
        // no move for `move` to mark either —
        // `bracket-instantiates-method-accepted` passes `a[1]` of type
        // `i32` to a `sink x: T`. The carve-out is `sink`'s alone: `&`
        // and `&out` mark a BORROW, which a `Copyable` type still needs.
        if conv == Conv::Sink
            && written.is_none()
            && (self.copyable(ty) || self.place_of(cx, value).is_none())
        {
            return;
        }
        let msg = match (want, written) {
            (Some(w), None) => format!(
                "the parameter is `{}`, so this argument must be written `{}` (ch01 R2)",
                conv_word(conv),
                w.spelled()
            ),
            (None, Some(g)) => format!(
                "the parameter is `let`, so this argument carries no marker; remove the `{}` \
                 (ch01 R2)",
                g.text()
            ),
            (Some(w), Some(g)) => format!(
                "the parameter is `{}`, so this argument must be written `{}`, not `{}` \
                 (ch01 R2)",
                conv_word(conv),
                w.spelled(),
                g.spelled()
            ),
            (None, None) => return,
        };
        self.bemit_code(cx, arg, Code::O(2), 39, msg);
    }

    /// The tape event an argument's convention produces (design §7.9),
    /// plus ch01 Rule 2's marker check at the same point. `slot` is the
    /// parameter the argument fills: its ordinal, convention and type.
    fn arg_tape(
        &mut self,
        cx: &mut BodyCx,
        call: usize,
        value: usize,
        (i, conv, ty): (usize, Conv, TyId),
        marked: bool,
    ) {
        if marked {
            self.conv_marker(cx, call, value, conv, ty, i);
        }
        let Some(p) = self.place_of(cx, value) else {
            return;
        };
        let kind = match conv {
            Conv::Let => {
                if self.copyable(ty) {
                    UseKind::Copy
                } else {
                    UseKind::Read
                }
            }
            Conv::Inout => UseKind::MutBorrow,
            Conv::Set => UseKind::OutBorrow,
            Conv::Sink => {
                if self.copyable(ty) {
                    UseKind::Copy
                } else {
                    UseKind::Move
                }
            }
        };
        cx.tape.push(
            value as u32,
            p,
            kind,
            Cause::Argument {
                call: call as u32,
                param: i as u16,
            },
        );
    }

    /// R41. `p` is the declared parameter type of a closure argument. When
    /// it is `fn`-shaped — written as a `fn` type, or a callable parameter
    /// `F: fn(...)` (R15) — and every PARAMETER type of that signature is
    /// complete under `b`, the closure is checked by R35; if the result is
    /// not complete the body is synthesised and the result matched one-way
    /// against it.
    ///
    /// `Some(true)`: R41 typed the argument. `Some(false)`: the signature
    /// mentions a projection on a BOUND head, which only R20's
    /// normalisation (I6) can complete — the closure is left alone, since
    /// SYNTHesising it would raise an R35 error that belongs to no rule
    /// (`map-sum-closure-checked-accepted`). `None`: R38(d) applies, and
    /// the closure is SYNTHed there and fails R35 as R41 says it should
    /// (`closure-before-its-type-source-rejected`).
    fn closure_argument(
        &mut self,
        cx: &mut BodyCx,
        call: usize,
        value: usize,
        (i, conv, p): (usize, Conv, TyId),
        b: &mut Binding,
        marked: bool,
    ) -> Option<bool> {
        let (slot, sig) = self.callable_signature(p, b)?;
        let id = FnTyId(self.fir.tys.a(self.fir.tys.unqual(sig)));
        let (convs, ptys) = {
            let (c, t) = self.fir.tys.fn_tys().params(id);
            (c.to_vec(), t.to_vec())
        };
        let mut ps: Vec<(Conv, TyId)> = Vec::with_capacity(ptys.len());
        for (k, &t) in ptys.iter().enumerate() {
            match self.subst_now(t, b) {
                Some(t) => ps.push((convs[k], t)),
                None => {
                    return if first_unbound(&self.fir.tys, t, b).is_some() {
                        // Genuinely incomplete: R38(d) applies.
                        None
                    } else {
                        // Complete but un-normalised: R20, which is I6's.
                        Some(false)
                    };
                }
            }
        }
        let declared_result = self.fir.tys.fn_tys().result(id);
        let declared_raises = self.fir.tys.fn_tys().raises(id);
        let raises = if declared_raises == NO_TY {
            NO_TY
        } else {
            self.subst_now(declared_raises, b).unwrap_or(TY_ERROR)
        };
        let want_result = self.subst_now(declared_result, b);
        let ft = match want_result {
            Some(r) => {
                let f = self.fir.tys.intern_fn_ty(&ps, r, raises, false);
                let want = self.fir.tys.fn_ty(f);
                cx.site(NodeKind::CallExpr, Slot::Argument);
                self.check(cx, value, want);
                want
            }
            None => {
                // The result is not complete: the body is SYNTHesised and
                // the declared result matched one-way against it. This is
                // the only place a result type flows out of a closure.
                let got = self.synth_closure_with(cx, value, &ps);
                let r = self.fir.tys.fn_tys().result(FnTyId(self.fir.tys.a(got)));
                if r != TY_ERROR && r != NO_TY && r != TY_NEVER {
                    self.match_n(declared_result, r, b);
                }
                got
            }
        };
        if let Some((owner, ord)) = slot {
            // A callable parameter is bound to the signature it accepted
            // (R41: "accepts a closure type, `fn` item or `fn` value of
            // that signature"), never to the closure's own row, so the
            // binding is the same whichever form the argument took.
            b.bind(owner, ord, ft);
        }
        self.arg_tape(cx, call, value, (i, conv, ft), marked);
        Some(true)
    }

    /// The `fn` signature a parameter type denotes for R41, and the slot
    /// it binds when it is a callable parameter (R15) rather than a
    /// written `fn` type.
    fn callable_signature(&mut self, p: TyId, b: &Binding) -> Option<(Option<(DefId, u16)>, TyId)> {
        let bare = self.fir.tys.unqual(p);
        if self.fir.tys.tag(bare) == TyTag::Fn {
            return Some((None, bare));
        }
        if self.fir.tys.tag(bare) != TyTag::Param {
            return None;
        }
        let owner = DefId(self.fir.tys.a(bare));
        let ord = self.fir.tys.b(bare) as u16;
        if !b.owns(owner) || b.slot(owner, ord) != NO_TY {
            return None;
        }
        let g = self.fir.sigs.generics(owner);
        if (ord as usize) >= self.fir.sigs.generics_store.count(g) {
            return None;
        }
        match self.fir.sigs.generics_store.param(g, ord as usize).kind {
            GParamKind::Callable { fn_ty } => Some((Some((owner, ord)), fn_ty)),
            _ => None,
        }
    }

    /// R12 at the call (R38(e)'s second half): every bound of every slot
    /// of the callee and its container, with the binding substituted in.
    /// This is the whole of what I4's provisional form of it did, now
    /// reached from inside the procedure that knows the binding. A
    /// generic struct literal (R34) reaches it with the struct as `gdef`.
    ///
    /// A CALLABLE parameter's "bound" is its signature (R15: "exactly one
    /// `fn_type`"; R41: it "accepts a closure type, `fn` item or `fn`
    /// value of that signature"). R38(d) binds `F` to whatever the argument
    /// synthesised — a closure, an item, or an `i32` — and nothing before
    /// this point has compared that with the signature, so the comparison
    /// is here, where every other bound is: the slot must be a function
    /// type equal, by R7/R10(b), to the signature with the binding
    /// substituted in. `U` of `F: fn(..) -> U` still unbound is R39's and
    /// was reported before this runs.
    fn check_bounds(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        gdef: DefId,
        owners: &[(DefId, u16)],
        b: &Binding,
    ) {
        use crate::wf::Holds;
        for &(owner, n) in owners {
            self.dep(owner);
            let g = self.fir.sigs.generics(owner);
            let count = self.fir.sigs.generics_store.count(g);
            let owner_is_trait = self.fir.sigs.kind(owner) == SigKind::Trait;
            for o in 0..(n as usize).min(count) {
                // A TRAIT container's ordinal 0 is its implicit `Self`, and
                // the only bound a `Self` carries is the trait itself (both
                // the prelude and lowering build it that way). That the
                // receiver implements the trait is a PRECONDITION of the
                // lookup that answered — `methods::trait_candidates` requires
                // `holds(recv, trait) == Yes`, and the rigid path requires
                // the trait to be among the receiver's declared bounds — so
                // re-deriving it here would only re-report what member lookup
                // already decided. §7.4(e)'s "bounds of the container" are
                // the bounds on the container's own PARAMETERS.
                if owner_is_trait && o == 0 {
                    continue;
                }
                let x = b.slot(owner, o as u16);
                if x == NO_TY || x == TY_ERROR {
                    continue;
                }
                if let GParamKind::Callable { fn_ty } =
                    self.fir.sigs.generics_store.param(g, o).kind
                {
                    let Some(want) = self.subst_now(fn_ty, b) else {
                        continue;
                    };
                    if self.fn_shape_eq(x, want) {
                        continue;
                    }
                    let got = self.show(x);
                    let sig = self.show(want);
                    let pname = self.sym(self.fir.sigs.generics_store.param(g, o).name);
                    let f = self.head_name(gdef);
                    self.bemit(
                        cx,
                        node,
                        41,
                        41,
                        format!(
                            "`{got}` is not a function of signature `{sig}`, which `{f}`'s callable parameter `{pname}` requires"
                        ),
                    );
                    return;
                }
                let bounds = {
                    let p = self.fir.sigs.generics_store.param(g, o);
                    self.fir.sigs.bounds.get(p.bounds).to_vec()
                };
                if bounds.is_empty() {
                    continue;
                }
                // I6: the subject goes through R20's normalisation first, so
                // `Vec[i32].Item` is `i32` here. What survives is NEUTRAL — a
                // projection on a rigid head — and `holds`'s `Proj` arm
                // answers it from the trait's `type A: ...` declaration plus
                // the constraint entries in scope (R16, R62). A subject that
                // merely CONTAINS a neutral projection (`Box2[I.Item]`) is
                // an ordinary R12 question: an impl matches it or not by
                // one-way match (a generic `impl[T] Tr for Box2[T]` binds
                // `T := I.Item`; a concrete `impl Tr for Box2[i64]` cannot,
                // R59), and the impl's own bounds on what it bound are
                // answered by the `Proj` arm. A brand has no bounds at all.
                let x = self.normalise(x);
                let x = self.fir.tys.unqual(x);
                if self.fir.tys.tag(x) == TyTag::Brand {
                    continue;
                }
                for want in bounds {
                    let Some(want) = self.subst_trait_ref(want, b) else {
                        continue;
                    };
                    if self.holds(x, want) != Holds::No {
                        continue;
                    }
                    let subject = self.show(x);
                    let (tdef, _) = self.fir.tys.trait_ref(want);
                    let tr = self.head_name(tdef);
                    let pname = self.sym(self.fir.sigs.generics_store.param(g, o).name);
                    let f = self.head_name(gdef);
                    self.bemit(
                        cx,
                        node,
                        12,
                        12,
                        format!(
                            "`{subject}` does not implement `{tr}`, which `{f}`'s parameter `{pname}` requires"
                        ),
                    );
                    return;
                }
            }
        }
        self.check_constraint_entries(cx, node, gdef, owners, b);
    }

    /// R62's USE side (design §7.4(e): "for each bound **and constraint
    /// entry** of the callee (and container)"). A constraint entry's subject
    /// is a projection written in the declaration's own terms (`I.Item`);
    /// at the call it goes through R20's substitute-and-normalise, which is
    /// what turns `I.Item` with `I := Circles` into `Circle`, and then every
    /// bound of the entry must hold for it.
    ///
    /// Takes no explicit generic arguments of its own (R38(a): "constraint
    /// entries take none"), so there is nothing to count here.
    fn check_constraint_entries(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        gdef: DefId,
        owners: &[(DefId, u16)],
        b: &Binding,
    ) {
        use crate::wf::Holds;
        for &(owner, _) in owners {
            let g = self.fir.sigs.generics(owner);
            let cl = self.fir.sigs.generics_store.constraints(g);
            let n = self.fir.sigs.constraints.count(cl);
            for i in 0..n {
                let (subject, bl) = self.fir.sigs.constraints.entry(cl, i);
                if subject == NO_TY || subject == TY_ERROR {
                    continue;
                }
                // The subject as the declaration wrote it, for the message.
                let written = self.show(subject);
                let Some(x) = self.subst_now(subject, b) else {
                    // A slot the entry mentions is still unbound (R39
                    // reported that) or the projection has no impl (the
                    // caller reports R20's `NoImpl`). Either way, silence.
                    continue;
                };
                let x = self.fir.tys.unqual(x);
                if x == TY_ERROR || x == NO_TY || self.fir.tys.tag(x) == TyTag::Brand {
                    continue;
                }
                let bounds = self.fir.sigs.bounds.get(bl).to_vec();
                for want in bounds {
                    let Some(want) = self.subst_trait_ref(want, b) else {
                        continue;
                    };
                    if self.holds(x, want) != Holds::No {
                        continue;
                    }
                    let subject = self.show(x);
                    let (tdef, _) = self.fir.tys.trait_ref(want);
                    let tr = self.head_name(tdef);
                    let f = self.head_name(gdef);
                    self.bemit(
                        cx,
                        node,
                        12,
                        62,
                        format!(
                            "`{subject}` does not implement `{tr}`, which `{f}`'s constraint entry `{written}: {tr}` requires"
                        ),
                    );
                    return;
                }
            }
        }
    }

    /// R37: a named argument's label MUST equal the parameter's name in
    /// that position.
    fn named_label(&mut self, cx: &mut BodyCx, arg: usize, param: Symbol, pos: usize) {
        if cx.kind(arg) != NodeKind::NamedArg || param == Symbol(0) {
            return;
        }
        let (a, b) = fors_resolve::paths::own_span(cx.f.tree, arg);
        let Some(i) = (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
            .find(|&i| cx.f.tokens.kinds[i] == fors_lex::TokenKind::Ident)
        else {
            return;
        };
        let label = self.names.intern(cx.f.tokens.text(i, cx.f.source));
        if label != param {
            let l = String::from_utf8_lossy(self.names.resolve(label)).into_owned();
            let p = String::from_utf8_lossy(self.names.resolve(param)).into_owned();
            self.bemit(cx, arg, 37, 37, format!("the argument in position {} is labelled `{l}`, but the parameter there is named `{p}`; arguments are never reordered", pos + 1));
        }
    }

    /// The expression inside an argument wrapper (`NamedArg`, `&x`,
    /// `&out x`).
    fn arg_value(&mut self, cx: &mut BodyCx, arg: usize) -> usize {
        match cx.kind(arg) {
            NodeKind::NamedArg | NodeKind::InoutArg | NodeKind::SetArg => {
                cx.f.tree.children(arg).next().unwrap_or(arg)
            }
            _ => arg,
        }
    }

    /// A form that is legal ONLY against an expected type, and so must
    /// not be SYNTHesised for a call or a literal this increment does not
    /// type: a closure (R35), a bare operator (R37), a `.variant` literal
    /// (R34) — and `none`, which R28's table puts in exactly the same
    /// position ("`none` takes its enum from the expected type"). A
    /// SYNTH of one of these would raise ITS rule's diagnostic for a call
    /// the checker simply has not reached.
    fn check_only_form(&mut self, cx: &mut BodyCx, node: usize) -> bool {
        match cx.kind(node) {
            NodeKind::Closure | NodeKind::BareOp | NodeKind::DotLit => true,
            NodeKind::NameExpr => matches!(
                cx.f.uses.target_of(node as u32),
                Some(ResolvedTarget::Entity(Entity::PreludeValue(s)))
                    if self.names.resolve(s) == b"none"
            ),
            _ => false,
        }
    }

    /// The arguments of a call this increment does not type. They are
    /// SYNTHESISED so nothing in the body is left unvisited — except the
    /// three forms that are legal only against an expected type
    /// (`closure`, `bare_op`, `dot_lit`), which would produce their own
    /// rule's diagnostic for a call the checker simply has not reached.
    fn undecided_args(&mut self, cx: &mut BodyCx, args: &[usize]) {
        for &a in args {
            let v = self.arg_value(cx, a);
            if self.check_only_form(cx, v) {
                continue;
            }
            self.synth(cx, v);
        }
    }

    /// R36: `call else |x| { ... }`. `x` has the call's `raises` type and
    /// the block is checked against the success type.
    fn handler(
        &mut self,
        cx: &mut BodyCx,
        handler: Option<usize>,
        success: TyId,
        raises: TyId,
        known: bool,
    ) {
        let Some(h) = handler else { return };
        if known && raises == NO_TY {
            // R36: the handler form requires a call of a `raises` function.
            self.bemit(cx, h, 36, 36, "an `else |e| { }` handler applies only to a call of a `raises` function; this call does not raise".to_string());
        }
        cx.bind(
            h as u32,
            if raises == NO_TY { TY_ERROR } else { raises },
            LocalKind::Value,
        );
        for b in cx.kids(h) {
            if cx.kind(b) == NodeKind::Block {
                cx.site(NodeKind::Handler, Slot::HandlerBlock);
                self.check(cx, b, success);
            }
        }
    }

    /// The callee, and the explicit `[...]` generic arguments written on
    /// it (R38(a)). The arguments are returned unlowered: R38(a) reads
    /// them by the callee's declared kinds, which are known only once the
    /// callee is.
    fn classify_callee(&mut self, cx: &mut BodyCx, node: usize) -> (Callee, Vec<usize>) {
        if cx.kind(node) == NodeKind::Bracket {
            let kids = cx.kids(node);
            let Some(&operand) = kids.first() else {
                return (Callee::Undecided, Vec::new());
            };
            // R47: a bracket on a path bound to a generic item instantiates.
            // `Type.name[..](..)` — R45's qualified form carrying R38(a)'s
            // explicit arguments on the FUNCTION segment — instantiates
            // too (I10a verification: `Layout.of[T]()` on a NON-generic
            // head was a silent `TY_ERROR`, because R47's test reads the
            // head's own arity and a monomorphic head has none; the
            // arguments are the associated function's, and R38(a) counts
            // them against `shape.gdef`, which is that function).
            if self.is_instantiation(cx, operand) || self.is_qualified_path(cx, operand) {
                let (c, nested) = self.classify_callee(cx, operand);
                if !nested.is_empty() {
                    return (Callee::Undecided, Vec::new());
                }
                return (c, kids[1..].to_vec());
            }
            self.synth(cx, node);
            return (Callee::Undecided, Vec::new());
        }
        (self.classify_head(cx, node), Vec::new())
    }

    /// Whether `node` is R45's qualified path `Type.name`: a `.`-path with
    /// a tail the resolver did not consume, whose head is a struct or enum
    /// declaration — exactly what [`Wf::qualified_callee`] accepts, read
    /// here without typing anything.
    fn is_qualified_path(&self, cx: &BodyCx, node: usize) -> bool {
        if cx.kind(node) != NodeKind::NameExpr
            || crate::member::path_segments(cx, node)
                <= crate::member::path_consumed(cx, node).max(1) as usize
        {
            return false;
        }
        match cx.f.uses.target_of(node as u32) {
            Some(ResolvedTarget::Entity(Entity::Item { file, decl })) => {
                let def = self.defs.def_of(file, decl);
                def != fors_fir::NO_DEF
                    && matches!(self.fir.sigs.kind(def), SigKind::Struct | SigKind::Enum)
            }
            _ => false,
        }
    }

    fn classify_head(&mut self, cx: &mut BodyCx, node: usize) -> Callee {
        match cx.kind(node) {
            NodeKind::NameExpr
                if crate::member::path_segments(cx, node)
                    > crate::member::path_consumed(cx, node).max(1) as usize =>
            {
                // A method call `x.m(..)` (R43/R44/R46) or a qualified call
                // `T.m(..)` (R45). The receiver prefix is still typed, so
                // its own errors are found and its tape events recorded;
                // the last segment resolves as a method, never a field.
                let n = crate::member::path_segments(cx, node);
                match self.path_head(cx, node) {
                    crate::member::PathHead::Value(_) => {
                        let recv = self.path_value(cx, node, n - 1, false);
                        if recv == TY_ERROR || recv == NO_TY {
                            return Callee::Undecided;
                        }
                        let Some(name) = self.segment_name(cx, node, n - 1) else {
                            return Callee::Undecided;
                        };
                        self.method_or_silent(cx, node, recv, name)
                    }
                    // R45's qualified form `Type.name`: the head is a type,
                    // not a value. The receiver arrives as args[0].
                    _ => self.qualified_callee(cx, node, n),
                }
            }
            NodeKind::NameExpr => match cx.f.uses.target_of(node as u32) {
                Some(ResolvedTarget::Entity(Entity::Item { file, decl })) => {
                    let def = self.defs.def_of(file, decl);
                    if def == fors_fir::NO_DEF
                        || !matches!(self.fir.sigs.kind(def), SigKind::Fn | SigKind::ExternFn)
                    {
                        return Callee::Undecided;
                    }
                    // R38's "parameters to determine": the container's, then
                    // the callee's own. A CONTAINER's parameters are a
                    // method's (R43's two tiers), which this increment
                    // leaves silent; the callee's own are R38's slots.
                    self.dep(def);
                    if self.container_arity(def) > 0 {
                        return Callee::Undecided;
                    }
                    Callee::Fn(def)
                }
                Some(ResolvedTarget::Entity(Entity::Variant { file, decl, index })) => {
                    let def = self.defs.def_of(file, decl);
                    self.dep(def);
                    if def == fors_fir::NO_DEF {
                        return Callee::Undecided;
                    }
                    match self.variant_slot(def, index) {
                        Some(i) => Callee::Variant(def, i, NO_TY),
                        None => {
                            // R34: a unit variant is named by its path and a
                            // struct-form one is a struct literal; calling
                            // either is an error, never silence.
                            let payload = self.variant_payload(def, index);
                            let h = self.head_name(def);
                            let n = crate::member::path_segments(cx, node);
                            let v = self
                                .segment_name(cx, node, n.saturating_sub(1))
                                .map(|s| self.sym(s))
                                .unwrap_or_default();
                            let msg = if payload == Some(PayloadKind::None) {
                                format!(
                                    "`{h}.{v}` is a unit variant and takes no payload; write `{h}.{v}`"
                                )
                            } else {
                                format!(
                                    "`{h}.{v}` is a struct-form variant; construct it with a struct literal"
                                )
                            };
                            self.bemit(cx, node, 34, 34, msg);
                            Callee::Undecided
                        }
                    }
                }
                // `some(x)`: `Option`'s tuple variant, whose `T` is R38's
                // to determine exactly like a user enum's.
                Some(ResolvedTarget::Entity(Entity::PreludeValue(sym))) => {
                    let def = self.prelude.option;
                    if def == fors_fir::NO_DEF || self.names.resolve(sym) != b"some" {
                        return Callee::Undecided;
                    }
                    self.dep(def);
                    match self.variant_named(def, sym) {
                        Some(i) => Callee::Variant(def, i, NO_TY),
                        None => Callee::Undecided,
                    }
                }
                Some(ResolvedTarget::Local { node: intro }) => {
                    let ty = cx.local(intro).map(|(t, _)| t).unwrap_or(TY_ERROR);
                    match self.callable_of(ty) {
                        Some(id) => Callee::Value(id),
                        None => Callee::Undecided,
                    }
                }
                _ => Callee::Undecided,
            },
            // A method call (R43-R46) or an instantiation (R47). The
            // receiver is synthesised, so its own errors are found and its
            // tape events recorded; R47's instantiation reading is I5's.
            NodeKind::FieldExpr => {
                let Some(operand) = cx.f.tree.children(node).next() else {
                    return Callee::Undecided;
                };
                // I10b: R45's qualified form whose HEAD carries R38(a)'s
                // explicit arguments — `Bag[i64].of(1)`. The operand is a
                // TYPE, so it is not synthesised and the receiver arrives
                // as args[0] exactly as in `Bag.of(1)`.
                if let Some(head) = self.instantiated_type(cx, operand) {
                    if head == TY_ERROR {
                        // R11 already reported the bracket.
                        return Callee::Undecided;
                    }
                    let Some(name) = self.field_name(cx, node) else {
                        return Callee::Undecided;
                    };
                    // R34 before R45, as in `qualified_callee`: `Opt2[i64].s(1)`
                    // and `Option[i64].some(1)` CONSTRUCT a variant.
                    let bare = self.fir.tys.unqual(head);
                    if self.fir.tys.tag(bare) == TyTag::Nominal {
                        let def = DefId(self.fir.tys.a(bare));
                        if self.fir.sigs.kind(def) == SigKind::Enum
                            && let Some(c) = self.variant_callee(cx, node, def, name, head)
                        {
                            return c;
                        }
                    }
                    return self.qualified_hit(cx, node, head, name, true);
                }
                let recv = self.synth(cx, operand);
                if recv == TY_ERROR || recv == NO_TY {
                    return Callee::Undecided;
                }
                let Some(name) = self.field_name(cx, node) else {
                    return Callee::Undecided;
                };
                self.method_or_silent(cx, node, recv, name)
            }
            NodeKind::Bracket => {
                self.synth(cx, node);
                Callee::Undecided
            }
            _ => {
                let ty = self.synth(cx, node);
                match self.callable_of(ty) {
                    Some(id) => Callee::Value(id),
                    None => Callee::Undecided,
                }
            }
        }
    }

    /// A method lookup that stays silent on what I4 does not own, and
    /// reports R43/R44 at the callee node otherwise.
    fn method_or_silent(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
    ) -> Callee {
        match self.lookup_method(cx, node, recv, name) {
            Ok(hit) => Callee::Method(hit),
            Err(LookupError::Silent) => Callee::Undecided,
            Err(LookupError::None { recv, name }) => {
                self.bemit(cx, node, 43, 43, format!("`{recv}` has no method `{name}`"));
                Callee::Undecided
            }
            Err(LookupError::Ambiguous { name, candidates }) => {
                let msg = format!(
                    "more than one candidate for the method `{name}` ({}); write the qualified form",
                    candidates
                        .iter()
                        .map(|c| format!("`{c}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                self.bemit(cx, node, 44, 44, msg);
                Callee::Undecided
            }
        }
    }

    /// R45's qualified `Type.name`: the head denotes a nominal type whose
    /// method is called with the receiver as an ordinary first argument.
    /// A trait head, whose `Self` is R38's inference, is still silent.
    ///
    /// I10a: a GENERIC head is no longer silent. `Buffer.empty()` used to
    /// leave the call node `TY_ERROR` with no diagnostic at all — the facts
    /// then carried no callee and lowering had to refuse the body — because
    /// this function bailed out on `arity > 0`. The head is instead applied
    /// to its OWN parameters, exactly as a generic variant construction is
    /// (see [`Callee::Variant`]'s shape), so R38 determines them from the
    /// expected type and the arguments and R39 reports when it cannot.
    fn qualified_callee(&mut self, cx: &mut BodyCx, node: usize, n: usize) -> Callee {
        let Some(target) = cx.f.uses.target_of(node as u32) else {
            return Callee::Undecided;
        };
        let head_def = match target {
            ResolvedTarget::Entity(Entity::Item { file, decl }) => self.defs.def_of(file, decl),
            // I10b (R45/R34): a PRELUDE head carrying a deferred tail.
            // `Option.some(1)` is R34's "a tuple variant is constructed by
            // calling its path" on the one enum no file declares, so the
            // resolver leaves `some` to ch08 R22 and this function refused
            // the head outright: the call node ended `TY_ERROR` with no
            // diagnostic, while a user enum's `Opt2.s(1)` — which the
            // resolver resolves whole — typed.
            ResolvedTarget::Entity(Entity::PreludeType(sym)) => match self.prelude.lookup(sym) {
                Some(fors_fir::prelude::PreludeEntity::Generic { def, .. }) => def,
                _ => return Callee::Undecided,
            },
            _ => return Callee::Undecided,
        };
        if head_def == fors_fir::NO_DEF
            || !matches!(
                self.fir.sigs.kind(head_def),
                SigKind::Struct | SigKind::Enum
            )
        {
            return Callee::Undecided;
        }
        self.dep(head_def);
        // R34 before R45: a tuple variant of this head is CONSTRUCTED, not
        // called as a method, and R38 determines the enum's parameters from
        // the payload and the expected type exactly as for `Opt2.s(1)`.
        if self.fir.sigs.kind(head_def) == SigKind::Enum
            && let Some(name) = self.segment_name(cx, node, n - 1)
            && let Some(c) = self.variant_callee(cx, node, head_def, name, NO_TY)
        {
            return c;
        }
        let recv = if self.arity(head_def) == 0 {
            self.fir.tys.nominal(head_def, NO_ARGS)
        } else {
            let xs = self.own_args(head_def);
            self.fir.tys.nominal_of(head_def, &xs)
        };
        let Some(name) = self.segment_name(cx, node, n - 1) else {
            return Callee::Undecided;
        };
        self.qualified_hit(cx, node, recv, name, false)
    }

    /// R45's lookup on a head type that is already known, and its R43/R44
    /// reporting. Shared by the plain qualified path (`Bag.of(1)`) and
    /// I10b's explicitly-instantiated one (`Bag[i64].of(1)`).
    fn qualified_hit(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv: TyId,
        name: Symbol,
        explicit_head: bool,
    ) -> Callee {
        match self.lookup_qualified(cx, node, recv, name) {
            Ok(mut hit) => {
                hit.explicit_head = explicit_head;
                Callee::Method(hit)
            }
            Err(LookupError::Silent) => Callee::Undecided,
            Err(LookupError::None { recv, name }) => {
                self.bemit(cx, node, 43, 43, format!("`{recv}` has no method `{name}`"));
                Callee::Undecided
            }
            Err(LookupError::Ambiguous { name, candidates }) => {
                let msg = format!(
                    "more than one candidate for the method `{name}` ({}); write the qualified form",
                    candidates
                        .iter()
                        .map(|c| format!("`{c}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                self.bemit(cx, node, 44, 44, msg);
                Callee::Undecided
            }
        }
    }

    /// R46's receiver use. The convention comes from the resolved method,
    /// never from a marker: `let` reads, `inout` borrows mutably, and
    /// `sink` moves a place receiver implicitly — explicit `(move x)`
    /// means exactly the same, and a `Copyable` receiver is copied.
    /// The event carries the consuming call and method for ch01's
    /// use-after-move diagnostic (R46's normative message is I8's).
    fn recv_use(&mut self, cx: &mut BodyCx, node: usize, callee: usize, hit: &MethodHit) {
        if cx.kind(callee) == NodeKind::FieldExpr {
            let Some(operand) = cx.f.tree.children(callee).next() else {
                return;
            };
            let Some(p) = self.place_of(cx, operand) else {
                return;
            };
            self.push_recv(cx, node, operand, p, hit);
            return;
        }
        self.recv_path_use(cx, node, callee, hit);
    }

    /// The receiver of a greedy-path call `x.m(..)`: the root local with
    /// the field segments between the consumed head and the method.
    /// `path_value` above typed the prefix without recording its read, so
    /// this is the receiver's only event.
    fn recv_path_use(&mut self, cx: &mut BodyCx, node: usize, callee: usize, hit: &MethodHit) {
        let Some(target) = cx.f.uses.target_of(callee as u32) else {
            return;
        };
        let root = match target {
            ResolvedTarget::Local { node: intro } => intro,
            _ => return,
        };
        let nsegs = crate::member::path_segments(cx, callee);
        let consumed = crate::member::path_consumed(cx, callee).max(1) as usize;
        if nsegs < 2 || consumed >= nsegs {
            return;
        }
        let mut segs = Vec::new();
        for k in consumed..nsegs - 1 {
            let Some(s) = self.segment_name(cx, callee, k) else {
                return;
            };
            segs.push(Seg::Field(s));
        }
        let p = cx.tape.intern(root, &segs);
        self.push_recv(cx, node, callee, p, hit);
    }

    fn push_recv(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        recv_node: usize,
        p: crate::tape::PlaceId,
        hit: &MethodHit,
    ) {
        let kind = match hit.conv {
            Conv::Let => {
                if self.copyable(hit.recv_ty) {
                    UseKind::Copy
                } else {
                    UseKind::Read
                }
            }
            Conv::Inout => UseKind::MutBorrow,
            Conv::Set => UseKind::OutBorrow,
            Conv::Sink => {
                if self.copyable(hit.recv_ty) {
                    UseKind::Copy
                } else {
                    UseKind::Move
                }
            }
        };
        let cause = match (hit.conv, kind) {
            (Conv::Sink, UseKind::Move) => Cause::ImplicitReceiver {
                call: node as u32,
                method: hit.def,
                owner: hit.owner,
            },
            _ => Cause::Explicit(recv_node as u32),
        };
        // R46: `(move x).m()` means exactly what `x.m()` means. The
        // receiver's own synthesis already recorded this place: a read of a
        // `FieldExpr` operand, and the explicit `Move` of a `(move x)`
        // wrapper. The receiver use below supersedes them, so events from
        // the receiver's own subtree for this place are withdrawn first —
        // scoped to the subtree, so an earlier call's events (which live
        // outside it) are left alone. For any other convention the explicit
        // move is kept (it still moves); only the redundant read goes.
        let implicit = matches!(cause, Cause::ImplicitReceiver { .. });
        let end = cx.f.tree.subtree_end(recv_node) as u32;
        cx.tape.events.retain(|e| {
            let own = e.place == p
                && (recv_node as u32) <= e.node
                && e.node < end
                && matches!(e.cause, Cause::Explicit(_));
            if !own {
                return true;
            }
            match e.kind {
                UseKind::Read | UseKind::Copy => false,
                UseKind::Move => !implicit,
                _ => true,
            }
        });
        cx.tape.push(recv_node as u32, p, kind, cause);
    }

    /// A declaration applied to its OWN generic parameters, each row of
    /// the kind R15 gave it: a brand parameter is a `Brand` row, not a
    /// `Param` one, so `Vec[T, A: brand]` is `Vec[Param(Vec,0),
    /// Brand(Param{Vec,1})]` and one-way matching it against a written
    /// `Vec[i32, a]` binds both slots.
    fn own_args(&mut self, def: DefId) -> Vec<TyId> {
        let g = self.fir.sigs.generics(def);
        let n = self.fir.sigs.generics_store.count(g);
        (0..n)
            .map(|o| match self.fir.sigs.generics_store.param(g, o).kind {
                GParamKind::Brand => self.fir.tys.brand_ty(fors_fir::ty::BrandRow::Param {
                    owner: def,
                    ordinal: o as u16,
                }),
                _ => self.fir.tys.param(def, o as u16),
            })
            .collect()
    }

    /// R38(a): one explicit generic argument, lowered by its slot's kind.
    fn explicit_arg(&mut self, cx: &mut BodyCx, node: usize, def: DefId, slot: usize) -> TyId {
        self.lower_generic_arg(cx, node, def, slot)
    }

    /// R34 for a variant named as a CALLEE on the enum's path (`Opt2.s(1)`,
    /// `Option.some(1)`, `Opt2[i64].s(1)`): a tuple variant is constructed
    /// and the enum's parameters are R38's slots (seeded from `head` when
    /// the head was written with its arguments); a unit or struct-form
    /// variant is never called, so naming one here is R34's error and the
    /// call is `Undecided` after it. `None` when `name` is no variant of
    /// `def` at all, so R45's lookup can answer.
    fn variant_callee(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        def: DefId,
        name: Symbol,
        head: TyId,
    ) -> Option<Callee> {
        let ms = self.fir.sigs.members(def);
        let i = (0..self.fir.sigs.member_store.count(ms)).find(|&i| {
            let m = self.fir.sigs.member_store.get(ms, i);
            m.kind == MemberKind::Variant && m.name == name
        })?;
        let payload = self.fir.sigs.member_store.get(ms, i).payload;
        if payload == PayloadKind::Tuple {
            return Some(Callee::Variant(def, i, head));
        }
        let h = self.head_name(def);
        let v = self.sym(name);
        let msg = if payload == PayloadKind::None {
            format!("`{h}.{v}` is a unit variant and takes no payload; write `{h}.{v}`")
        } else {
            format!("`{h}.{v}` is a struct-form variant; construct it with a struct literal")
        };
        self.bemit(cx, node, 34, 34, msg);
        Some(Callee::Undecided)
    }

    /// The member index of an enum variant by NAME (the prelude values
    /// `some`/`none` reach `Option`'s members this way).
    fn variant_named(&mut self, def: DefId, name: Symbol) -> Option<usize> {
        let ms = self.fir.sigs.members(def);
        (0..self.fir.sigs.member_store.count(ms)).find(|&i| {
            let m = self.fir.sigs.member_store.get(ms, i);
            m.kind == MemberKind::Variant && m.name == name && m.payload == PayloadKind::Tuple
        })
    }

    /// The member index of an enum's variant given the resolver's ordinal
    /// (which counts distinct variant NAMES, ch08's `Entity::Variant`).
    /// The payload kind of an enum's variant given the resolver's ordinal
    /// (`None` past the last variant).
    pub(crate) fn variant_payload(&mut self, def: DefId, ordinal: u32) -> Option<PayloadKind> {
        let ms = self.fir.sigs.members(def);
        let mut seen = 0u32;
        for i in 0..self.fir.sigs.member_store.count(ms) {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind != MemberKind::Variant {
                continue;
            }
            if seen == ordinal {
                return Some(m.payload);
            }
            seen += 1;
        }
        None
    }

    fn variant_slot(&mut self, def: DefId, ordinal: u32) -> Option<usize> {
        let ms = self.fir.sigs.members(def);
        let mut seen = 0u32;
        for i in 0..self.fir.sigs.member_store.count(ms) {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind != MemberKind::Variant {
                continue;
            }
            if seen == ordinal {
                return (m.payload == PayloadKind::Tuple).then_some(i);
            }
            seen += 1;
        }
        None
    }

    // --------------------------------------------------- struct literals

    /// R34: a struct literal names each field exactly once and nothing
    /// else, each visible, and is typed as a call whose parameters are the
    /// fields in written order.
    pub fn struct_lit(&mut self, cx: &mut BodyCx, node: usize, expected: Option<TyId>) -> TyId {
        let kids = cx.kids(node);
        let Some(&head) = kids.first() else {
            return TY_ERROR;
        };
        let inits: Vec<usize> = kids
            .iter()
            .copied()
            .filter(|&c| cx.kind(c) == NodeKind::FInit)
            .collect();
        let def = match self.struct_head(cx, head) {
            Some(d) => d,
            None => {
                for &i in &inits {
                    if let Some(v) = cx.f.tree.children(i).next()
                        && !self.check_only_form(cx, v)
                    {
                        self.synth(cx, v);
                    }
                }
                return TY_ERROR;
            }
        };
        self.dep(def);
        // R34/R38: a struct literal is a call whose parameters are the
        // fields. A GENERIC struct's own parameters are determined by the
        // same procedure, with step (c) — the expected type — doing the
        // work the written head cannot (`struct-literal-args-from-
        // expected-accepted`).
        let arity = self.arity(def) as u16;
        let owners: Vec<(DefId, u16)> = if arity == 0 {
            Vec::new()
        } else {
            vec![(def, arity)]
        };
        let mut b = Binding::new(&owners);
        self.live_bindings += 1;
        if arity > 0 {
            self.bindings_created += 1;
            let xs = self.own_args(def);
            let head_ty = self.fir.tys.nominal_of(def, &xs);
            if let Some(w) = expected
                && w != TY_ERROR
                && w != NO_TY
            {
                let mut probe = b.clone();
                if self.match_n_mode(head_ty, w, &mut probe, MatchMode::NoFail) {
                    b = probe;
                }
            }
        }
        let ms = self.fir.sigs.members(def);
        let count = self.fir.sigs.member_store.count(ms);
        let mut fields: Vec<(Symbol, u8, TyId)> = Vec::with_capacity(count);
        for i in 0..count {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind == MemberKind::Field {
                fields.push((m.name, m.vis, m.ty));
            }
        }
        let mut seen = vec![false; fields.len()];
        let mut bad = false;
        // A slot this increment does not determine (an unbound BRAND, see
        // `unbound_slot`; a projection R20 would normalise; a field whose
        // value already failed): the literal's type is left open rather
        // than guessed, and nothing is reported.
        let mut open = false;
        // R38(d)'s SYNTH half for the literal: a field whose type is not
        // yet complete is synthesised and the field type matched one-way
        // against the result, then compared in full at (e) once every
        // field has been visited (`Pair { a: 1u8, b: true }` is T0026 at
        // `true`, with or without an expected type).
        let mut pending: Vec<(usize, TyId, TyId)> = Vec::new();
        for &init in &inits {
            let Some(name) = self.field_name_of_init(cx, init) else {
                continue;
            };
            let value = cx.f.tree.children(init).next();
            match fields.iter().position(|&(n, ..)| n == name) {
                Some(k) => {
                    if seen[k] {
                        let f = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                        self.bemit(
                            cx,
                            init,
                            34,
                            34,
                            format!("the field `{f}` is written twice"),
                        );
                        bad = true;
                    }
                    seen[k] = true;
                    if fields[k].1 == VIS_PRIVATE && !self.same_module(def, cx.owner) {
                        let f = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                        let h = self.head_name(def);
                        self.bemit_code(
                            cx,
                            init,
                            Code::N(11),
                            49,
                            format!("the field `{f}` of `{h}` is not `pub`"),
                        );
                        bad = true;
                    }
                    if let Some(v) = value {
                        match self.subst_now(fields[k].2, &b) {
                            Some(ft) => {
                                cx.site(NodeKind::FInit, Slot::FieldInit);
                                self.check(cx, v, ft);
                                self.use_value(cx, v, ft, Cause::Explicit(node as u32));
                            }
                            None => {
                                if first_unbound(&self.fir.tys, fields[k].2, &b).is_none() {
                                    // Every slot bound and still not
                                    // complete: R20's normalisation (I6).
                                    open = true;
                                    if !self.check_only_form(cx, v) {
                                        self.synth(cx, v);
                                    }
                                    continue;
                                }
                                let s = self.synth(cx, v);
                                if s == TY_ERROR || s == NO_TY {
                                    open = true;
                                    continue;
                                }
                                // R33: a `never` field binds nothing.
                                if s != TY_NEVER {
                                    self.match_n(fields[k].2, s, &mut b);
                                }
                                pending.push((v, fields[k].2, s));
                            }
                        }
                    }
                }
                None => {
                    let f = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                    let h = self.head_name(def);
                    self.bemit(cx, init, 34, 34, format!("`{h}` has no field `{f}`"));
                    bad = true;
                    if let Some(v) = value {
                        self.synth(cx, v);
                    }
                }
            }
        }
        if !bad && let Some(k) = seen.iter().position(|&s| !s) {
            let f = String::from_utf8_lossy(self.names.resolve(fields[k].0)).into_owned();
            let h = self.head_name(def);
            let missing = seen.iter().filter(|&&s| !s).count();
            let more = if missing > 1 {
                format!(" (and {} more)", missing - 1)
            } else {
                String::new()
            };
            self.bemit(cx, node, 34, 34, format!("the struct literal of `{h}` does not name the field `{f}`{more}; a literal names each field exactly once"));
            bad = true;
        }
        // (e) for the literal: every synthesised field's type, substituted
        // in full, compared once; then every slot determined; then R12's
        // bounds on the struct's own parameters.
        for (v, fty, s) in pending {
            match self.subst_now(fty, &b) {
                Some(t) => {
                    if bad || open {
                        continue;
                    }
                    let got = self.subsume(cx, v, s, t);
                    if got == TY_ERROR && t != TY_ERROR {
                        bad = true;
                    } else {
                        self.use_value(cx, v, t, Cause::Explicit(node as u32));
                    }
                }
                None => match first_unbound(&self.fir.tys, fty, &b) {
                    Some((owner, ord, false)) => {
                        if !bad && !open {
                            self.cannot_infer(cx, v, def, owner, ord);
                            bad = true;
                        }
                    }
                    _ => open = true,
                },
            }
        }
        if !bad && !open && arity > 0 {
            match self.unbound_slot(&owners, &b) {
                Some((_, _, true)) => open = true,
                Some((owner, ord, false)) => {
                    self.cannot_infer(cx, node, def, owner, ord);
                    bad = true;
                }
                None => {}
            }
        }
        if !bad && !open && arity > 0 {
            self.check_bounds(cx, node, def, &owners, &b);
        }
        let ty = if bad || open {
            TY_ERROR
        } else if arity == 0 {
            self.fir.tys.nominal(def, NO_ARGS)
        } else {
            // R38(f) for the literal: the head with every slot substituted.
            let xs = self.own_args(def);
            let head_ty = self.fir.tys.nominal_of(def, &xs);
            match self.subst_now(head_ty, &b) {
                Some(t) => t,
                None => TY_ERROR,
            }
        };
        // D2/D3: a struct literal is typed as a call whose parameters are
        // the fields in written order. It is not a function call, so the
        // callee marks visited-but-not-a-call; each field init checks like
        // a `let` value.
        cx.facts.set_callee(node as u32, FactCallee::Undecided);
        cx.facts.set_arg_convs(
            node as u32,
            inits
                .iter()
                .filter(|&&i| cx.f.tree.children(i).next().is_some())
                .map(|_| Conv::Let)
                .collect(),
        );
        // D2 (rest, I10a): a generic struct's determined arguments, in its
        // own parameter order; empty for a non-generic struct.
        let determined: Vec<TyId> = b
            .slots()
            .to_vec()
            .into_iter()
            .map(|t| if t == NO_TY { NO_TY } else { self.normalise(t) })
            .collect();
        cx.facts.set_generic_args(node as u32, determined);
        // R38's "nothing survives the call": the literal's `Binding` dies
        // here, before the result is handed back.
        self.live_bindings -= 1;
        match expected {
            Some(w) => self.subsume(cx, node, ty, w),
            None => ty,
        }
    }

    /// The struct a literal's head names, if this increment can decide it.
    fn struct_head(&mut self, cx: &mut BodyCx, head: usize) -> Option<DefId> {
        if cx.kind(head) != NodeKind::NameExpr {
            return None;
        }
        match cx.f.uses.target_of(head as u32)? {
            ResolvedTarget::Entity(Entity::Item { file, decl }) => {
                let def = self.defs.def_of(file, decl);
                (def != fors_fir::NO_DEF && self.fir.sigs.kind(def) == SigKind::Struct)
                    .then_some(def)
            }
            // I10b (R34): `return Self { v: v };` inside an impl. ch09 is
            // silent on the head's spelling — R34 says a struct literal names
            // "the struct"'s fields and ch07 writes a path — so `Self` reads
            // here exactly as it reads everywhere else in a body: the impl's
            // own self type. Before this the head resolved to no `Entity` at
            // all, the literal answered `TY_ERROR` and nothing was said.
            ResolvedTarget::Local { node: intro } => {
                let (snode, sty) = cx.lcx.self_binding()?;
                if intro != snode {
                    return None;
                }
                let bare = self.fir.tys.unqual(sty);
                if self.fir.tys.tag(bare) == TyTag::Nominal {
                    let def = DefId(self.fir.tys.a(bare));
                    if self.fir.sigs.kind(def) == SigKind::Struct {
                        return Some(def);
                    }
                }
                // I10b verification: `Self { .. }` inside a trait's default
                // body (a rigid `Self`) or an enum's impl names no struct,
                // and R34's literal "MUST name each field of the struct" —
                // reported, never absorbed.
                let shown = self.show(bare);
                self.bemit(
                    cx,
                    head,
                    34,
                    34,
                    format!("`Self` here is `{shown}`, not a struct, so a struct literal cannot name its fields"),
                );
                None
            }
            _ => None,
        }
    }

    fn field_name_of_init(&mut self, cx: &BodyCx, init: usize) -> Option<Symbol> {
        let (a, b) = fors_resolve::paths::own_span(cx.f.tree, init);
        let i = (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
            .find(|&i| cx.f.tokens.kinds[i] == fors_lex::TokenKind::Ident)?;
        Some(self.names.intern(cx.f.tokens.text(i, cx.f.source)))
    }

    // --------------------------------------------------- dot literals

    /// R34: `.v` names the expected enum's variant `v`.
    pub fn check_dot_lit(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        if want == TY_ERROR || want == NO_TY {
            return TY_ERROR;
        }
        let bare = self.fir.tys.unqual(want);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            let w = self.show(want);
            self.bemit(
                cx,
                node,
                34,
                34,
                format!("a `.variant` literal needs an enum type here; the expected type is `{w}`"),
            );
            return TY_ERROR;
        }
        let def = DefId(self.fir.tys.a(bare));
        self.dep(def);
        if self.fir.sigs.kind(def) != SigKind::Enum {
            let w = self.show(want);
            self.bemit(
                cx,
                node,
                34,
                34,
                format!("a `.variant` literal needs an enum type here; the expected type is `{w}`"),
            );
            return TY_ERROR;
        }
        let Some(name) = self.dot_name(cx, node) else {
            return TY_ERROR;
        };
        let ms = self.fir.sigs.members(def);
        for i in 0..self.fir.sigs.member_store.count(ms) {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind == MemberKind::Variant && m.name == name {
                return want;
            }
        }
        let v = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
        let h = self.head_name(def);
        self.bemit(cx, node, 34, 34, format!("`{h}` has no variant `{v}`"));
        TY_ERROR
    }

    fn dot_name(&mut self, cx: &BodyCx, node: usize) -> Option<Symbol> {
        let (a, b) = cx.f.tree.token_range(node);
        let i = (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
            .find(|&i| cx.f.tokens.kinds[i] == fors_lex::TokenKind::Ident)?;
        Some(self.names.intern(cx.f.tokens.text(i, cx.f.source)))
    }

    /// R28/R34: `none` and a unit variant take their enum from the expected
    /// type. Answers `None` when the path is not one of those, so the
    /// caller falls through to subsumption.
    pub fn check_prelude_value(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        want: TyId,
    ) -> Option<TyId> {
        let target = cx.f.uses.target_of(node as u32)?;
        // §7.10: `TY_ERROR` is absorbing. `none` has no type of its own
        // (R28/R38 take `Option`'s argument from the expected type), so an
        // expected type that failed to lower must leave it silent, not
        // send it to SYNTH where R39 would report a parameter the writer
        // never had a chance to supply.
        if (want == TY_ERROR || want == NO_TY)
            && matches!(
                target,
                ResolvedTarget::Entity(Entity::PreludeValue(s)) if self.names.resolve(s) == b"none"
            )
        {
            return Some(TY_ERROR);
        }
        let bare = self.fir.tys.unqual(want);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return None;
        }
        let head = DefId(self.fir.tys.a(bare));
        match target {
            ResolvedTarget::Entity(Entity::PreludeValue(sym)) => {
                let name = self.names.resolve(sym).to_vec();
                if name == b"none" && head == self.prelude.option {
                    Some(want)
                } else {
                    None
                }
            }
            ResolvedTarget::Entity(Entity::Variant { file, decl, index }) => {
                let def = self.defs.def_of(file, decl);
                if def != head {
                    return None;
                }
                // Only a UNIT variant takes its enum from the expected type;
                // a tuple variant named bare is R34's error, which SYNTH
                // reports (`path_head`).
                (self.variant_payload(def, index) == Some(PayloadKind::None)).then_some(want)
            }
            // `Option.none`: the resolver leaves the tail of a prelude head
            // to ch08 R22, so the path is the head plus one deferred
            // segment. A unit variant of that enum takes the expected type
            // exactly as `none` does; anything else subsumes as before.
            ResolvedTarget::Entity(Entity::PreludeType(sym)) => {
                let def = match self.prelude.lookup(sym) {
                    Some(fors_fir::prelude::PreludeEntity::Generic { def, .. }) => def,
                    _ => return None,
                };
                if def != head || self.fir.sigs.kind(def) != SigKind::Enum {
                    return None;
                }
                let n = crate::member::path_segments(cx, node);
                if n != crate::member::path_consumed(cx, node).max(1) as usize + 1 {
                    return None;
                }
                let name = self.segment_name(cx, node, n - 1)?;
                let ms = self.fir.sigs.members(def);
                let unit = (0..self.fir.sigs.member_store.count(ms)).any(|i| {
                    let m = self.fir.sigs.member_store.get(ms, i);
                    m.kind == MemberKind::Variant
                        && m.name == name
                        && m.payload == PayloadKind::None
                });
                unit.then_some(want)
            }
            _ => None,
        }
    }

    /// Unused in I3 but part of the tape's vocabulary: the unit type a call
    /// with no result yields.
    pub fn unit(&self) -> TyId {
        TY_UNIT
    }

    /// `t` for a code number, re-exported for the body modules.
    pub fn tcode(n: u16) -> Code {
        t(n)
    }
}

/// The three convention markers ch01 Rule 2 spells out.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Marker {
    Inout,
    Set,
    Move,
}

impl Marker {
    fn text(self) -> &'static str {
        match self {
            Marker::Inout => "&",
            Marker::Set => "&out",
            Marker::Move => "move",
        }
    }

    /// The marker on an argument, as ch01 Rule 2 spells it.
    fn spelled(self) -> &'static str {
        match self {
            Marker::Inout => "&x",
            Marker::Set => "&out x",
            Marker::Move => "move x",
        }
    }
}

fn conv_word(c: Conv) -> &'static str {
    match c {
        Conv::Let => "let",
        Conv::Inout => "inout",
        Conv::Sink => "sink",
        Conv::Set => "set",
    }
}

/// The marker a call site wrote on one argument, if any. `&x`/`&out x`
/// are their own nodes (possibly inside a `NamedArg`); `move x` is a
/// unary expression and so is the argument's value itself.
fn marker_of(cx: &BodyCx, arg: usize, value: usize) -> Option<Marker> {
    let outer = if cx.kind(arg) == NodeKind::NamedArg {
        cx.f.tree.children(arg).next().unwrap_or(arg)
    } else {
        arg
    };
    for n in [outer, value] {
        match cx.kind(n) {
            NodeKind::InoutArg => return Some(Marker::Inout),
            NodeKind::SetArg => return Some(Marker::Set),
            NodeKind::UnaryExpr if crate::body::own_first(cx, n) == Some(TokenKind::KwMove) => {
                return Some(Marker::Move);
            }
            _ => {}
        }
    }
    None
}

/// The `i`th written argument of a call, as `call_expr_inner` counts them
/// (the callee is child 0 and a `Handler` is not an argument).
fn arg_node(cx: &BodyCx, call: usize, i: usize) -> Option<usize> {
    if cx.kind(call) != NodeKind::CallExpr {
        return None;
    }
    cx.f.tree
        .children(call)
        .skip(1)
        .filter(|&c| cx.f.tree.kinds[c] != NodeKind::Handler)
        .nth(i)
}

/// R38's "nothing survives the call": a `Binding` is a stack local of
/// [`Wf::type_call`] (and of the struct-literal form of the same
/// procedure). `Wf::live_bindings` counts the ones on the stack right
/// now, and `body.rs` asserts it is zero at every statement boundary —
/// the design's one-line statement that no inference state leaks.
pub const BINDINGS_LIVE_AT_A_STATEMENT_BOUNDARY: u32 = 0;

/// Kept so the `ArgsId`/`FnTyId` imports above stay meaningful to a reader
/// of this module's signature surface.
const _: Option<ArgsId> = None;
