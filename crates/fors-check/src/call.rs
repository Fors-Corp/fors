//! Calls, struct literals and variant construction (design §7.4).
//!
//! I3 lands the half of R38 with NOTHING to determine: a call to a
//! non-generic function, a struct literal of a non-generic struct, a
//! non-generic variant construction, and a call of a value of `fn` or
//! closure type. Every other callee is [`Callee::Undecided`]: silent,
//! absorbing, and left to I4 (methods) and I5 (generic calls).

use fors_fir::sig::{Conv, MemberKind, PayloadKind, SigKind, VIS_PRIVATE};
use fors_fir::ty::{ArgsId, FnTyId, NO_ARGS, NO_TY, TY_ERROR, TY_UNIT, TyId, TyTag};
use fors_index::Symbol;
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_resolve::target::{Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::{BodyCx, LocalKind, Slot};
use crate::diag::t;
use crate::tape::{Cause, UseKind};
use crate::wf::Wf;

/// What a call's callee turned out to be. `Undecided` is the honest state
/// for everything this increment does not type.
enum Callee {
    /// A function with no parameters to determine.
    Fn(DefId),
    /// A tuple variant of a non-generic enum: `(enum def, member index)`.
    Variant(DefId, usize),
    /// A value of `fn` or closure type (R7).
    Value(FnTyId),
    Undecided,
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
    pub fn call_expr(&mut self, cx: &mut BodyCx, node: usize, expected: Option<TyId>) -> TyId {
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
        let callee = self.classify_callee(cx, callee_node);
        let (params, result, raises) = match callee {
            Callee::Fn(def) => {
                let sig = self.fir.sigs.fn_sig(def);
                if sig == fors_fir::NO_FN_SIG {
                    (Vec::new(), TY_ERROR, NO_TY)
                } else {
                    let n = self.fir.sigs.fn_sigs.count(sig);
                    let mut ps = Vec::with_capacity(n);
                    for i in 0..n {
                        let p = self.fir.sigs.fn_sigs.param(sig, i);
                        ps.push((p.name, p.conv, p.ty));
                    }
                    (
                        ps,
                        self.fir.sigs.fn_sigs.result(sig),
                        self.fir.sigs.fn_sigs.raises(sig),
                    )
                }
            }
            Callee::Variant(def, i) => {
                let ms = self.fir.sigs.members(def);
                let m = self.fir.sigs.member_store.get(ms, i);
                let xs = self.fir.tys.args(m.args).to_vec();
                let ps = xs.into_iter().map(|t| (Symbol(0), Conv::Sink, t)).collect();
                (ps, self.fir.tys.nominal(def, NO_ARGS), NO_TY)
            }
            Callee::Value(id) => {
                let (convs, tys) = self.fir.tys.fn_tys().params(id);
                let ps = convs
                    .iter()
                    .copied()
                    .zip(tys.iter().copied())
                    .map(|(c, t)| (Symbol(0), c, t))
                    .collect();
                (
                    ps,
                    self.fir.tys.fn_tys().result(id),
                    self.fir.tys.fn_tys().raises(id),
                )
            }
            Callee::Undecided => {
                self.undecided_args(cx, &args);
                self.handler(cx, handler, TY_ERROR, TY_ERROR, false);
                return TY_ERROR;
            }
        };
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

        for (i, &arg) in args.iter().enumerate() {
            match params.get(i) {
                Some(&(name, conv, ty)) => {
                    self.named_label(cx, arg, name, i);
                    let value = self.arg_value(cx, arg);
                    cx.site(NodeKind::CallExpr, Slot::Argument);
                    self.check(cx, value, ty);
                    if let Some(p) = self.place_of(cx, value) {
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
                                call: node as u32,
                                param: i as u16,
                            },
                        );
                    }
                }
                // R39's argument-count rule is I5's gate; the extra
                // arguments are still typed, so nothing is left unvisited.
                None => {
                    let value = self.arg_value(cx, arg);
                    self.synth(cx, value);
                }
            }
        }
        self.handler(cx, handler, result, raises, true);
        match expected {
            Some(w) => self.subsume(cx, node, result, w),
            None => result,
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

    /// The arguments of a call this increment does not type. They are
    /// SYNTHESISED so nothing in the body is left unvisited — except the
    /// three forms that are legal only against an expected type
    /// (`closure`, `bare_op`, `dot_lit`), which would produce their own
    /// rule's diagnostic for a call the checker simply has not reached.
    fn undecided_args(&mut self, cx: &mut BodyCx, args: &[usize]) {
        for &a in args {
            let v = self.arg_value(cx, a);
            if matches!(
                cx.kind(v),
                NodeKind::Closure | NodeKind::BareOp | NodeKind::DotLit
            ) {
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

    fn classify_callee(&mut self, cx: &mut BodyCx, node: usize) -> Callee {
        match cx.kind(node) {
            NodeKind::NameExpr
                if crate::member::path_segments(cx, node)
                    > crate::member::path_consumed(cx, node).max(1) as usize =>
            {
                // A method call `x.m(..)` or a qualified call `T.m(..)`:
                // R43-R46 and R45 are I4's. The receiver is still typed, so
                // its own errors are found and its tape events recorded.
                let n = crate::member::path_segments(cx, node);
                self.path_value(cx, node, n - 1);
                Callee::Undecided
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
                    // the callee's own. Zero of both is this increment's.
                    self.dep(def);
                    if self.arity(def) > 0 || self.container_arity(def) > 0 {
                        return Callee::Undecided;
                    }
                    Callee::Fn(def)
                }
                Some(ResolvedTarget::Entity(Entity::Variant { file, decl, index })) => {
                    let def = self.defs.def_of(file, decl);
                    self.dep(def);
                    if def == fors_fir::NO_DEF || self.arity(def) > 0 {
                        return Callee::Undecided;
                    }
                    match self.variant_slot(def, index) {
                        Some(i) => Callee::Variant(def, i),
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
            // A method call (R43-R46) or an instantiation (R47): I4/I5's.
            // The receiver is still synthesised, so its own errors are
            // found and its tape events recorded.
            NodeKind::FieldExpr => {
                if let Some(operand) = cx.f.tree.children(node).next() {
                    self.synth(cx, operand);
                }
                Callee::Undecided
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

    /// The member index of an enum's variant given the resolver's ordinal
    /// (which counts distinct variant NAMES, ch08's `Entity::Variant`).
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
                        && !matches!(
                            cx.kind(v),
                            NodeKind::Closure | NodeKind::BareOp | NodeKind::DotLit
                        )
                    {
                        self.synth(cx, v);
                    }
                }
                return TY_ERROR;
            }
        };
        self.dep(def);
        if self.arity(def) > 0 {
            // Determining a struct's own parameters is R38's, which is I5's.
            for &i in &inits {
                if let Some(v) = cx.f.tree.children(i).next()
                    && !matches!(
                        cx.kind(v),
                        NodeKind::Closure | NodeKind::BareOp | NodeKind::DotLit
                    )
                {
                    self.synth(cx, v);
                }
            }
            return TY_ERROR;
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
                        cx.site(NodeKind::FInit, Slot::FieldInit);
                        self.check(cx, v, fields[k].2);
                        self.use_value(cx, v, fields[k].2, Cause::Explicit(node as u32));
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
        let ty = if bad {
            TY_ERROR
        } else {
            self.fir.tys.nominal(def, NO_ARGS)
        };
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
                let _ = index;
                Some(want)
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

/// R38's "nothing survives the call": a `Binding` is a stack local of
/// `type_call`. I3 creates none at all — every callee it types has zero
/// parameters to determine — and this constant records that so the
/// assertion I5 adds has something to compare against.
pub const BINDINGS_CREATED_IN_I3: usize = 0;

/// Kept so the `ArgsId`/`FnTyId` imports above stay meaningful to a reader
/// of this module's signature surface.
const _: Option<ArgsId> = None;
