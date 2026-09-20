//! Member access without scope lookup (design §7.7; ch09 R42, R45, R47,
//! R49). I3 owns the half that needs no trait search: a field of a struct
//! head, the built-in `len`, and R47's reading of a `bracket`.
//!
//! Method lookup (R43/R44's two tiers) is I4's; a method call here is
//! silent and absorbing, never a guess.

use fors_fir::sig::{MemberKind, SigKind, VIS_PRIVATE};
use fors_fir::subst::{Binding, subst_norm};
use fors_fir::ty::{ArgsId, FnTyId, NO_ARGS, NO_TY, PrimKind, TY_ERROR, TyId, TyTag};
use fors_index::Symbol;
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::target::{Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::{BodyCx, Slot};
use crate::wf::Wf;

impl Wf<'_> {
    /// R28: a `path` in expression position.
    ///
    /// ch07's `path` is greedy over `.ident`, so `x.f` and `Shape.dot` are
    /// ONE `NameExpr` node and the resolver records how many segments it
    /// accounted for (`consumed`). Every segment past that is a deferred
    /// member (ch08 R16/R22) and is this rule's — R42 for a field, R43/R45
    /// for anything else, which is I4's.
    pub fn name_expr(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let n = path_segments(cx, node);
        self.path_value(cx, node, n)
    }

    /// The value the first `upto` segments of a path denote. A call's
    /// callee asks for `upto = segments - 1`, because its last segment is
    /// the method or associated function (R43/R45), not a field.
    pub fn path_value(&mut self, cx: &mut BodyCx, node: usize, upto: usize) -> TyId {
        let consumed = path_consumed(cx, node).max(1) as usize;
        let head = self.path_head(cx, node);
        let mut ty = match head {
            PathHead::Value(t) => t,
            PathHead::NotAValue | PathHead::Silent => return TY_ERROR,
        };
        if upto <= consumed {
            if ty != TY_ERROR && ty != NO_TY {
                self.read_event(cx, node, ty);
            }
            return ty;
        }
        for k in consumed..upto {
            let Some(name) = self.segment_name(cx, node, k) else {
                return TY_ERROR;
            };
            ty = self.member_of(cx, node, ty, name);
            if ty == TY_ERROR {
                return TY_ERROR;
            }
        }
        self.read_event(cx, node, ty);
        ty
    }

    fn read_event(&mut self, cx: &mut BodyCx, node: usize, ty: TyId) {
        if let Some(p) = self.place_of(cx, node) {
            let k = if self.copyable(ty) {
                crate::tape::UseKind::Copy
            } else {
                crate::tape::UseKind::Read
            };
            cx.tape
                .push(node as u32, p, k, crate::tape::Cause::Explicit(node as u32));
        }
    }

    /// What the resolved prefix of a path denotes.
    pub fn path_head(&mut self, cx: &mut BodyCx, node: usize) -> PathHead {
        let Some(target) = cx.f.uses.target_of(node as u32) else {
            return PathHead::Silent;
        };
        match target {
            ResolvedTarget::Local { node: intro } => match cx.local(intro) {
                Some((t, _)) => PathHead::Value(t),
                None => PathHead::Silent,
            },
            ResolvedTarget::Entity(Entity::Item { file, decl }) => {
                let def = self.defs.def_of(file, decl);
                if def == fors_fir::NO_DEF {
                    return PathHead::Silent;
                }
                self.dep(def);
                match self.fir.sigs.kind(def) {
                    SigKind::Const => PathHead::Value(self.fir.sigs.const_ty(def)),
                    SigKind::Fn | SigKind::ExternFn => {
                        // R7: a NON-GENERIC `fn` item used as a value has the
                        // matching `fn` type; a generic one must be written
                        // with all its arguments (T0039, I5).
                        if self.arity(def) > 0 || self.container_arity(def) > 0 {
                            return PathHead::Silent;
                        }
                        let t = self.fn_item_ty(def);
                        PathHead::Value(t)
                    }
                    // A type, trait or enum head: not a value. A tail on one
                    // is R45's qualified form, which is I4's.
                    _ => PathHead::NotAValue,
                }
            }
            ResolvedTarget::Entity(Entity::Variant { file, decl, index }) => {
                let def = self.defs.def_of(file, decl);
                if def == fors_fir::NO_DEF || self.arity(def) > 0 {
                    return PathHead::Silent;
                }
                let _ = index;
                self.dep(def);
                let t = self.fir.tys.nominal(def, NO_ARGS);
                PathHead::Value(t)
            }
            _ => PathHead::Silent,
        }
    }

    /// The `k`th `.`-segment of a path node.
    pub fn segment_name(&mut self, cx: &BodyCx, node: usize, k: usize) -> Option<Symbol> {
        let (a, b) = fors_resolve::paths::own_span(cx.f.tree, node);
        let i = (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
            .filter(|&i| cx.f.tokens.kinds[i] == TokenKind::Ident)
            .nth(k)?;
        Some(self.names.intern(cx.f.tokens.text(i, cx.f.source)))
    }

    /// The `fn` type of a non-generic function item (R7).
    pub fn fn_item_ty(&mut self, def: DefId) -> TyId {
        let sig = self.fir.sigs.fn_sig(def);
        if sig == fors_fir::NO_FN_SIG {
            return TY_ERROR;
        }
        let n = self.fir.sigs.fn_sigs.count(sig);
        let mut ps = Vec::with_capacity(n);
        for i in 0..n {
            let p = self.fir.sigs.fn_sigs.param(sig, i);
            ps.push((p.conv, p.ty));
        }
        let r = self.fir.sigs.fn_sigs.result(sig);
        let e = self.fir.sigs.fn_sigs.raises(sig);
        let id = self.fir.tys.intern_fn_ty(&ps, r, e, false);
        self.fir.tys.fn_ty(id)
    }

    /// How many generic parameters a declaration declares of its own (a
    /// trait's implicit `Self` excluded, as `Shapes` records it).
    pub fn arity(&self, def: DefId) -> usize {
        self.shapes.arity(def)
    }

    /// The enclosing `impl`/`trait`'s arity, which a method's call must
    /// determine too (design §7.4's "parameters to determine").
    pub fn container_arity(&self, def: DefId) -> usize {
        match self.defs.get(def).map(|r| r.parent) {
            Some(p) if p != fors_fir::NO_DEF => {
                self.shapes.arity(p) + usize::from(self.fir.sigs.kind(p) == SigKind::Trait)
            }
            _ => 0,
        }
    }

    /// R42 for an explicit `FieldExpr` node — the shape ch07's `place`
    /// production builds (`consume a.b;`, `f(&x.y)`) and the one a postfix
    /// `.` after a non-path operand builds (`f().x`).
    pub fn field_expr(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let Some(operand) = cx.f.tree.children(node).next() else {
            return TY_ERROR;
        };
        let recv = self.synth(cx, operand);
        let Some(name) = self.field_name(cx, node) else {
            return TY_ERROR;
        };
        self.member_of(cx, node, recv, name)
    }

    /// R42: the field `name` of `recv`, with the head's arguments
    /// substituted and ch01 R11's qualifier carried; R49 enforces ch08
    /// R11's visibility on the way, with ch08's own code.
    pub fn member_of(&mut self, cx: &mut BodyCx, node: usize, recv: TyId, name: Symbol) -> TyId {
        if recv == TY_ERROR || recv == NO_TY {
            return TY_ERROR;
        }
        let bare = self.fir.tys.unqual(recv);
        let quals = self.fir.tys.quals(recv);
        match self.fir.tys.tag(bare) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(bare));
                self.dep(def);
                // `len` on `Array`/`Slice`/`vector` is built in (R42).
                if let Some(g) = self.prelude.generic_index(def) {
                    use fors_fir::prelude::gty;
                    if self.names.resolve(name) == b"len"
                        && matches!(g, gty::ARRAY | gty::SLICE | gty::VECTOR)
                    {
                        return self.fir.tys.prim(PrimKind::Usize);
                    }
                    // Another prelude head's members are std's: silent.
                    return TY_ERROR;
                }
                if self.fir.sigs.kind(def) != SigKind::Struct {
                    // An enum, a trait or an `impl` head: R42's "no fields"
                    // applies to an ENUM VALUE; anything else reached here
                    // is a qualified form (R45), which is I4's.
                    if self.fir.sigs.kind(def) == SigKind::Enum {
                        let n = self.show(recv);
                        self.bemit(
                            cx,
                            node,
                            42,
                            42,
                            format!("`{n}` is an enum and has no fields"),
                        );
                    }
                    return TY_ERROR;
                }
                let ms = self.fir.sigs.members(def);
                for i in 0..self.fir.sigs.member_store.count(ms) {
                    let m = self.fir.sigs.member_store.get(ms, i);
                    if m.kind != MemberKind::Field || m.name != name {
                        continue;
                    }
                    if m.vis == VIS_PRIVATE && !self.same_module(def, cx.owner) {
                        let f = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                        let h = self.head_name(def);
                        self.bemit_code(
                            cx,
                            node,
                            Code::N(11),
                            49,
                            format!("the field `{f}` of `{h}` is not `pub`"),
                        );
                        return TY_ERROR;
                    }
                    let ty = self.substituted(def, ArgsId(self.fir.tys.b(bare)), m.ty);
                    let carried = fors_fir::ty::Quals(
                        quals.0 & (fors_fir::ty::Q_IMM | fors_fir::ty::Q_SECRET),
                    );
                    return if carried.is_none() {
                        ty
                    } else {
                        self.fir.tys.qualified(ty, carried)
                    };
                }
                // Not a field. R42 is explicit that naming a method
                // without calling it is rejected too ("there are no method
                // values"), so one message covers both readings.
                let f = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                let h = self.head_name(def);
                self.bemit(cx, node, 42, 42, format!("`{h}` has no field `{f}` (if `{f}` is a method, call it: there are no method values)"));
                TY_ERROR
            }
            TyTag::Param | TyTag::Proj => {
                let n = self.show(recv);
                self.bemit(
                    cx,
                    node,
                    42,
                    42,
                    format!("`{n}` is rigid and has no fields"),
                );
                TY_ERROR
            }
            TyTag::Tuple => {
                self.bemit(
                    cx,
                    node,
                    42,
                    42,
                    "a tuple has no field names; bind or pattern-match its components".to_string(),
                );
                TY_ERROR
            }
            // MARC: verification of I3 (2026-09-20): R42's "a primitive has
            // no fields" was silent. A `fn` type or a `dyn` has none either.
            TyTag::Prim | TyTag::Fn | TyTag::Dyn => {
                let n = self.show(recv);
                let f = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                self.bemit(
                    cx,
                    node,
                    42,
                    42,
                    format!("`{n}` has no fields (`{f}`); a method is called, not read"),
                );
                TY_ERROR
            }
            _ => TY_ERROR,
        }
    }

    /// Whether `def`'s declaring module is `user`'s.
    pub fn same_module(&self, def: DefId, user: DefId) -> bool {
        match (self.defs.get(def), self.defs.get(user)) {
            (Some(a), Some(b)) => a.module == b.module,
            // A prelude row has no module: nothing about it is private.
            _ => true,
        }
    }

    /// `ty` with `head`'s generic parameters bound to `args`.
    pub fn substituted(&mut self, head: DefId, args: ArgsId, ty: TyId) -> TyId {
        if self.fir.tys.is_monomorphic(ty) {
            return ty;
        }
        let xs = self.fir.tys.args(args).to_vec();
        if xs.is_empty() {
            return ty;
        }
        let mut b = Binding::new(&[(head, xs.len() as u16)]);
        for (i, &x) in xs.iter().enumerate() {
            b.bind(head, i as u16, x);
        }
        self.subst_calls += 1;
        subst_norm(&mut self.fir.tys, ty, &b).unwrap_or(TY_ERROR)
    }

    /// The identifier a `FieldExpr` carries. The operand is the node's
    /// FIRST child and begins at the node's first token (the parser wraps
    /// the last sibling), so the name is the last identifier AFTER it.
    pub fn field_name(&mut self, cx: &BodyCx, node: usize) -> Option<Symbol> {
        let (_, end) = cx.f.tree.token_range(node);
        let after =
            cx.f.tree
                .children(node)
                .next()
                .map_or(0, |c| cx.f.tree.token_range(c).1);
        let i = (after as usize..(end as usize).min(cx.f.tokens.kinds.len()))
            .rfind(|&i| cx.f.tokens.kinds[i] == TokenKind::Ident)?;
        Some(self.names.intern(cx.f.tokens.text(i, cx.f.source)))
    }

    /// R47: a `bracket` instantiates iff its operand is a path bound to a
    /// generic item (or a method); otherwise it indexes (R29's procedure).
    /// The reading never depends on the arguments.
    pub fn bracket(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let Some(&operand) = kids.first() else {
            return TY_ERROR;
        };
        if self.is_instantiation(cx, operand) {
            // Explicit generic arguments are R38(a)'s, which is I5's.
            return TY_ERROR;
        }
        let s = if cx.kind(operand) == NodeKind::NameExpr
            && path_segments(cx, operand) > path_consumed(cx, operand).max(1) as usize
        {
            // The operand's last segment is either a field (so this is an
            // index) or a method (so this is R45's instantiation). Deciding
            // it is I4's; reading it as an index without saying anything is
            // the silent, absorbing answer either way.
            let n = path_segments(cx, operand);
            cx.quiet += 1;
            let t = self.path_value(cx, operand, n);
            cx.quiet -= 1;
            t
        } else {
            self.synth(cx, operand)
        };
        if s == TY_ERROR || s == NO_TY {
            for &a in kids.iter().skip(1) {
                self.synth(cx, a);
            }
            return TY_ERROR;
        }
        let bare = self.fir.tys.unqual(s);
        let index = kids.get(1).copied();
        // ch03 R24: a range directly inside the brackets slices an array or
        // a slice, and nothing else.
        let ranged = index.is_some_and(|i| cx.kind(i) == NodeKind::RangeExpr);
        if self.fir.tys.tag(bare) == TyTag::Nominal {
            let def = DefId(self.fir.tys.a(bare));
            if let Some(g) = self.prelude.generic_index(def) {
                use fors_fir::prelude::gty;
                let args = self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec();
                if matches!(g, gty::ARRAY | gty::SLICE | gty::VECTOR) {
                    let elem = args.first().copied().unwrap_or(TY_ERROR);
                    if let Some(i) = index {
                        if ranged {
                            self.synth(cx, i);
                            let slice = self.prelude.generics[gty::SLICE];
                            return self.fir.tys.nominal_of(slice, &[elem]);
                        }
                        let u = self.fir.tys.prim(PrimKind::Usize);
                        cx.site(NodeKind::Bracket, Slot::IndexOperand);
                        self.check(cx, i, u);
                    }
                    return elem;
                }
            }
        }
        self.user_index(cx, node, bare, index)
    }

    /// R29's `a[i]` over the `Index` impls. I3 decides only the
    /// unambiguous case: exactly one impl for this head. Two impls
    /// (R29's "several") and a rigid subject are I4's.
    fn user_index(&mut self, cx: &mut BodyCx, _node: usize, s: TyId, index: Option<usize>) -> TyId {
        let idx_trait = self.prelude.traits[fors_fir::prelude::tr::INDEX];
        let head = self.fir.tys.head_key(s);
        self.impl_scans += 1;
        let rows = self.impls.bucket(idx_trait, head);
        if rows.len() != 1 {
            if let Some(i) = index {
                self.synth(cx, i);
            }
            // MARC: verification of I3 (2026-09-20). R29's "None: T0029" was
            // silent. It is reported when NO impl could live outside this
            // build: a user-declared head (ch08 R21 puts its `Index` impls
            // in its defining module), a scalar (R22's built-in set is
            // closed), a tuple, a `fn` type or a `dyn`. A prelude head's
            // impls may be `std`'s and absent; a rigid subject is I4's.
            if rows.is_empty() && self.no_index_anywhere(s) {
                let n = self.show(s);
                self.bemit(
                    cx,
                    _node,
                    29,
                    29,
                    format!("`{n}` does not implement `Index`, which `[ ]` needs"),
                );
            }
            return TY_ERROR;
        }
        let r = self.impls.row(rows[0]);
        self.dep(r.def);
        if r.self_ty != s {
            if let Some(i) = index {
                self.synth(cx, i);
            }
            return TY_ERROR;
        }
        let want = self
            .fir
            .tys
            .args(r.trait_args)
            .first()
            .copied()
            .unwrap_or(TY_ERROR);
        if let Some(i) = index {
            cx.site(NodeKind::Bracket, Slot::IndexOperand);
            self.check(cx, i, want);
        }
        let out = self.fir.sigs.assoc(r.def);
        let rhs = self.fir.sigs.assocs.rhs_of(out, self.prelude.output_name);
        if rhs == NO_TY { TY_ERROR } else { rhs }
    }

    /// Whether `s` is a type no `Index` impl outside this build could name.
    fn no_index_anywhere(&mut self, s: TyId) -> bool {
        match self.fir.tys.tag(s) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(s));
                self.prelude.generic_index(def).is_none() && self.defs.get(def).is_some()
            }
            TyTag::Prim => PrimKind::from_u8(self.fir.tys.a(s) as u8)
                .is_some_and(|p| p.is_integer() || p.is_float() || p == PrimKind::Bool),
            TyTag::Tuple | TyTag::Fn | TyTag::Dyn => true,
            _ => false,
        }
    }

    /// R47's reading test, which never looks at the arguments: the operand
    /// must be a path bound to a GENERIC item (a non-generic one has nothing
    /// to instantiate, so its bracket indexes).
    fn is_instantiation(&mut self, cx: &mut BodyCx, operand: usize) -> bool {
        match cx.kind(operand) {
            NodeKind::NameExpr => match cx.f.uses.target_of(operand as u32) {
                Some(ResolvedTarget::Entity(Entity::Item { file, decl })) => {
                    let def = self.defs.def_of(file, decl);
                    def != fors_fir::NO_DEF
                        && matches!(
                            self.fir.sigs.kind(def),
                            SigKind::Fn
                                | SigKind::ExternFn
                                | SigKind::Struct
                                | SigKind::Enum
                                | SigKind::Trait
                        )
                        && self
                            .fir
                            .sigs
                            .generics_store
                            .count(self.fir.sigs.generics(def))
                            > 0
                }
                Some(ResolvedTarget::Entity(Entity::PreludeType(s))) => !matches!(
                    self.prelude.lookup(s),
                    Some(fors_fir::prelude::PreludeEntity::Ty(_))
                ),
                _ => false,
            },
            // `x.m[i32]()`: a method instantiation (R45), I4's.
            NodeKind::FieldExpr => true,
            _ => false,
        }
    }

    /// The `fn` row behind a value that is called (R7).
    pub fn callable_of(&mut self, ty: TyId) -> Option<FnTyId> {
        let bare = self.fir.tys.unqual(ty);
        (self.fir.tys.tag(bare) == TyTag::Fn).then(|| FnTyId(self.fir.tys.a(bare)))
    }
}

/// What a path's resolved prefix denotes (design §7.7's first column).
pub enum PathHead {
    Value(TyId),
    /// A type, trait or module: a tail on one is R45's qualified form.
    NotAValue,
    /// Already diagnosed, deliberately deferred, or not this increment's.
    Silent,
}

/// How many `.`-segments a path node writes.
pub fn path_segments(cx: &BodyCx, node: usize) -> usize {
    let (a, b) = fors_resolve::paths::own_span(cx.f.tree, node);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .filter(|&i| cx.f.tokens.kinds[i] == TokenKind::Ident)
        .count()
}

/// How many of them the resolver accounted for (ch08 R16's deferral).
pub fn path_consumed(cx: &BodyCx, node: usize) -> u8 {
    match cx.f.uses.node.binary_search(&(node as u32)) {
        Ok(i) => cx.f.uses.consumed[i],
        Err(_) => 0,
    }
}
