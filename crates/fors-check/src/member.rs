//! Member access without scope lookup (design §7.7; ch09 R42, R45, R47,
//! R49). I3 owns the half that needs no trait search: a field of a struct
//! head, the built-in `len`, and R47's reading of a `bracket`.
//!
//! Method lookup (R43/R44's two tiers) is I4's; a method call here is
//! silent and absorbing, never a guess.

use fors_fir::sig::{MemberKind, SigKind, VIS_PRIVATE};
use fors_fir::subst::Binding;
use fors_fir::ty::{ArgsId, FnTyId, NO_ARGS, NO_TY, PrimKind, TY_ERROR, TyId, TyTag};
use fors_index::Symbol;
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::target::{Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::{BodyCx, Slot};
use crate::facts::MemberTarget;
use crate::lower::FileCtx;
use crate::wf::Wf;

fn is_assign_op(k: TokenKind) -> bool {
    matches!(
        k,
        TokenKind::Eq
            | TokenKind::PlusEq
            | TokenKind::MinusEq
            | TokenKind::StarEq
            | TokenKind::SlashEq
            | TokenKind::PercentEq
            | TokenKind::AmpEq
            | TokenKind::PipeEq
            | TokenKind::CaretEq
            | TokenKind::ShlEq
            | TokenKind::ShrEq
    )
}

/// Whether the expression at `node` stands in a PLACE position: the left
/// of an assignment, or an argument marked `&`/`move`/`inout` (ch01 R2).
///
/// R42's "a method is called, not read" fix appends `()`, and `()` in a
/// place position is not a wrong guess but a PARSE error — `&out.len()`
/// and `a[i].c() = 1` both stop the file parsing. The arbiter test proved
/// it, so the fix is withheld here rather than offered and rejected. Error
/// path only.
fn in_place_position(f: &FileCtx, node: usize) -> bool {
    let kinds = &f.tokens.kinds;
    let (a, b) = f.tree.token_range(node);
    let (a, b) = ((a as usize).min(kinds.len()), (b as usize).min(kinds.len()));
    if let Some(i) = (0..a).rev().find(|i| !kinds[*i].is_trivia())
        && matches!(
            kinds[i],
            TokenKind::Amp | TokenKind::KwMove | TokenKind::KwInout
        )
    {
        return true;
    }
    if let Some(i) = (b..kinds.len()).find(|i| !kinds[*i].is_trivia())
        && is_assign_op(kinds[i])
    {
        return true;
    }
    false
}

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
        self.path_value(cx, node, n, true)
    }

    /// The value the first `upto` segments of a path denote. A call's
    /// callee asks for `upto = segments - 1`, because its last segment is
    /// the method or associated function (R43/R45), not a field. `read`
    /// records the prefix's read event; a method callee passes `false`
    /// because R46 records the receiver's own event (with its convention)
    /// instead.
    pub fn path_value(&mut self, cx: &mut BodyCx, node: usize, upto: usize, read: bool) -> TyId {
        let consumed = path_consumed(cx, node).max(1) as usize;
        let head = self.path_head(cx, node);
        let mut ty = match head {
            PathHead::Value(t) => t,
            PathHead::NotAValue | PathHead::Silent => return TY_ERROR,
        };
        if upto <= consumed {
            if read && ty != TY_ERROR && ty != NO_TY {
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
        if read {
            self.read_event(cx, node, ty);
        }
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
                        // matching `fn` type. A generic one must be written
                        // with all its arguments: there is no `fn` type to
                        // give it, and R38 determines a parameter only AT a
                        // call, never from the place a value is stored
                        // (R28's table: "a generic `fn` ... with no
                        // arguments is T0039").
                        if self.arity(def) > 0 {
                            let f = self.head_name(def);
                            let g = self.fir.sigs.generics(def);
                            let p = self.sym(self.fir.sigs.generics_store.param(g, 0).name);
                            self.bemit(cx, node, 39, 39, format!("`{f}` is generic, so it has no `fn` type of its own; write its arguments (`{f}[{p}]`)"));
                            return PathHead::Silent;
                        }
                        if self.container_arity(def) > 0 {
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
            // R28/R38: `none` in SYNTH mode has nothing to determine
            // `Option`'s argument from. In CHECK mode `check_prelude_value`
            // answers before this is reached.
            ResolvedTarget::Entity(Entity::PreludeValue(sym))
                if self.names.resolve(sym) == b"none" =>
            {
                self.bemit(
                    cx,
                    node,
                    39,
                    39,
                    "cannot infer `Option`'s argument for `none` here; write `Option[T].none` or give the binding a type".to_string(),
                );
                PathHead::Silent
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
                        // I3.5 (D4): the builtin resolution lowering reads.
                        cx.facts
                            .set_member(node as u32, MemberTarget::LenBuiltin { head: def });
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
                    // I3.5 (D4): `(head, field index)` for lowering.
                    cx.facts.set_member(
                        node as u32,
                        MemberTarget::Field {
                            head: def,
                            index: i as u32,
                        },
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
                let end = cx.range(node).1;
                let placed = in_place_position(cx.f, node);
                let emitted = self.bemit(
                    cx,
                    node,
                    42,
                    42,
                    format!("`{n}` has no fields (`{f}`); a method is called, not read"),
                );
                if emitted && !placed {
                    // R14: whether `{f}` is a method of `{n}`, and whether
                    // it takes arguments, is not decided here — the edit
                    // only writes down the reading the message states.
                    self.sink.attach_fix(fors_diag::Fix::insert(
                        fors_diag::FixKind::CallMethod,
                        format!("call it: `{f}()`"),
                        end,
                        "()",
                    ));
                }
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
        self.subst_norm_n(ty, &b).unwrap_or(TY_ERROR)
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
            let t = self.path_value(cx, operand, n, true);
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

    /// R29's `a[i]` over the `Index` impls. I3 decided only the
    /// unambiguous case: exactly one impl for this head. I4 adds R29's
    /// "several" ([`Self::index_several`]); a rigid subject, whose
    /// candidate impls are its `Index[...]` BOUNDS, stays I5's.
    fn user_index(&mut self, cx: &mut BodyCx, _node: usize, s: TyId, index: Option<usize>) -> TyId {
        let idx_trait = self.prelude.traits[fors_fir::prelude::tr::INDEX];
        let head = self.fir.tys.head_key(s);
        self.impl_scans += 1;
        self.note_bucket(idx_trait, head);
        let rows = self.impls.bucket(idx_trait, head);
        if rows.len() > 1 {
            return self.index_several(cx, _node, s, index, idx_trait, &rows);
        }
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
        // I5: the impl may be GENERIC (`impl[T] Index[usize] for Box[T]`),
        // in which case its self type is not the subject but one-way
        // matches it. Determining the impl's parameters is the same
        // `Binding` machinery R38 uses at a call, and without it both the
        // index type and `Output` would be read with the impl's own
        // parameters still in them.
        let Some(b) = self.impl_binding(&r, s) else {
            if let Some(i) = index {
                self.synth(cx, i);
            }
            return TY_ERROR;
        };
        let declared = self
            .fir
            .tys
            .args(r.trait_args)
            .first()
            .copied()
            .unwrap_or(TY_ERROR);
        let want = self.subst_impl(declared, &b);
        if let Some(i) = index {
            cx.site(NodeKind::Bracket, Slot::IndexOperand);
            self.check(cx, i, want);
        }
        let out = self.fir.sigs.assoc(r.def);
        let rhs = self.fir.sigs.assocs.rhs_of(out, self.prelude.output_name);
        // F7 (fmir-interpreter.md §4.1's gap): record which `Index` impl
        // this `a[i]` resolved to — and, when exactly one `IndexMut` impl
        // also matches this head, its `at_mut` too — so lowering has a
        // fact to read for `a[i]`/`a[i] = v` on a user nominal type
        // (`Buffer`, `Vec`, ...). Same unambiguous-impl scope as the rest
        // of this function; `index_several`'s several-impl case is I4's.
        let at = self.index_method_def(r.def, b"at");
        let at_mut = {
            let idx_mut_trait = self.prelude.traits[fors_fir::prelude::tr::INDEXMUT];
            self.note_bucket(idx_mut_trait, head);
            let mut_rows = self.impls.bucket(idx_mut_trait, head);
            if mut_rows.len() == 1 {
                let rm = self.impls.row(mut_rows[0]);
                self.index_method_def(rm.def, b"at_mut")
            } else {
                None
            }
        };
        if let Some(at) = at {
            cx.facts
                .set_member(_node as u32, MemberTarget::IndexImpl { at, at_mut });
        }
        if rhs == NO_TY {
            TY_ERROR
        } else {
            self.subst_impl(rhs, &b)
        }
    }

    /// The `DefId` of the method named `name` directly inside impl `def`
    /// (`Index::at`'s or `IndexMut::at_mut`'s own implementation).
    fn index_method_def(&self, def: DefId, name: &[u8]) -> Option<DefId> {
        self.impl_method_names(def)
            .into_iter()
            .find(|&(sym, _)| self.names.resolve(sym) == name)
            .map(|(_, d)| d)
    }

    /// The impl's own parameters, determined from its self type against
    /// the subject (design §7.6's `impl_lookup`, one candidate). `None`
    /// when the impl does not match, or when a slot is left unbound (R18
    /// forbids that for a well-formed impl, so it means the head failed
    /// to lower).
    fn impl_binding(&mut self, r: &fors_fir::impls::ImplRow, s: TyId) -> Option<Binding> {
        let n = self
            .fir
            .sigs
            .generics_store
            .count(self.fir.sigs.generics(r.def));
        let mut b = Binding::new(&[(r.def, n as u16)]);
        if !fors_fir::subst::one_way_match(&mut self.fir.tys, r.self_ty, s, &mut b) {
            return None;
        }
        b.is_complete().then_some(b)
    }

    fn subst_impl(&mut self, ty: TyId, b: &Binding) -> TyId {
        if b.owner_count() == 0 {
            return ty;
        }
        self.subst_calls += 1;
        self.subst_norm_n(ty, b).unwrap_or(TY_ERROR)
    }

    /// R29's "Several" clause (increment I4). With more than one `Index`
    /// impl for the head the index is SYNTHESISED and `S` must implement
    /// `Index[synth(i)]` by one Rule 12 lookup — so an unsuffixed literal
    /// index, which has no type of its own to synthesise, MUST be rejected
    /// ("suffix the index"). Adding a second impl can therefore break
    /// `a[0]`, but can never silently change which impl `a[0]` meant.
    /// Nothing is ranked.
    fn index_several(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        s: TyId,
        index: Option<usize>,
        idx_trait: DefId,
        rows: &[u32],
    ) -> TyId {
        let Some(i) = index else {
            return TY_ERROR;
        };
        if self.is_bare_literal(cx, i) {
            self.bemit(
                cx,
                node,
                29,
                29,
                "with several `Index` impls the index is synthesised, so an unsuffixed literal \
                 index names no impl; suffix the index"
                    .to_string(),
            );
            return TY_ERROR;
        }
        let it = self.synth(cx, i);
        if it == TY_ERROR || it == NO_TY {
            return TY_ERROR;
        }
        let args = self.fir.tys.intern_args(&[it]);
        let want = self.fir.tys.intern_trait_ref(idx_trait, args);
        if self.holds(s, want) == crate::wf::Holds::No {
            let n = self.show(s);
            let ity = self.show(it);
            self.bemit(
                cx,
                node,
                29,
                29,
                format!("`{n}` does not implement `Index[{ity}]`, which `[ ]` needs here"),
            );
            return TY_ERROR;
        }
        // The result is the chosen impl's `Output`, never a ranked guess.
        // A GENERIC impl is selected by the same one-way match `holds`
        // just used, so its `Index[I]` and `Output` are read with its
        // parameters determined, not with the impl's own rows still in
        // them (I5).
        for &r in rows {
            let row = self.impls.row(r);
            let Some(b) = self.impl_binding(&row, s) else {
                continue;
            };
            let declared = self
                .fir
                .tys
                .args(row.trait_args)
                .first()
                .copied()
                .unwrap_or(TY_ERROR);
            if self.subst_impl(declared, &b) != it {
                continue;
            }
            self.dep(row.def);
            let out = self.fir.sigs.assoc(row.def);
            let rhs = self.fir.sigs.assocs.rhs_of(out, self.prelude.output_name);
            return if rhs == NO_TY {
                TY_ERROR
            } else {
                self.subst_impl(rhs, &b)
            };
        }
        TY_ERROR
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
    pub(crate) fn is_instantiation(&mut self, cx: &mut BodyCx, operand: usize) -> bool {
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
