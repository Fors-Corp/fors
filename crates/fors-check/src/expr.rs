//! The two judgements over every expression form (design §7.3, ch09
//! R26-R37, R42, R47).
//!
//! `synth` never fails: a form this increment does not decide yields
//! [`TY_ERROR`], which is absorbing, so an unimplemented rule can only make
//! the checker quieter, never wrong. Every diagnostic below is at the node
//! whose rule it is, once.

use fors_fir::prelude::{gty, tr};
use fors_fir::sig::Conv;
use fors_fir::ty::{
    ArgsId, FnTyId, NO_ARGS, NO_TY, PrimKind, TY_ERROR, TY_NEVER, TY_UNIT, TraitRefId, TyId, TyTag,
};
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::target::{DeferReason, Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::{BodyCx, LocalKind, Slot, is_expr_kind, is_type_node, op_between, own_first};
use crate::lower::{MAX_LIST, MAX_PARAMS, parse_int_literal};
use crate::wf::{Holds, Wf};

/// What a numeric literal token is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lit {
    IntUnsuffixed,
    FloatUnsuffixed,
    Suffixed(PrimKind),
    Bool,
    Str,
    None,
}

impl Wf<'_> {
    // ------------------------------------------------------------ check

    /// `check(e, T)` (design §7.3's dispatcher). Returns `T` on success,
    /// [`TY_NEVER`] under R10(a) and [`TY_ERROR`] under recovery.
    pub fn check(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        cx.nodes += 1;
        self.checks += 1;
        match cx.kind(node) {
            NodeKind::Literal => self.check_literal(cx, node, want),
            NodeKind::DotLit => self.check_dot_lit(cx, node, want),
            NodeKind::Block => self.check_block(cx, node, want),
            NodeKind::IfExpr => self.if_expr(cx, node, Some(want)),
            NodeKind::MatchExpr => self.match_expr(cx, node, Some(want)),
            NodeKind::ComptimeBlock => {
                let kids = cx.kids(node);
                match kids.first() {
                    Some(&b) => self.check(cx, b, want),
                    None => TY_UNIT,
                }
            }
            NodeKind::TupleOrParen => self.check_tuple(cx, node, want),
            NodeKind::ArrayLit => self.check_array(cx, node, want),
            NodeKind::Closure => self.check_closure(cx, node, want),
            NodeKind::CallExpr => self.call_expr(cx, node, Some(want)),
            NodeKind::StructLit => self.struct_lit(cx, node, Some(want)),
            NodeKind::NameExpr => {
                // `none` and a unit variant take their enum from the
                // expected type (R28/R34); everything else subsumes.
                if let Some(t) = self.check_prelude_value(cx, node, want) {
                    return t;
                }
                let s = self.synth(cx, node);
                self.subsume(cx, node, s, want)
            }
            NodeKind::TryExpr => {
                let kids = cx.kids(node);
                match kids.first() {
                    Some(&c) if cx.kind(c) == NodeKind::CallExpr => {
                        self.try_guard(cx, node);
                        cx.under_try = Some(node as u32);
                        let t = self.call_expr(cx, c, Some(want));
                        cx.under_try = None;
                        t
                    }
                    _ => {
                        let s = self.synth(cx, node);
                        self.subsume(cx, node, s, want)
                    }
                }
            }
            NodeKind::UnaryExpr if self.is_bare_literal(cx, node) => {
                // R26's table: `-a` checks against `T` by checking the
                // literal (ch07 Disambiguation 8 makes `-4` one literal).
                let kids = cx.kids(node);
                match kids.first() {
                    Some(&c) => {
                        let t = self.check(cx, c, want);
                        self.require_trait(cx, node, t, tr::NEG, "-", 29);
                        t
                    }
                    None => TY_ERROR,
                }
            }
            NodeKind::Error => TY_ERROR,
            NodeKind::AsmExpr | NodeKind::BareOp => {
                // ch04 R27 and R37: CHECK-only forms this increment does not
                // decide. Silent, absorbing.
                TY_ERROR
            }
            _ => {
                let s = self.synth(cx, node);
                self.subsume(cx, node, s, want)
            }
        }
    }

    /// R10, applied once, at the outermost type only.
    pub fn subsume(&mut self, cx: &mut BodyCx, node: usize, s: TyId, want: TyId) -> TyId {
        if want == NO_TY || s == NO_TY || s == TY_ERROR || want == TY_ERROR || s == want {
            return want;
        }
        if s == TY_NEVER {
            return want; // (a)
        }
        if self.fn_shape_eq(s, want) {
            return want; // (b)
        }
        if self.fir.tys.tag(self.fir.tys.unqual(want)) == TyTag::Dyn {
            return match self.to_dyn(s, want) {
                Ok(()) => want,
                Err((code, msg)) => {
                    self.bemit(cx, node, code, 10, msg);
                    TY_ERROR
                }
            };
        }
        let sn = self.show(s);
        let wn = self.show(want);
        self.bemit(cx, node, 26, 26, format!("expected `{wn}`, found `{sn}`"));
        TY_ERROR
    }

    /// R10(b): a closure type or `fn` item coerces to an EQUAL `fn` type.
    /// "Equal" is R7's equality; the only slack is that a closure row and a
    /// `fn` row with the same shape are the same function type.
    fn fn_shape_eq(&mut self, s: TyId, want: TyId) -> bool {
        let (s, want) = (self.fir.tys.unqual(s), self.fir.tys.unqual(want));
        if self.fir.tys.tag(s) != TyTag::Fn || self.fir.tys.tag(want) != TyTag::Fn {
            return false;
        }
        let (a, b) = (FnTyId(self.fir.tys.a(s)), FnTyId(self.fir.tys.a(want)));
        let (ca, pa) = self.fir.tys.fn_tys().params(a);
        let (cb, pb) = self.fir.tys.fn_tys().params(b);
        ca == cb
            && pa == pb
            && self.fir.tys.fn_tys().result(a) == self.fir.tys.fn_tys().result(b)
            && self.fir.tys.fn_tys().raises(a) == self.fir.tys.fn_tys().raises(b)
    }

    /// R10(c) and its four exclusions (round 6: rigid, neutral projection,
    /// linear; ch01 R15(b)/R19a's brand and scoped values are I5's).
    pub fn to_dyn(&mut self, s: TyId, want: TyId) -> Result<(), (u16, String)> {
        let bare = self.fir.tys.unqual(s);
        let dyn_ty = self.fir.tys.unqual(want);
        let tref = TraitRefId(self.fir.tys.a(dyn_ty));
        let (tdef, _) = self.fir.tys.trait_ref(tref);
        let trait_name = self.head_name(tdef);
        match self.fir.tys.tag(bare) {
            TyTag::Param => {
                let n = self.show(s);
                return Err((
                    10,
                    format!(
                        "a value of the rigid type `{n}` does not coerce to `dyn {trait_name}`: take `dyn {trait_name}` as a parameter instead"
                    ),
                ));
            }
            TyTag::Proj => {
                let n = self.show(s);
                return Err((
                    10,
                    format!(
                        "a value of the neutral projection `{n}` does not coerce to `dyn {trait_name}`"
                    ),
                ));
            }
            _ => {}
        }
        if self.is_linear(bare) {
            let n = self.show(s);
            return Err((
                10,
                format!(
                    "a value of the linear type `{n}` does not coerce to `dyn {trait_name}`: its cleanup obligation would become invisible (ch01 R22f)"
                ),
            ));
        }
        match self.holds(bare, tref) {
            Holds::No => {
                let n = self.show(s);
                Err((
                    26,
                    format!(
                        "expected `dyn {trait_name}`, found `{n}`: `{n}` does not implement `{trait_name}`"
                    ),
                ))
            }
            _ => Ok(()),
        }
    }

    // ------------------------------------------------------------ synth

    /// `synth(e)` (design §7.3). Never fails.
    pub fn synth(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        cx.nodes += 1;
        self.synths += 1;
        match cx.kind(node) {
            NodeKind::Literal => self.synth_literal(cx, node),
            NodeKind::DotLit => {
                // R34: a dot literal is CHECK only.
                self.bemit(cx, node, 34, 34, "a `.variant` literal is legal only where an enum type is expected; write the enum's name".to_string());
                TY_ERROR
            }
            NodeKind::NameExpr => self.name_expr(cx, node),
            NodeKind::AddExpr | NodeKind::MulExpr | NodeKind::BitExpr | NodeKind::CmpExpr => {
                self.operator(cx, node)
            }
            NodeKind::UnaryExpr => self.unary(cx, node),
            NodeKind::NotExpr => {
                for c in cx.kids(node) {
                    cx.site(NodeKind::NotExpr, Slot::Condition);
                    self.check_condition(cx, c, NodeKind::NotExpr);
                }
                self.fir.tys.prim(PrimKind::Bool)
            }
            NodeKind::AndExpr | NodeKind::OrExpr => {
                let k = cx.kind(node);
                for c in cx.kids(node) {
                    cx.site(k, Slot::Condition);
                    self.check_condition(cx, c, k);
                }
                self.fir.tys.prim(PrimKind::Bool)
            }
            NodeKind::RangeExpr => self.range_expr(cx, node),
            NodeKind::CastExpr => self.cast_expr(cx, node),
            NodeKind::Block => self.synth_block(cx, node),
            NodeKind::IfExpr => self.if_expr(cx, node, None),
            NodeKind::MatchExpr => self.match_expr(cx, node, None),
            NodeKind::ComptimeBlock => {
                let kids = cx.kids(node);
                match kids.first() {
                    Some(&b) => self.synth(cx, b),
                    None => TY_UNIT,
                }
            }
            NodeKind::TupleOrParen => self.synth_tuple(cx, node),
            NodeKind::ArrayLit => self.synth_array(cx, node),
            NodeKind::StructLit => self.struct_lit(cx, node, None),
            NodeKind::CallExpr => self.call_expr(cx, node, None),
            NodeKind::FieldExpr => self.field_expr(cx, node),
            NodeKind::Bracket => self.bracket(cx, node),
            NodeKind::TryExpr => {
                self.try_guard(cx, node);
                let kids = cx.kids(node);
                match kids.first() {
                    Some(&c) if cx.kind(c) == NodeKind::CallExpr => {
                        cx.under_try = Some(node as u32);
                        let t = self.call_expr(cx, c, None);
                        cx.under_try = None;
                        t
                    }
                    Some(&c) => {
                        // R36: `e?` requires `e` to be a call.
                        if cx.kind(c) != NodeKind::Error {
                            self.bemit(
                                cx,
                                node,
                                36,
                                36,
                                "`?` applies only to a call of a `raises` function".to_string(),
                            );
                        }
                        self.synth(cx, c);
                        TY_ERROR
                    }
                    None => TY_ERROR,
                }
            }
            NodeKind::Closure => self.synth_closure(cx, node),
            NodeKind::InoutArg | NodeKind::SetArg | NodeKind::NamedArg => {
                let kids = cx.kids(node);
                match kids.first() {
                    Some(&c) => self.synth(cx, c),
                    None => TY_ERROR,
                }
            }
            NodeKind::BareOp => {
                // R37: legal only in CHECK mode against a `fn(let X, let X)`.
                self.bemit(
                    cx,
                    node,
                    37,
                    37,
                    "a bare operator argument is legal only where a `fn` type is expected"
                        .to_string(),
                );
                TY_ERROR
            }
            NodeKind::AsmExpr | NodeKind::Error => TY_ERROR,
            _ => TY_ERROR,
        }
    }

    // --------------------------------------------------------- literals

    /// Classifies a `Literal` node's token (R27).
    pub fn lit_of(&mut self, cx: &BodyCx, node: usize) -> Lit {
        let (a, b) = cx.f.tree.token_range(node);
        for i in a as usize..(b as usize).min(cx.f.tokens.kinds.len()) {
            match cx.f.tokens.kinds[i] {
                TokenKind::Int => return int_lit(cx.f.tokens.text(i, cx.f.source)),
                TokenKind::Float => return float_lit(cx.f.tokens.text(i, cx.f.source)),
                TokenKind::KwTrue | TokenKind::KwFalse => return Lit::Bool,
                TokenKind::Str | TokenKind::MultilineStr => return Lit::Str,
                _ => {}
            }
        }
        Lit::None
    }

    fn synth_literal(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        match self.lit_of(cx, node) {
            Lit::IntUnsuffixed => self.fir.tys.prim(PrimKind::I32),
            Lit::FloatUnsuffixed => self.fir.tys.prim(PrimKind::F64),
            Lit::Suffixed(k) => self.fir.tys.prim(k),
            Lit::Bool => self.fir.tys.prim(PrimKind::Bool),
            Lit::Str => self.fir.tys.prim(PrimKind::Str),
            Lit::None => TY_ERROR,
        }
    }

    fn check_literal(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        let lit = self.lit_of(cx, node);
        let bare = self.fir.tys.unqual(want);
        match lit {
            Lit::IntUnsuffixed | Lit::FloatUnsuffixed if want != TY_ERROR && want != NO_TY => {
                let prim = if self.fir.tys.tag(bare) == TyTag::Prim {
                    PrimKind::from_u8(self.fir.tys.a(bare) as u8)
                } else {
                    None
                };
                match prim {
                    Some(p) if lit == Lit::IntUnsuffixed && p.is_integer() => want,
                    Some(p) if lit == Lit::FloatUnsuffixed && p.is_float() => want,
                    Some(p) if lit == Lit::IntUnsuffixed && p.is_float() => {
                        let w = self.show(want);
                        self.bemit(cx, node, 27, 27, format!("an integer literal does not check against the float type `{w}`; write it with a decimal point"));
                        TY_ERROR
                    }
                    Some(p) if lit == Lit::FloatUnsuffixed && p.is_integer() => {
                        let w = self.show(want);
                        self.bemit(cx, node, 27, 27, format!("a float literal checks against `f32` or `f64` only, not the integer type `{w}`"));
                        TY_ERROR
                    }
                    _ if matches!(self.fir.tys.tag(bare), TyTag::Param | TyTag::Proj) => {
                        let w = self.show(want);
                        self.bemit(
                            cx,
                            node,
                            27,
                            27,
                            format!("a literal never checks against the rigid type `{w}`"),
                        );
                        TY_ERROR
                    }
                    _ => {
                        let s = self.synth_literal(cx, node);
                        self.subsume(cx, node, s, want)
                    }
                }
            }
            _ => {
                let s = self.synth_literal(cx, node);
                self.subsume(cx, node, s, want)
            }
        }
    }

    // -------------------------------------------------------- operators

    /// R29. A flat n-ary node folds left to right; the one syntactic
    /// exception is an unsuffixed literal on the left.
    fn operator(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kind = cx.kind(node);
        let kids = cx.kids(node);
        if kids.is_empty() {
            return TY_ERROR;
        }
        let lit_left = kids.len() >= 2
            && self.is_bare_literal(cx, kids[0])
            && !self.is_bare_literal(cx, kids[1]);
        // MARC: verification of I3 (2026-09-20). `never` is absorbing here
        // (R10(a), R33: a `never` operand binds nothing and coerces to
        // whatever the other side is). Before, `1 + die()` CHECKed the
        // literal against `never` and `die() + 1` checked `1` against
        // `never`, both spurious T0026s. A `never` right operand under the
        // literal exception falls back to the ordinary order; a `never`
        // left operand makes the whole expression `never` and the rest is
        // merely synthesised.
        let (mut acc, mut prev, start) = if lit_left {
            let t = self.synth(cx, kids[1]);
            if t == TY_NEVER {
                let a = self.synth(cx, kids[0]);
                (a, 1usize, 2usize)
            } else {
                cx.site(kind, Slot::OperatorRhs);
                self.check(cx, kids[0], t);
                if let Some(op) = op_between(cx, kids[0], kids[1]) {
                    self.require_operator(cx, kids[1], t, op, 29);
                }
                (t, 1usize, 2usize)
            }
        } else {
            (self.synth(cx, kids[0]), 0usize, 1usize)
        };
        for j in start..kids.len() {
            if acc == TY_NEVER {
                self.synth(cx, kids[j]);
                prev = j;
                continue;
            }
            if let Some(op) = op_between(cx, kids[prev], kids[j]) {
                self.require_operator(cx, kids[j], acc, op, 29);
            }
            cx.site(kind, Slot::OperatorRhs);
            let r = self.check(cx, kids[j], acc);
            if acc == TY_ERROR {
                acc = r;
            }
            prev = j;
        }
        if acc == TY_NEVER {
            TY_NEVER
        } else if kind == NodeKind::CmpExpr {
            self.fir.tys.prim(PrimKind::Bool)
        } else {
            acc
        }
    }

    fn unary(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let Some(&c) = kids.first() else {
            return TY_ERROR;
        };
        match own_first(cx, node) {
            Some(TokenKind::KwMove) => {
                let t = self.synth(cx, c);
                if let Some(p) = self.place_of(cx, c) {
                    cx.tape.push(
                        node as u32,
                        p,
                        crate::tape::UseKind::Move,
                        crate::tape::Cause::Explicit(node as u32),
                    );
                }
                t
            }
            _ => {
                // `-e`: R29's `Neg` (R22: signed integers and floats only).
                // A negated literal is the literal.
                let t = self.synth(cx, c);
                self.require_trait(cx, node, t, tr::NEG, "-", 29);
                t
            }
        }
    }

    /// Requires `s` to implement the trait `op` needs (R29); R57's "the fix
    /// is a bound" half, for a rigid `s`, is I5's.
    pub fn require_operator(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        s: TyId,
        op: TokenKind,
        site: u16,
    ) {
        let Some(which) = trait_of(op) else { return };
        self.require_trait(cx, node, s, which, op_text(op), site);
    }

    /// Requires `s` to implement the prelude trait `which` (R29), naming the
    /// operator `sym` in the diagnostic. MARC: verification of I3
    /// (2026-09-20): unary `-` asked for `Sub`, so `-x` on an unsigned
    /// integer passed; it asks for `Neg` now.
    pub fn require_trait(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        s: TyId,
        which: usize,
        sym: &str,
        site: u16,
    ) {
        if s == TY_ERROR || s == NO_TY || s == TY_NEVER {
            return;
        }
        let bare = self.fir.tys.unqual(s);
        if matches!(self.fir.tys.tag(bare), TyTag::Param | TyTag::Proj) {
            return; // R57, I5's
        }
        let tdef = self.prelude.traits[which];
        if tdef == fors_fir::NO_DEF {
            return;
        }
        let want = self.fir.tys.intern_trait_ref(tdef, NO_ARGS);
        if self.holds(bare, want) == Holds::No {
            let n = self.show(s);
            let tn = self.head_name(tdef);
            self.bemit(
                cx,
                node,
                29,
                site,
                format!("`{n}` does not implement `{tn}`, which the operator `{sym}` needs"),
            );
        }
    }

    /// R30: `not`/`and`/`or` operands and `if`/`while` conditions are
    /// SYNTHESISED and must be `bool`.
    pub fn check_condition(&mut self, cx: &mut BodyCx, node: usize, _parent: NodeKind) -> TyId {
        let s = self.synth(cx, node);
        let b = self.fir.tys.prim(PrimKind::Bool);
        if s == TY_ERROR || s == NO_TY || s == TY_NEVER || self.fir.tys.unqual(s) == b {
            return b;
        }
        let n = self.show(s);
        self.bemit(cx, node, 30, 30, format!("expected `bool`, found `{n}`: there is no truthiness and `and`/`or`/`not` are not overloadable"));
        TY_ERROR
    }

    /// R30: both operands of `..<`/`..=` are the same integer type.
    fn range_expr(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        if kids.len() < 2 {
            for &c in &kids {
                self.synth(cx, c);
            }
            return TY_ERROR;
        }
        let lit_left = self.is_bare_literal(cx, kids[0]) && !self.is_bare_literal(cx, kids[1]);
        // MARC: verification of I3 (2026-09-20). R30's own clause — "both
        // operands MUST be the same integer type" — carries R30's code, so
        // two NON-literal operands of different types are T0030 here, not
        // R26's subsumption failure. A literal operand is still CHECKed
        // against the other's type (R27's literal typing, R29's exception).
        // A `never` bound makes the range `never` (R10(a)); the other bound
        // is synthesised so its own errors are still reported.
        let elem = if lit_left {
            let t = self.synth(cx, kids[1]);
            if t == TY_NEVER {
                self.synth(cx, kids[0]);
                return TY_NEVER;
            }
            cx.site(NodeKind::RangeExpr, Slot::OperatorRhs);
            self.check(cx, kids[0], t);
            t
        } else if self.is_bare_literal(cx, kids[1]) {
            let t = self.synth(cx, kids[0]);
            if t == TY_NEVER {
                self.synth(cx, kids[1]);
                return TY_NEVER;
            }
            cx.site(NodeKind::RangeExpr, Slot::OperatorRhs);
            self.check(cx, kids[1], t);
            t
        } else {
            let a = self.synth(cx, kids[0]);
            let b = self.synth(cx, kids[1]);
            if a == TY_NEVER || b == TY_NEVER {
                return TY_NEVER;
            }
            if a != TY_ERROR
                && b != TY_ERROR
                && a != NO_TY
                && b != NO_TY
                && self.fir.tys.unqual(a) != self.fir.tys.unqual(b)
            {
                let (x, y) = (self.show(a), self.show(b));
                self.bemit(cx, node, 30, 30, format!("both operands of a range must be the same integer type; found `{x}` and `{y}`"));
                return TY_ERROR;
            }
            a
        };
        if elem == TY_ERROR || elem == NO_TY {
            return TY_ERROR;
        }
        let bare = self.fir.tys.unqual(elem);
        let ok = self.fir.tys.tag(bare) == TyTag::Prim
            && PrimKind::from_u8(self.fir.tys.a(bare) as u8).is_some_and(|p| p.is_integer());
        if !ok {
            let n = self.show(elem);
            self.bemit(
                cx,
                node,
                30,
                30,
                format!("both operands of a range must be the same integer type; found `{n}`"),
            );
            return TY_ERROR;
        }
        let incl = own_first(cx, node) == Some(TokenKind::DotDotEq)
            || op_between(cx, kids[0], kids[1]) == Some(TokenKind::DotDotEq);
        let head = self.prelude.generics[if incl { gty::RANGEINCL } else { gty::RANGE }];
        self.fir.tys.nominal_of(head, &[bare])
    }

    /// R30's `e as U`, plus R10(c) written explicitly (`x as dyn Tr`).
    fn cast_expr(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let Some(&operand) = kids.first() else {
            return TY_ERROR;
        };
        let mut s = self.synth(cx, operand);
        for &ty_node in kids.iter().skip(1) {
            if !is_type_node(cx.kind(ty_node)) {
                continue;
            }
            let u = self.lower_annotation(cx, ty_node);
            if u == TY_ERROR || s == TY_ERROR {
                s = TY_ERROR;
                continue;
            }
            if s == TY_NEVER {
                // R10(a): `never` coerces to `U`; the cast is never reached.
                s = u;
                continue;
            }
            if self.fir.tys.tag(self.fir.tys.unqual(u)) == TyTag::Dyn {
                s = match self.to_dyn(s, u) {
                    Ok(()) => u,
                    Err((code, msg)) => {
                        self.bemit(cx, node, code, 10, msg);
                        TY_ERROR
                    }
                };
                continue;
            }
            if self.numeric(s) && self.numeric(u) {
                s = u;
                continue;
            }
            let a = self.show(s);
            let b = self.show(u);
            self.bemit(
                cx,
                node,
                30,
                30,
                format!("`as` converts between numeric primitives only; `{a}` to `{b}` is not one"),
            );
            s = TY_ERROR;
        }
        s
    }

    fn numeric(&mut self, t: TyId) -> bool {
        let bare = self.fir.tys.unqual(t);
        self.fir.tys.tag(bare) == TyTag::Prim
            && PrimKind::from_u8(self.fir.tys.a(bare) as u8)
                .is_some_and(|p| p.is_integer() || p.is_float())
    }

    /// Whether `node` is an unsuffixed numeric literal, optionally negated
    /// (R29's one syntactic exception; ch07 Disambiguation 8).
    fn is_bare_literal(&mut self, cx: &mut BodyCx, node: usize) -> bool {
        let n = match cx.kind(node) {
            NodeKind::UnaryExpr if own_first(cx, node) == Some(TokenKind::Minus) => {
                match cx.f.tree.children(node).next() {
                    Some(c) => c,
                    None => return false,
                }
            }
            _ => node,
        };
        cx.kind(n) == NodeKind::Literal
            && matches!(
                self.lit_of(cx, n),
                Lit::IntUnsuffixed | Lit::FloatUnsuffixed
            )
    }

    // --------------------------------------------------- if, match, tuple

    fn if_expr(&mut self, cx: &mut BodyCx, node: usize, want: Option<TyId>) -> TyId {
        let kids = cx.kids(node);
        let mut blocks: Vec<usize> = Vec::new();
        let mut i = 0usize;
        while i < kids.len() {
            if i + 1 < kids.len() && cx.kind(kids[i + 1]) == NodeKind::Block {
                cx.site(NodeKind::IfExpr, Slot::Condition);
                self.check_condition(cx, kids[i], NodeKind::IfExpr);
                blocks.push(kids[i + 1]);
                i += 2;
            } else {
                // The trailing `else` block.
                blocks.push(kids[i]);
                i += 1;
            }
        }
        let has_else = kids.len() % 2 == 1;
        match want {
            Some(w) => {
                // R32: in CHECK mode EVERY branch is checked.
                let mut all_never = has_else && !blocks.is_empty();
                for &b in &blocks {
                    cx.site(NodeKind::IfExpr, Slot::Tail);
                    if self.check(cx, b, w) != TY_NEVER {
                        all_never = false;
                    }
                }
                if !has_else && w != TY_UNIT && w != TY_ERROR && w != NO_TY && w != TY_NEVER {
                    let n = self.show(w);
                    self.bemit(
                        cx,
                        node,
                        26,
                        32,
                        format!("expected `{n}`: an `if` with no `else` has type `()`"),
                    );
                    return TY_ERROR;
                }
                // Every arm diverged, so the `if` itself does: a body whose
                // last statement is `if c { return a; } else { return b; }`
                // needs no tail expression.
                if all_never { TY_NEVER } else { w }
            }
            None if !has_else => {
                for &b in &blocks {
                    cx.site(NodeKind::IfExpr, Slot::Tail);
                    self.check(cx, b, TY_UNIT);
                }
                TY_UNIT
            }
            None => {
                // R32: synthesise in source order until one is not `never`;
                // every later branch is checked against it.
                let mut fixed = TY_NEVER;
                for &b in &blocks {
                    if fixed == TY_NEVER {
                        let t = self.synth_block(cx, b);
                        if t != TY_NEVER {
                            fixed = t;
                        }
                    } else {
                        cx.site(NodeKind::IfExpr, Slot::Tail);
                        self.check(cx, b, fixed);
                    }
                }
                fixed
            }
        }
    }

    fn match_expr(&mut self, cx: &mut BodyCx, node: usize, want: Option<TyId>) -> TyId {
        let kids = cx.kids(node);
        let Some(&scrutinee) = kids.first() else {
            return TY_ERROR;
        };
        let s = self.synth(cx, scrutinee);
        if let Some(p) = self.place_of(cx, scrutinee) {
            let k = if self.copyable(s) {
                crate::tape::UseKind::Copy
            } else {
                crate::tape::UseKind::Read
            };
            cx.tape.push(
                scrutinee as u32,
                p,
                k,
                crate::tape::Cause::Explicit(node as u32),
            );
        }
        let mut fixed = want.unwrap_or(TY_NEVER);
        let mut arms = 0usize;
        let mut all_never = true;
        for &arm in kids.iter().skip(1) {
            if cx.kind(arm) != NodeKind::Arm {
                continue;
            }
            let parts = cx.kids(arm);
            let Some(&pat) = parts.first() else { continue };
            self.bind_pat(cx, pat, s);
            let Some(&body) = parts.iter().find(|&&c| is_expr_kind(cx.kind(c))) else {
                continue;
            };
            arms += 1;
            if want.is_some() || fixed != TY_NEVER {
                cx.site(NodeKind::MatchExpr, Slot::Tail);
                if self.check(cx, body, fixed) != TY_NEVER {
                    all_never = false;
                }
            } else {
                let t = self.synth(cx, body);
                if t != TY_NEVER {
                    fixed = t;
                    all_never = false;
                }
            }
        }
        // R32: all arms `never` means the `match` is `never`. (Whether the
        // arms COVER the scrutinee is R53's, in I7.)
        if arms > 0 && all_never {
            return TY_NEVER;
        }
        fixed
    }

    fn synth_tuple(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        if kids.len() == 1 && !has_comma(cx, node) {
            return self.synth(cx, kids[0]);
        }
        let mut parts = Vec::with_capacity(kids.len());
        for &c in &kids {
            parts.push(self.synth(cx, c));
        }
        if parts.is_empty() {
            return TY_UNIT;
        }
        if parts.len() > MAX_LIST {
            self.bemit(cx, node, 4, 4, format!("implementation limit: a tuple has {} components; at most {MAX_LIST} are supported", parts.len()));
            return TY_ERROR;
        }
        self.fir.tys.tuple_of(&parts)
    }

    fn check_tuple(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        let kids = cx.kids(node);
        if kids.len() == 1 && !has_comma(cx, node) {
            return self.check(cx, kids[0], want);
        }
        let bare = self.fir.tys.unqual(want);
        if self.fir.tys.tag(bare) == TyTag::Tuple {
            let parts = self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec();
            if parts.len() == kids.len() {
                for (i, &c) in kids.iter().enumerate() {
                    self.check(cx, c, parts[i]);
                }
                return want;
            }
        }
        let s = self.synth_tuple(cx, node);
        self.subsume(cx, node, s, want)
    }

    // --------------------------------------------------- array literals

    /// ch03 R22: `T` from the first element, `N` the count.
    fn synth_array(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        if kids.is_empty() {
            // ch03 R22's empty-literal rejection is ch03's (I10).
            return TY_ERROR;
        }
        if is_repeat(cx, node) {
            let elem = self.synth(cx, kids[0]);
            let n = kids.get(1).and_then(|&c| self.const_usize(cx, c));
            return self.array_of(elem, n);
        }
        // R32's pattern for `never`: the element type is the first
        // element's that is not `never`; later ones are checked against it.
        let mut elem = TY_NEVER;
        let mut i = 0usize;
        while i < kids.len() && elem == TY_NEVER {
            elem = self.synth(cx, kids[i]);
            i += 1;
        }
        for &c in kids.iter().skip(i) {
            cx.site(NodeKind::ArrayLit, Slot::ArrayElement);
            self.check(cx, c, elem);
        }
        self.array_of(elem, Some(kids.len() as i128))
    }

    /// ch03 R21: against `Array[E, N]`, `vector[E, N]` or `mask[N]`.
    fn check_array(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        let bare = self.fir.tys.unqual(want);
        let elem = if self.fir.tys.tag(bare) == TyTag::Nominal {
            let def = DefId(self.fir.tys.a(bare));
            let args = self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec();
            match self.prelude.generic_index(def) {
                Some(gty::ARRAY) | Some(gty::VECTOR) => args.first().copied(),
                Some(gty::MASK) => Some(self.fir.tys.prim(PrimKind::Bool)),
                _ => None,
            }
        } else {
            None
        };
        let Some(elem) = elem else {
            let s = self.synth_array(cx, node);
            return self.subsume(cx, node, s, want);
        };
        let kids = cx.kids(node);
        let take = if is_repeat(cx, node) { 1 } else { kids.len() };
        for &c in kids.iter().take(take) {
            cx.site(NodeKind::ArrayLit, Slot::ArrayElement);
            self.check(cx, c, elem);
        }
        want
    }

    fn array_of(&mut self, elem: TyId, n: Option<i128>) -> TyId {
        let head = self.prelude.generics[gty::ARRAY];
        let usize_ty = self.fir.tys.prim(PrimKind::Usize);
        let count = match n {
            Some(v) => self.fir.tys.const_ty(fors_fir::ConstValue::I(v), usize_ty),
            None => TY_ERROR,
        };
        self.fir.tys.nominal_of(head, &[elem, count])
    }

    /// A comptime-constant `usize` written as an array repeat count: a
    /// literal or a `const` whose value lowering already folded.
    fn const_usize(&mut self, cx: &mut BodyCx, node: usize) -> Option<i128> {
        match cx.kind(node) {
            NodeKind::Literal => {
                let (a, b) = cx.f.tree.token_range(node);
                (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
                    .find(|&i| cx.f.tokens.kinds[i] == TokenKind::Int)
                    .and_then(|i| parse_int_literal(cx.f.tokens.text(i, cx.f.source)))
            }
            NodeKind::NameExpr => match cx.f.uses.target_of(node as u32) {
                Some(ResolvedTarget::Entity(Entity::Item { file, decl })) => {
                    let def = self.defs.def_of(file, decl);
                    let v = self.fir.sigs.const_val(def);
                    (v != fors_fir::ty::NO_CONST)
                        .then(|| self.fir.tys.const_value(v))
                        .and_then(|c| c.as_int())
                }
                _ => None,
            },
            _ => None,
        }
    }

    // -------------------------------------------------------- closures

    /// R35, SYNTH half: every `cparam` must carry a type.
    fn synth_closure(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let cparams: Vec<usize> = kids
            .iter()
            .copied()
            .filter(|&c| cx.kind(c) == NodeKind::CParam)
            .collect();
        let body = kids
            .iter()
            .copied()
            .find(|&c| cx.kind(c) != NodeKind::CParam);
        let mut ps: Vec<(Conv, TyId)> = Vec::new();
        let mut bad = false;
        for &p in &cparams {
            let annot = cx.f.tree.children(p).find(|&c| is_type_node(cx.kind(c)));
            let ty = match annot {
                Some(a) => self.lower_annotation(cx, a),
                None => {
                    bad = true;
                    TY_ERROR
                }
            };
            cx.bind(p as u32, ty, LocalKind::Value);
            ps.push((conv_of_cparam(cx, p), ty));
        }
        if bad {
            self.bemit(cx, node, 35, 35, "in SYNTH mode every closure parameter must carry a type; a closure parameter's type is never inferred from the body".to_string());
        }
        let saved = cx.enter_closure(true, TY_ERROR, NO_TY);
        let result = match body {
            Some(b) if cx.kind(b) == NodeKind::Block => self.synth_block(cx, b),
            Some(b) => self.synth(cx, b),
            None => TY_UNIT,
        };
        cx.leave_closure(saved);
        if bad {
            return TY_ERROR;
        }
        if ps.len() > MAX_PARAMS {
            self.bemit(cx, node, 35, 35, format!("implementation limit: a closure has {} parameters; at most {MAX_PARAMS} are supported", ps.len()));
            return TY_ERROR;
        }
        let id = self.fir.tys.intern_fn_ty(&ps, result, NO_TY, true);
        self.fir.tys.fn_ty(id)
    }

    /// R35, CHECK half: the `fn` type supplies the parameter types.
    fn check_closure(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        let bare = self.fir.tys.unqual(want);
        if self.fir.tys.tag(bare) != TyTag::Fn {
            let s = self.synth_closure(cx, node);
            return self.subsume(cx, node, s, want);
        }
        let id = FnTyId(self.fir.tys.a(bare));
        let (convs, ptys) = self.fir.tys.fn_tys().params(id);
        let (convs, ptys) = (convs.to_vec(), ptys.to_vec());
        let result = self.fir.tys.fn_tys().result(id);
        let raises = self.fir.tys.fn_tys().raises(id);
        let kids = cx.kids(node);
        let cparams: Vec<usize> = kids
            .iter()
            .copied()
            .filter(|&c| cx.kind(c) == NodeKind::CParam)
            .collect();
        let body = kids
            .iter()
            .copied()
            .find(|&c| cx.kind(c) != NodeKind::CParam);
        if cparams.len() != ptys.len() {
            let w = self.show(want);
            self.bemit(
                cx,
                node,
                35,
                35,
                format!(
                    "this closure takes {} parameter(s), but `{w}` declares {}",
                    cparams.len(),
                    ptys.len()
                ),
            );
            return TY_ERROR;
        }
        for (i, &p) in cparams.iter().enumerate() {
            let annot = cx.f.tree.children(p).find(|&c| is_type_node(cx.kind(c)));
            let ty = match annot {
                Some(a) => {
                    let written = self.lower_annotation(cx, a);
                    if written != TY_ERROR && written != ptys[i] {
                        let a1 = self.show(written);
                        let b1 = self.show(ptys[i]);
                        self.bemit(cx, p, 35, 35, format!("this closure parameter is written `{a1}`, but the expected `fn` type declares `{b1}`"));
                    }
                    ptys[i]
                }
                None => ptys[i],
            };
            if conv_written(cx, p).is_some_and(|c| c != convs[i]) {
                self.bemit(
                    cx,
                    p,
                    35,
                    35,
                    "this closure parameter's convention disagrees with the expected `fn` type"
                        .to_string(),
                );
            }
            cx.bind(p as u32, ty, LocalKind::Value);
        }
        let saved = cx.enter_closure(false, result, raises);
        if let Some(b) = body {
            self.check(cx, b, result);
        }
        cx.leave_closure(saved);
        want
    }

    // ------------------------------------------------------- `?` guard

    /// R33's round-6 clause for `?`.
    fn try_guard(&mut self, cx: &mut BodyCx, node: usize) {
        if cx.in_defer_body() {
            let kw = cx.defer_word();
            self.bemit(
                cx,
                node,
                33,
                33,
                format!("no `?` inside a `{kw}` body (ch01 R23c); use a handler instead"),
            );
        }
    }

    // -------------------------------------------------------- patterns

    /// Binds a pattern's names. R50's own checks (and exhaustiveness) are
    /// I7's; this is only what the body needs to have types for.
    pub fn bind_pat(&mut self, cx: &mut BodyCx, pat: usize, s: TyId) {
        match cx.kind(pat) {
            NodeKind::PatLet => cx.bind(pat as u32, s, LocalKind::Value),
            NodeKind::PatTuple => {
                let parts: Vec<TyId> = if self.fir.tys.tag(self.fir.tys.unqual(s)) == TyTag::Tuple {
                    self.fir
                        .tys
                        .args(ArgsId(self.fir.tys.b(self.fir.tys.unqual(s))))
                        .to_vec()
                } else {
                    Vec::new()
                };
                for (i, c) in cx.kids(pat).into_iter().enumerate() {
                    self.bind_pat(cx, c, parts.get(i).copied().unwrap_or(TY_ERROR));
                }
            }
            NodeKind::PatDot | NodeKind::PatPath => {
                let name = last_ident(cx, pat)
                    .map(|i| self.names.intern(cx.f.tokens.text(i, cx.f.source)));
                let payload_tys = name.map(|n| self.variant_payload(s, n)).unwrap_or_default();
                for c in cx.kids(pat) {
                    if cx.kind(c) != NodeKind::Payload {
                        continue;
                    }
                    for (i, sub) in cx.kids(c).into_iter().enumerate() {
                        let t = match cx.kind(sub) {
                            NodeKind::FPat => {
                                let fname = last_ident(cx, sub)
                                    .map(|i| self.names.intern(cx.f.tokens.text(i, cx.f.source)));
                                fname
                                    .and_then(|f| self.record_field(s, name, f))
                                    .unwrap_or(TY_ERROR)
                            }
                            _ => payload_tys.get(i).copied().unwrap_or(TY_ERROR),
                        };
                        match cx.kind(sub) {
                            NodeKind::FPat => {
                                for inner in cx.kids(sub) {
                                    self.bind_pat(cx, inner, t);
                                }
                                if cx.kids(sub).is_empty() {
                                    // `{ x }` shorthand binds the field name.
                                    cx.bind(sub as u32, t, LocalKind::Value);
                                }
                            }
                            _ => self.bind_pat(cx, sub, t),
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// The tuple-payload types of variant `name` of enum `s`, with the
    /// enum's own arguments substituted (`some(let v)` on `Option[i64]`
    /// binds `v: i64`, not `Option`'s parameter).
    fn variant_payload(&mut self, s: TyId, name: fors_index::Symbol) -> Vec<TyId> {
        let bare = self.fir.tys.unqual(s);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return Vec::new();
        }
        let def = DefId(self.fir.tys.a(bare));
        let args = ArgsId(self.fir.tys.b(bare));
        let ms = self.fir.sigs.members(def);
        for i in 0..self.fir.sigs.member_store.count(ms) {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.name == name && m.kind == fors_fir::sig::MemberKind::Variant {
                let xs = self.fir.tys.args(m.args).to_vec();
                return xs
                    .into_iter()
                    .map(|x| self.substituted(def, args, x))
                    .collect();
            }
        }
        Vec::new()
    }

    fn record_field(
        &mut self,
        s: TyId,
        variant: Option<fors_index::Symbol>,
        field: fors_index::Symbol,
    ) -> Option<TyId> {
        let bare = self.fir.tys.unqual(s);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return None;
        }
        let def = DefId(self.fir.tys.a(bare));
        let ms = self.fir.sigs.members(def);
        for i in 0..self.fir.sigs.member_store.count(ms) {
            let m = self.fir.sigs.member_store.get(ms, i);
            match m.kind {
                fors_fir::sig::MemberKind::Field if variant.is_none() && m.name == field => {
                    let args = ArgsId(self.fir.tys.b(bare));
                    return Some(self.substituted(def, args, m.ty));
                }
                fors_fir::sig::MemberKind::Variant if Some(m.name) == variant => {
                    let sub = m.sub;
                    for j in 0..self.fir.sigs.member_store.count(sub) {
                        let f = self.fir.sigs.member_store.get(sub, j);
                        if f.name == field {
                            let args = ArgsId(self.fir.tys.b(bare));
                            return Some(self.substituted(def, args, f.ty));
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }
}

// ------------------------------------------------------------- helpers

fn has_comma(cx: &BodyCx, node: usize) -> bool {
    let (a, b) = cx.f.tree.token_range(node);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .any(|i| cx.f.tokens.kinds[i] == TokenKind::Comma)
}

/// `[x; n]` rather than `[a, b, c]`.
fn is_repeat(cx: &BodyCx, node: usize) -> bool {
    let (a, b) = cx.f.tree.token_range(node);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .any(|i| cx.f.tokens.kinds[i] == TokenKind::Semi)
}

fn last_ident(cx: &BodyCx, node: usize) -> Option<usize> {
    let (a, b) = fors_resolve::paths::own_span(cx.f.tree, node);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .rfind(|&i| cx.f.tokens.kinds[i] == TokenKind::Ident)
}

fn conv_written(cx: &BodyCx, p: usize) -> Option<Conv> {
    let (a, b) = fors_resolve::paths::own_span(cx.f.tree, p);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len())).find_map(|i| {
        match cx.f.tokens.kinds[i] {
            TokenKind::KwLet => Some(Conv::Let),
            TokenKind::KwInout => Some(Conv::Inout),
            TokenKind::KwSink => Some(Conv::Sink),
            TokenKind::Ident if cx.f.tokens.text(i, cx.f.source) == b"set" => Some(Conv::Set),
            _ => None,
        }
    })
}

fn conv_of_cparam(cx: &BodyCx, p: usize) -> Conv {
    conv_written(cx, p).unwrap_or(Conv::Let)
}

/// ch09 R21's closed operator-trait table.
pub fn trait_of(op: TokenKind) -> Option<usize> {
    Some(match op {
        TokenKind::Plus | TokenKind::PlusEq => tr::ADD,
        TokenKind::Minus | TokenKind::MinusEq => tr::SUB,
        TokenKind::Star | TokenKind::StarEq => tr::MUL,
        TokenKind::Slash | TokenKind::SlashEq => tr::DIV,
        TokenKind::Percent | TokenKind::PercentEq => tr::REM,
        TokenKind::Amp | TokenKind::AmpEq => tr::BITAND,
        TokenKind::Pipe | TokenKind::PipeEq => tr::BITOR,
        TokenKind::Caret | TokenKind::CaretEq => tr::BITXOR,
        TokenKind::Shl | TokenKind::ShlEq => tr::SHL,
        TokenKind::Shr | TokenKind::ShrEq => tr::SHR,
        TokenKind::EqEq | TokenKind::NotEq => tr::EQ,
        TokenKind::Lt | TokenKind::Gt | TokenKind::LtEq | TokenKind::GtEq => tr::ORD,
        _ => return None,
    })
}

fn op_text(op: TokenKind) -> &'static str {
    match op {
        TokenKind::Plus | TokenKind::PlusEq => "+",
        TokenKind::Minus | TokenKind::MinusEq => "-",
        TokenKind::Star | TokenKind::StarEq => "*",
        TokenKind::Slash | TokenKind::SlashEq => "/",
        TokenKind::Percent | TokenKind::PercentEq => "%",
        TokenKind::Amp | TokenKind::AmpEq => "&",
        TokenKind::Pipe | TokenKind::PipeEq => "|",
        TokenKind::Caret | TokenKind::CaretEq => "^",
        TokenKind::Shl | TokenKind::ShlEq => "<<",
        TokenKind::Shr | TokenKind::ShrEq => ">>",
        TokenKind::EqEq => "==",
        TokenKind::NotEq => "!=",
        TokenKind::Lt => "<",
        TokenKind::Gt => ">",
        TokenKind::LtEq => "<=",
        TokenKind::GtEq => ">=",
        _ => "this operator",
    }
}

/// The type suffix of an integer literal, if it carries one.
fn int_lit(txt: &[u8]) -> Lit {
    let mut i = 0usize;
    let mut radix = 10u32;
    if txt.len() >= 2 && txt[0] == b'0' {
        match txt[1] | 0x20 {
            b'x' => {
                radix = 16;
                i = 2;
            }
            b'o' => {
                radix = 8;
                i = 2;
            }
            b'b' => {
                radix = 2;
                i = 2;
            }
            _ => {}
        }
    }
    while i < txt.len() && (txt[i] == b'_' || (txt[i] as char).is_digit(radix)) {
        i += 1;
    }
    match suffix_prim(&txt[i..]) {
        Some(p) => Lit::Suffixed(p),
        None => Lit::IntUnsuffixed,
    }
}

fn float_lit(txt: &[u8]) -> Lit {
    let cut = txt.len().saturating_sub(3);
    match suffix_prim(&txt[cut..]) {
        Some(p) if p.is_float() => Lit::Suffixed(p),
        _ => Lit::FloatUnsuffixed,
    }
}

fn suffix_prim(s: &[u8]) -> Option<PrimKind> {
    Some(match s {
        b"i8" => PrimKind::I8,
        b"i16" => PrimKind::I16,
        b"i32" => PrimKind::I32,
        b"i64" => PrimKind::I64,
        b"isize" => PrimKind::Isize,
        b"u8" => PrimKind::U8,
        b"u16" => PrimKind::U16,
        b"u32" => PrimKind::U32,
        b"u64" => PrimKind::U64,
        b"usize" => PrimKind::Usize,
        b"f32" => PrimKind::F32,
        b"f64" => PrimKind::F64,
        _ => return None,
    })
}

/// A `Deferred` target the checker must be silent about (design §7.10).
pub fn silent_defer(r: DeferReason) -> bool {
    matches!(
        r,
        DeferReason::Diagnosed | DeferReason::StdAbsent | DeferReason::Member
    )
}
