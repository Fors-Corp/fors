//! ch03 (numerics and determinism) in the checker — increment I10, half A
//! (`docs/design/type-checker.md` §8's ch03 rows, §13's I10).
//!
//! Codes are `D00nn`, the rule number (design §14 Q1):
//!
//! - **D0001** (R1): `i128`/`u128` named as a type (`lower::rejected_width`).
//! - **D0004** (R4): an `unchecked_<op>` call in a declaration that does not
//!   carry `@unsafe(invariant: "...")`. ch04 R10 owns the attribute's own
//!   form; this is the call site R4 names.
//! - **D0005** (R5): one numeric primitive where another is expected — no
//!   implicit widening, int<->float or float<->float conversion.
//! - **D0006** (R6): a lossy conversion (`wrap_as`/`sat_as`/`trunc_as`)
//!   whose target is not a numeric primitive.
//! - **D0008** (R8): an `@fastmath(..)` flag outside `{reassoc, contract,
//!   nsz, finite, recip}`.
//! - **D0009** (R9): a `comptime_int`/`comptime_float` value escaping to
//!   runtime without an explicit conversion.
//! - **D0011** (R11): a `reduce` call that is not `reduce(op, xs)` or
//!   `reduce(op, xs, identity: e)` over a sequence.
//! - **D0015** (R15): a scalar accumulator inside a `parallel for`.
//! - **D0018** (R18): an unspecialised generic call inside a `simd` body.
//! - **D0019**/**D0020** (R19, R20): lane counts and `SVec[T]`, in lowering.
//! - **D0021**, **D0022**, **D0024**, **D0025** (R21, R22, R24/R24a, R25):
//!   array literals, in `expr.rs`.
//!
//! The explicit-arithmetic and conversion methods of R4/R6 are REAL
//! declarations now: every numeric primitive has a prelude inherent impl
//! (`fors_fir::prelude::build`), so R43's lookup finds them, R38 types the
//! call, and a name outside the family is R43's ordinary T0043. What
//! lowering reads is published in [`BodyFacts::numeric`] (D11).
//!
//! [`BodyFacts::numeric`]: crate::facts::BodyFacts::numeric

use fors_fir::prelude::{NumericMethodKind, gty, numeric_method_kind};
use fors_fir::sig::Conv;
use fors_fir::ty::{ArgsId, NO_TY, PrimKind, TY_ERROR, TY_NEVER, TyId, TyTag};
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::target::ResolvedTarget;
use fors_syntax::NodeKind;

use crate::body::BodyCx;
use crate::facts::{ArithOp, FactCallee, NumericCallRow, NumericMethod, ReduceRow};
use crate::lower::FileCtx;
use crate::methods::MethodHit;
use crate::tape::Cause;
use crate::wf::Wf;

/// ch03 R8's closed flag set.
const FASTMATH_FLAGS: [&[u8]; 5] = [b"reassoc", b"contract", b"nsz", b"finite", b"recip"];

impl Wf<'_> {
    /// Whether `hit` is one of ch03's language-known numeric methods (a
    /// method of a numeric primitive's prelude inherent impl), and which.
    pub(crate) fn numeric_method(&self, hit: &MethodHit) -> Option<NumericMethod> {
        if !self
            .prelude
            .numeric_impls
            .iter()
            .any(|&(_, d)| d == hit.owner)
        {
            return None;
        }
        let name = self.method_name_of(hit.owner, hit.def)?;
        let ops = [
            ArithOp::Add,
            ArithOp::Sub,
            ArithOp::Mul,
            ArithOp::Div,
            ArithOp::Rem,
            ArithOp::Shl,
            ArithOp::Shr,
            ArithOp::Neg,
        ];
        Some(match numeric_method_kind(self.names.resolve(name))? {
            NumericMethodKind::Arith { mode, op } => {
                let op = ops[op as usize];
                match mode {
                    0 => NumericMethod::Wrap(op),
                    1 => NumericMethod::Sat(op),
                    _ => NumericMethod::Unchecked(op),
                }
            }
            NumericMethodKind::Conv(0) => NumericMethod::WrapAs,
            NumericMethodKind::Conv(1) => NumericMethod::SatAs,
            NumericMethodKind::Conv(_) => NumericMethod::TruncAs,
        })
    }

    fn method_name_of(&self, owner: DefId, mdef: DefId) -> Option<fors_index::Symbol> {
        self.impl_method_names(owner)
            .into_iter()
            .find(|&(_, d)| d == mdef)
            .map(|(n, _)| n)
    }

    /// ch03 R4: "`unchecked_<op>` MUST NOT appear outside a declaration
    /// carrying `@unsafe(invariant: "...")` (ch04 Rule 10; there is no
    /// call-site or block form)". Reported at the call; the attribute's own
    /// well-formedness is ch04 R10's (half B).
    pub(crate) fn unchecked_site(&mut self, cx: &mut BodyCx, node: usize, kind: NumericMethod) {
        let NumericMethod::Unchecked(_) = kind else {
            return;
        };
        if decl_has_attr(cx.f, cx.decl_node(), b"unsafe") {
            return;
        }
        self.bemit_code(
            cx,
            node,
            Code::D(4),
            43,
            "an `unchecked_` operation may appear only inside a declaration carrying `@unsafe(invariant: \"...\")`; there is no call-site or block form (ch03 R4, ch04 R10)".to_string(),
        );
    }

    /// After R38 typed a numeric-method call: R6's target check and the D11
    /// row.
    pub(crate) fn numeric_call_done(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        hit: &MethodHit,
        kind: NumericMethod,
        result: TyId,
    ) {
        let conv = matches!(
            kind,
            NumericMethod::WrapAs | NumericMethod::SatAs | NumericMethod::TruncAs
        );
        if conv && result != TY_ERROR && result != NO_TY && !self.is_numeric_prim(result) {
            let shown = self.show(result);
            self.bemit_code(
                cx,
                node,
                Code::D(6),
                43,
                format!("a lossy numeric conversion converts to a numeric primitive only; `{shown}` is not one (ch03 R6)"),
            );
            return;
        }
        if result == TY_ERROR || result == NO_TY {
            return;
        }
        cx.facts.numeric.calls.push(NumericCallRow {
            call: node as u32,
            method: hit.def,
            owner: hit.owner,
            kind,
            recv: hit.recv_ty,
            result,
        });
    }

    /// Whether `t` is an integer or float primitive.
    pub(crate) fn is_numeric_prim(&self, t: TyId) -> bool {
        let bare = self.fir.tys.unqual(t);
        self.fir.tys.tag(bare) == TyTag::Prim
            && PrimKind::from_u8(self.fir.tys.a(bare) as u8)
                .is_some_and(|p| p.is_integer() || p.is_float())
    }

    /// Whether `t` is ch03 R9's `comptime_int` or `comptime_float`.
    pub(crate) fn is_comptime_ty(&self, t: TyId) -> bool {
        let bare = self.fir.tys.unqual(t);
        self.fir.tys.tag(bare) == TyTag::Nominal && {
            let d = DefId(self.fir.tys.a(bare));
            d == self.prelude.comptime_int || d == self.prelude.comptime_float
        }
    }

    /// ch03 R5 and R9 at R10's subsumption: the two mismatches chapter 3
    /// names, under its own codes. `None` for every other mismatch (ch09's
    /// T0026).
    ///
    /// R9's escape is reported wherever it happens. R5's is reported under
    /// D0005 only at the value of an ANNOTATED `let`/`var` initializer
    /// (`r5_site`): that is where `03-numerics/implicit-widen-rejected`
    /// places it ("diagnosed at the let_stmt initializer"), while the ch09
    /// corpus asserts T0026 for the same fault at an operand
    /// (`mixed-width-operands-rejected`, `for-element-type-mismatch-
    /// rejected`) and at a call argument (`literal-default-ignores-later-
    /// use-rejected`, `projection-arg-before-head-final-check-rejected`).
    /// Each corpus is kept at the site it names; one code per fault is the
    /// owner's call.
    pub(crate) fn numeric_mismatch(
        &mut self,
        s: TyId,
        want: TyId,
        r5_site: bool,
    ) -> Option<(Code, String)> {
        if self.is_comptime_ty(s) && !self.is_comptime_ty(want) {
            let (sn, wn) = (self.show(s), self.show(want));
            return Some((
                Code::D(9),
                format!(
                    "expected `{wn}`, found `{sn}`: a `{sn}` value is comptime-only and does not escape to runtime without an explicit conversion; write `as {wn}` (ch03 R9)"
                ),
            ));
        }
        if r5_site
            && self.is_numeric_prim(s)
            && self.is_numeric_prim(want)
            && self.fir.tys.unqual(s) != self.fir.tys.unqual(want)
        {
            let (sn, wn) = (self.show(s), self.show(want));
            return Some((
                Code::D(5),
                format!(
                    "expected `{wn}`, found `{sn}`: there is no implicit numeric conversion, so `{sn}` does not stand in for `{wn}`; convert explicitly with `as {wn}` (ch03 R5)"
                ),
            ));
        }
        None
    }

    /// ch03 R9: a runtime `let`/`var` of a comptime-only type.
    pub(crate) fn comptime_binding(&mut self, cx: &mut BodyCx, node: usize, ty: TyId) {
        if !self.is_comptime_ty(ty) || cx.in_region(NodeKind::ComptimeBlock).is_some() {
            return;
        }
        let shown = self.show(ty);
        self.bemit_code(
            cx,
            node,
            Code::D(9),
            31,
            format!("a runtime binding cannot hold a `{shown}`: the type is comptime-only; bind the value after an explicit conversion to a fixed-width type (ch03 R9)"),
        );
    }

    /// ch03 R8: `@fastmath(flags)` with `flags` a subset of the closed set.
    pub(crate) fn fastmath_flags(&mut self, cx: &mut BodyCx, stmt: usize) {
        for a in cx.kids(stmt) {
            if cx.kind(a) != NodeKind::Attribute || !attr_is(cx.f, a, b"fastmath") {
                continue;
            }
            for arg in cx.kids(a) {
                if cx.kind(arg) != NodeKind::AttrArg {
                    continue;
                }
                let (s, e) = cx.f.tree.token_range(arg);
                let words: Vec<&[u8]> = (s as usize..(e as usize).min(cx.f.tokens.kinds.len()))
                    .filter(|&i| cx.f.tokens.kinds[i] == TokenKind::Ident)
                    .map(|i| cx.f.tokens.text(i, cx.f.source))
                    .collect();
                if words.len() == 1 && FASTMATH_FLAGS.contains(&words[0]) {
                    continue;
                }
                let shown = String::from_utf8_lossy(
                    &cx.f.source[cx.range(arg).0 as usize..cx.range(arg).1 as usize],
                )
                .trim()
                .to_string();
                self.bemit_code(
                    cx,
                    arg,
                    Code::D(8),
                    31,
                    format!("`{shown}` is not a `@fastmath` flag: the flags are exactly `reassoc`, `contract`, `nsz`, `finite` and `recip` (ch03 R8)"),
                );
                return;
            }
        }
    }

    /// ch03 R15: inside a `parallel for`, an assignment that accumulates
    /// into a scalar declared outside the loop. The loop is named; the fix
    /// is an explicit `reduce`.
    pub(crate) fn accumulator_in_parallel(
        &mut self,
        cx: &mut BodyCx,
        assign: usize,
        place: usize,
        rhs: &[usize],
        compound: bool,
    ) {
        let Some(region) = cx.in_region(NodeKind::ParallelForStmt) else {
            return;
        };
        let region = region as usize;
        let Some(intro) = local_root(cx, place) else {
            return;
        };
        let end = cx.f.tree.subtree_end(region);
        if (intro as usize) >= region && (intro as usize) < end {
            return;
        }
        let reads_itself = compound
            || rhs.iter().any(|&r| {
                let e = cx.f.tree.subtree_end(r);
                (r..e).any(|n| cx.kind(n) == NodeKind::NameExpr && local_root(cx, n) == Some(intro))
            });
        if !reads_itself {
            return;
        }
        let header = loop_header(cx, region);
        let name = String::from_utf8_lossy(
            &cx.f.source[cx.range(place).0 as usize..cx.range(place).1 as usize],
        )
        .trim()
        .to_string();
        self.bemit_code(
            cx,
            assign,
            Code::D(15),
            31,
            format!("`{header}` accumulates into the scalar `{name}`, declared outside it: a scalar accumulator loop is never parallelised or turned into a reduction implicitly; write the reduction explicitly with `reduce(op, xs)` (ch03 R15)"),
        );
    }

    /// ch03 R18: an unspecialised generic call inside a `simd` body.
    pub(crate) fn specialize_in_simd(&mut self, cx: &mut BodyCx, node: usize, def: DefId) {
        if cx.in_region(NodeKind::SimdForStmt).is_none() {
            return;
        }
        if self.defs.get(def).is_none() || self.arity(def) == 0 {
            return;
        }
        if self.fir.sigs.is_specialize(def) {
            return;
        }
        let name = self.head_name(def);
        self.bemit_code(
            cx,
            node,
            Code::D(18),
            38,
            format!("`{name}` is generic and not `@specialize`, so inside a `simd` body this call would go through a witness table; an unspecialised call is not allowed here — mark `{name}` `@specialize` (ch03 R18)"),
        );
    }

    /// ch03 R11/R11a: `reduce(op, xs)` and `reduce(op, xs, identity: e)`.
    /// `xs` is a `Slice[T]`, `Array[T, N]` or `vector[T, N]`; `op` is checked
    /// against `fn(let T, let T) -> T` (a bare operator there is R37's CHECK
    /// form); `e` against `T`; the call is a `T`.
    pub(crate) fn reduce_call(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        args: &[usize],
        expected: Option<TyId>,
    ) -> TyId {
        cx.facts.set_callee(node as u32, FactCallee::Undecided);
        let mut positional: Vec<usize> = Vec::new();
        let mut identity: Option<usize> = None;
        let mut bad = false;
        for &a in args {
            if cx.kind(a) == NodeKind::NamedArg {
                let label = first_ident(cx.f, a);
                let value = cx.kids(a).first().copied();
                if label == Some(b"identity".as_slice()) && identity.is_none() && value.is_some() {
                    identity = value;
                } else {
                    if !bad {
                        self.bemit_code(
                            cx,
                            a,
                            Code::D(11),
                            37,
                            "`reduce` takes exactly one named argument, `identity:` (ch03 R11a)"
                                .to_string(),
                        );
                    }
                    bad = true;
                    if let Some(v) = value {
                        self.synth(cx, v);
                    }
                }
            } else {
                positional.push(a);
            }
        }
        if positional.len() != 2 {
            if !bad {
                self.bemit_code(
                    cx,
                    node,
                    Code::D(11),
                    39,
                    format!("`reduce` is called as `reduce(op, xs)` or `reduce(op, xs, identity: e)`; this call has {} positional argument(s) (ch03 R11)", positional.len()),
                );
            }
            for &a in &positional {
                if cx.kind(a) != NodeKind::BareOp {
                    self.synth(cx, a);
                }
            }
            if let Some(e) = identity {
                self.synth(cx, e);
            }
            return TY_ERROR;
        }
        let (op, xs) = (positional[0], positional[1]);
        let st = self.synth(cx, xs);
        let elem = self.sequence_elem(st);
        if elem.is_none() && st != TY_ERROR && st != NO_TY && st != TY_NEVER {
            let shown = self.show(st);
            self.bemit_code(
                cx,
                xs,
                Code::D(11),
                37,
                format!("`reduce` folds a `Slice[T]`, `Array[T, N]` or `vector[T, N]`; `{shown}` is none of them (ch03 R11)"),
            );
        }
        let elem = elem.unwrap_or(TY_ERROR);
        if elem != TY_ERROR {
            self.arg_tape(cx, node, xs, (1, Conv::Let, st), false);
        }
        // The operator: `fn(let T, let T) -> T`. A bare operator's node is
        // not recorded in D1 (see `ReduceRow::op_fn`).
        let mut op_fn = TY_ERROR;
        if elem == TY_ERROR {
            if cx.kind(op) != NodeKind::BareOp {
                self.synth(cx, op);
            }
        } else {
            let id = self.fir.tys.intern_fn_ty(
                &[(Conv::Let, elem), (Conv::Let, elem)],
                elem,
                NO_TY,
                false,
            );
            let fn_ty = self.fir.tys.fn_ty(id);
            if cx.kind(op) == NodeKind::BareOp {
                let tok = bare_op_token(cx, op);
                match tok {
                    Some(t) if crate::expr::trait_of(t).is_some() => {
                        self.require_operator(cx, op, elem, t, 37);
                    }
                    _ => {
                        self.bemit(
                            cx,
                            op,
                            37,
                            37,
                            "this bare operator is not a binary arithmetic or bitwise operator"
                                .to_string(),
                        );
                    }
                }
            } else {
                // ch03 R25: a call argument whose parameter type (here
                // `fn(let T, let T) -> T`, `T` already read off `xs`) is
                // complete is a CHECK position.
                cx.site(NodeKind::CallExpr, crate::body::Slot::Argument);
                self.check(cx, op, fn_ty);
            }
            op_fn = fn_ty;
        }
        if let Some(e) = identity {
            if elem == TY_ERROR {
                self.synth(cx, e);
            } else {
                cx.site(NodeKind::CallExpr, crate::body::Slot::Argument);
                self.check(cx, e, elem);
                self.use_value(cx, e, elem, Cause::Explicit(node as u32));
            }
        }
        if elem == TY_ERROR {
            return TY_ERROR;
        }
        cx.facts.numeric.reduces.push(ReduceRow {
            call: node as u32,
            op: op as u32,
            op_fn,
            xs: xs as u32,
            identity: identity.map(|e| e as u32),
            elem,
        });
        match expected {
            Some(w) => self.subsume(cx, node, elem, w),
            None => elem,
        }
    }

    /// The element type of a `Slice[T]`, `Array[T, N]` or `vector[T, N]`.
    pub(crate) fn sequence_elem(&mut self, t: TyId) -> Option<TyId> {
        let bare = self.fir.tys.unqual(t);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return None;
        }
        let def = DefId(self.fir.tys.a(bare));
        match self.prelude.generic_index(def) {
            Some(gty::SLICE) | Some(gty::ARRAY) | Some(gty::VECTOR) => self
                .fir
                .tys
                .args(ArgsId(self.fir.tys.b(bare)))
                .first()
                .copied(),
            _ => None,
        }
    }

    /// ch03 R23's broadcast constructors: the element type `splat` takes on
    /// `vector[T, N]` (`T`) or `mask[N]` (`bool`), when `head` is one.
    pub(crate) fn splat_elem(&mut self, head: TyId) -> Option<TyId> {
        let bare = self.fir.tys.unqual(head);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return None;
        }
        let def = DefId(self.fir.tys.a(bare));
        match self.prelude.generic_index(def) {
            Some(gty::VECTOR) => self
                .fir
                .tys
                .args(ArgsId(self.fir.tys.b(bare)))
                .first()
                .copied(),
            Some(gty::MASK) => Some(self.fir.tys.prim(PrimKind::Bool)),
            _ => None,
        }
    }
}

/// Whether the attribute node `a` is `@name`.
pub(crate) fn attr_is(f: &FileCtx, a: usize, name: &[u8]) -> bool {
    let (s, e) = f.tree.token_range(a);
    let mut sig = (s as usize..(e as usize).min(f.tokens.kinds.len()))
        .filter(|&i| !f.tokens.kinds[i].is_trivia());
    let _at = sig.next();
    sig.next().is_some_and(|i| {
        f.tokens.kinds[i] == TokenKind::Ident && f.tokens.text(i, f.source) == name
    })
}

/// Whether declaration `decl` carries the attribute `@name`.
pub(crate) fn decl_has_attr(f: &FileCtx, decl: usize, name: &[u8]) -> bool {
    f.tree
        .children(decl)
        .any(|c| f.tree.kinds[c] == NodeKind::Attribute && attr_is(f, c, name))
}

/// The first identifier token a node owns (a named argument's label).
fn first_ident<'s>(f: &FileCtx<'s>, node: usize) -> Option<&'s [u8]> {
    let (s, e) = f.tree.token_range(node);
    (s as usize..(e as usize).min(f.tokens.kinds.len()))
        .find(|&i| f.tokens.kinds[i] == TokenKind::Ident)
        .map(|i| f.tokens.text(i, f.source))
}

/// The operator token a `BareOp` node owns.
fn bare_op_token(cx: &BodyCx, node: usize) -> Option<TokenKind> {
    let (s, e) = cx.f.tree.token_range(node);
    (s as usize..(e as usize).min(cx.f.tokens.kinds.len()))
        .map(|i| cx.f.tokens.kinds[i])
        .find(|k| !k.is_trivia())
}

/// The introducing node of the local a place's first segment names.
fn local_root(cx: &BodyCx, node: usize) -> Option<u32> {
    match cx.kind(node) {
        NodeKind::NameExpr => match cx.f.uses.target_of(node as u32) {
            Some(ResolvedTarget::Local { node: intro }) => Some(intro),
            _ => None,
        },
        NodeKind::FieldExpr | NodeKind::Bracket => {
            let first = cx.f.tree.children(node).next()?;
            local_root(cx, first)
        }
        _ => None,
    }
}

/// A loop's header as written (`parallel for x in xs`), for the message.
fn loop_header(cx: &BodyCx, region: usize) -> String {
    let (start, end) = cx.range(region);
    let body_start =
        cx.f.tree
            .children(region)
            .find(|&c| cx.kind(c) == NodeKind::Block)
            .map_or(end, |b| cx.range(b).0);
    let text = String::from_utf8_lossy(&cx.f.source[start as usize..body_start as usize]);
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}
