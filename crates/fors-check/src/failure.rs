//! ch02 (failure) in the checker — increment I10, half A
//! (`docs/design/type-checker.md` §8's ch02 rows, §13's I10).
//!
//! ch09 R36 types the `raises`/`?`/`else |e|`/`raise` surface; the rules it
//! cites are ch02's and so are their codes (design §14 Q1: `F00nn`, the
//! rule number is the code):
//!
//! - **F0001** (ch02 R1): a call to a `raises` function not immediately
//!   followed by `?` or `else |e| { }`; `?` or `raise` in a function that
//!   declares no `raises`; a `raise` operand that is not of the declared
//!   `raises` type.
//! - **F0002** (ch02 R2): `?` on a call that does not raise, or on anything
//!   that is not a call.
//! - **F0003** (ch02 R3): `?` across two different error types with no
//!   `ErrorFrom[E]` impl for the caller's `F` — exactly ONE lookup, never a
//!   chain.
//! - **F0005** (ch02 R5): a handler after a call that does not raise. A
//!   handler block that neither diverges nor yields the success type keeps
//!   ch09 R26's T0026 (its message cites ch02 R5): `09-types/handler-block-
//!   type-rejected` asserts T0026 for the very program `02-failure/handler-
//!   block-mismatched-type-rejected` cites R5 for, and the corpus that names
//!   a code outranks the one that names only a rule.
//! - **F0009** (ch02 R9): a contract expression with a `secret`-typed
//!   subexpression.
//! - **F0010** (ch02 R10): a contract in a module whose policy is
//!   `.proved` — the proof engine is the future verification chapter's, so
//!   in this compiler it discharges nothing and every such contract is the
//!   compile error R10 requires (no silent runtime fallback).
//! - **F0013** (ch02 R13): an `extern "c"` function that declares `raises`.
//!
//! What lowering needs (FMIR F3) is published in [`BodyFacts::failure`]
//! (D10): per `?` the callee's error type and the propagation edge, per
//! handler the binding and the block, per `raise` the raised type and
//! variant.
//!
//! [`BodyFacts::failure`]: crate::facts::BodyFacts::failure

use fors_fir::prelude::tr;
use fors_fir::subst::{Binding, one_way_match};
use fors_fir::ty::{NO_ARGS, NO_TY, TY_ERROR, TY_NEVER, TyId, TyTag};
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_syntax::NodeKind;

use crate::body::BodyCx;
use crate::facts::{FactCallee, Propagation, RaiseRow, TryRow};
use crate::wf::{Holds, Wf};

/// ch02 R1's clause for a `raise` operand of the wrong type.
pub const WHY_RAISE: &str =
    "`raise` takes a value of the enclosing function's declared `raises` type (ch02 R1)";
/// ch02 R5's clause for a handler block's value.
pub const WHY_HANDLER: &str =
    "an `else |e| { }` block must diverge or yield the call's success type (ch02 R5)";

impl Wf<'_> {
    /// Pushes the value positions of `node` with `code`; returns the mark
    /// [`Wf::pop_yield`] truncates back to.
    pub(crate) fn push_yield(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        code: Code,
        why: &'static str,
    ) -> usize {
        let mark = cx.yield_codes.len();
        let mut out = Vec::new();
        value_positions(cx, node, &mut out);
        for n in out {
            cx.yield_codes.push((n, code, why));
        }
        mark
    }

    pub(crate) fn pop_yield(&mut self, cx: &mut BodyCx, mark: usize) {
        cx.yield_codes.truncate(mark);
    }

    /// ch02 R2/R3 at one `call?`, after R38 determined the callee's `raises`
    /// type `E`: records the propagation edge (D10), or reports F0003 when
    /// `E` differs from the enclosing `F` and no single `ErrorFrom[E]` impl
    /// for `F` bridges them.
    pub(crate) fn try_edge(&mut self, cx: &mut BodyCx, try_node: u32, call: u32, e: TyId) {
        let f = cx.raises;
        if e == NO_TY || e == TY_ERROR || f == NO_TY || f == TY_ERROR {
            return;
        }
        let e = self.normalise(e);
        let f = self.normalise(f);
        let edge = if e == f || self.fir.tys.unqual(e) == self.fir.tys.unqual(f) {
            Some(Propagation::Same)
        } else if e == TY_NEVER {
            // A callee that cannot fail propagates nothing; the edge is
            // never taken and needs no conversion.
            Some(Propagation::Same)
        } else {
            let ef = self.prelude.traits[tr::ERRORFROM];
            let args = self.fir.tys.intern_args(&[e]);
            let tref = self.fir.tys.intern_trait_ref(ef, args);
            match self.holds(f, tref) {
                Holds::Yes => {
                    let bare = self.fir.tys.unqual(f);
                    if matches!(self.fir.tys.tag(bare), TyTag::Param | TyTag::Proj) {
                        Some(Propagation::ErrorFromBound)
                    } else {
                        self.error_from_impl(bare, e)
                            .map(|(impl_def, from_fn)| Propagation::ErrorFrom { impl_def, from_fn })
                    }
                }
                Holds::No => {
                    let (en, fname) = (self.show(e), self.show(f));
                    self.bemit_code(
                        cx,
                        try_node as usize,
                        Code::F(3),
                        36,
                        format!(
                            "`?` cannot send `{en}` into `raises {fname}`: the two error types differ and there is no `impl ErrorFrom[{en}] for {fname}`; `?` performs exactly one `ErrorFrom` lookup and never chains a second (ch02 R3)"
                        ),
                    );
                    None
                }
                Holds::Unknown => None,
            }
        };
        if let Some(edge) = edge {
            cx.facts.failure.tries.push(TryRow {
                node: try_node,
                call,
                callee_raises: e,
                target: f,
                edge,
            });
        }
    }

    /// The one `impl ErrorFrom[E] for F` R12 found (R19: at most one
    /// matches), with its `from` method.
    fn error_from_impl(&mut self, f: TyId, e: TyId) -> Option<(DefId, DefId)> {
        let ef = self.prelude.traits[tr::ERRORFROM];
        let want = self.fir.tys.intern_args(&[e]);
        let mut found = None;
        for r in self.impls.exact(ef, f) {
            let row = self.impls.row(r);
            if row.trait_args == want {
                found = Some(row.def);
                break;
            }
        }
        if found.is_none() {
            let head = self.fir.tys.head_key(f);
            for r in self.impls.bucket(ef, head) {
                let row = self.impls.row(r);
                let arity = self
                    .fir
                    .sigs
                    .generics_store
                    .count(self.fir.sigs.generics(row.def));
                let mut b = Binding::new(&[(row.def, arity as u16)]);
                if !one_way_match(&mut self.fir.tys, row.self_ty, f, &mut b) {
                    continue;
                }
                let ra = if row.trait_args == NO_ARGS {
                    Vec::new()
                } else {
                    self.fir.tys.args_vec(row.trait_args)
                };
                if ra.len() == 1 && one_way_match(&mut self.fir.tys, ra[0], e, &mut b) {
                    found = Some(row.def);
                    break;
                }
            }
        }
        let impl_def = found?;
        let from = self.names.intern(b"from");
        let from_fn = self
            .impl_method_names(impl_def)
            .into_iter()
            .find(|&(n, _)| n == from)
            .map(|(_, d)| d)?;
        Some((impl_def, from_fn))
    }

    /// D10's `raise` row: the raised type and, when the operand names it,
    /// the variant.
    pub(crate) fn record_raise(&mut self, cx: &mut BodyCx, node: usize, value: usize, ty: TyId) {
        if ty == NO_TY || ty == TY_ERROR {
            return;
        }
        let variant = self.raised_variant(cx, value, ty);
        cx.facts.failure.raises.push(RaiseRow {
            node: node as u32,
            value: value as u32,
            ty,
            variant,
        });
    }

    fn raised_variant(&mut self, cx: &mut BodyCx, value: usize, ty: TyId) -> Option<(DefId, u32)> {
        match cx.kind(value) {
            NodeKind::CallExpr => match cx.facts.callee_of(value as u32) {
                FactCallee::Variant { en, index } => Some((en, index)),
                _ => None,
            },
            NodeKind::NameExpr | NodeKind::DotLit => {
                let bare = self.fir.tys.unqual(ty);
                if self.fir.tys.tag(bare) != TyTag::Nominal {
                    return None;
                }
                let en = DefId(self.fir.tys.a(bare));
                if self.fir.sigs.kind(en) != fors_fir::sig::SigKind::Enum {
                    return None;
                }
                let name = self.last_ident(cx, value)?;
                let ms = self.fir.sigs.members(en);
                (0..self.fir.sigs.member_store.count(ms))
                    .find(|&i| {
                        let m = self.fir.sigs.member_store.get(ms, i);
                        m.kind == fors_fir::sig::MemberKind::Variant && m.name == name
                    })
                    .map(|i| (en, i as u32))
            }
            NodeKind::TupleOrParen => {
                let kids = cx.kids(value);
                match kids.as_slice() {
                    [one] => self.raised_variant(cx, *one, ty),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The last identifier token a node owns (a path's final segment).
    pub(crate) fn last_ident(&mut self, cx: &BodyCx, node: usize) -> Option<fors_index::Symbol> {
        let (a, b) = cx.f.tree.token_range(node);
        let i = (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
            .rev()
            .find(|&i| cx.f.tokens.kinds[i] == fors_lex::TokenKind::Ident)?;
        Some(self.names.intern(cx.f.tokens.text(i, cx.f.source)))
    }

    /// ch02 R9: a contract expression MUST NOT contain a `secret`-typed
    /// subexpression (its runtime check is a branch, ch05). Reads the types
    /// the contract was just checked with; reports the outermost offending
    /// node, once.
    pub(crate) fn contract_secret(&mut self, cx: &mut BodyCx, expr: usize) {
        let end = cx.f.tree.subtree_end(expr);
        for n in expr..end {
            let t = cx.facts.ty_of(n as u32);
            if t == NO_TY || t == TY_ERROR {
                continue;
            }
            if self.fir.tys.quals(t).is_secret() {
                let shown = self.show(t);
                self.bemit_code(
                    cx,
                    n,
                    Code::F(9),
                    49,
                    format!(
                        "a contract expression must not contain a `secret` value: this subexpression is `{shown}`, and a contract's runtime check is a branch on it (ch02 R9, ch05)"
                    ),
                );
                return;
            }
        }
    }
}

/// The value positions of `node`: itself, and recursively the tail of a
/// block, every branch block of an `if`, every arm body of a `match`, the
/// inside of parentheses and of a `comptime` block. A mismatch there is
/// the value's fault, not some statement's inside it.
pub(crate) fn value_positions(cx: &BodyCx, node: usize, out: &mut Vec<u32>) {
    out.push(node as u32);
    match cx.kind(node) {
        NodeKind::Block => {
            let kids = cx.kids(node);
            if let (_, Some(last)) = crate::body::split_tail(cx, &kids) {
                value_positions(cx, last, out);
            }
        }
        NodeKind::IfExpr => {
            for c in cx.kids(node) {
                if cx.kind(c) == NodeKind::Block {
                    value_positions(cx, c, out);
                }
            }
        }
        NodeKind::MatchExpr => {
            for c in cx.kids(node) {
                if cx.kind(c) == NodeKind::Arm
                    && let Some(&body) = cx.kids(c).last()
                {
                    value_positions(cx, body, out);
                }
            }
        }
        NodeKind::TupleOrParen | NodeKind::ComptimeBlock => {
            let kids = cx.kids(node);
            if let [one] = kids.as_slice() {
                value_positions(cx, *one, out);
            }
        }
        _ => {}
    }
}
