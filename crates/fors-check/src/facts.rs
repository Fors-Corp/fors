//! `BodyFacts`: the typed side table FMIR lowering reads (design
//! `docs/design/type-checker.md` §4.2, `docs/design/fmir-interpreter.md`
//! §4.1 [HOLE-4]).
//!
//! Increment I3.5 (strictly additive I3 follow-up): a `BodyFacts` struct of
//! arrays filled by the existing `synth`/`check` recursion, plus the
//! retained [`UseTape`]. Every increment from F1 onward reads this instead
//! of re-deriving types; the checker itself never reads it back, so a
//! facts bug can only starve lowering, never mis-check a program.
//!
//! Coverage contract: [`BodyFacts::record`] is called exactly once per
//! `synth`/`check` return (the two wrappers in `expr.rs`) and once per
//! `call_expr` return (the `?`-operand bypass in both judgements calls it
//! directly). A node whose type was decided therefore always has an entry;
//! [`NO_TY`] means "never visited", never "visited and unknown" — every
//! undecided form answers [`TY_ERROR`], which is absorbing and recorded.

use fors_fir::sig::Conv;
use fors_fir::ty::{NO_TY, TyId};
use fors_index::ids::DefId;

use crate::tape::UseTape;

/// What a call's callee turned out to be (FMIR datum D2, §4.1).
///
/// I3.5 records the I3 subset: free functions, enum variants and `fn`
/// values. I4 adds method resolution (inherent-before-trait lookup,
/// `TraitMethod`); I5 adds the determined generic arguments.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FactCallee {
    /// Never visited (not "undecided": see [`FactCallee::Undecided`]).
    None,
    /// A non-generic function item.
    Direct(DefId),
    /// A tuple variant construction: `(enum def, member index)`.
    Variant { en: DefId, index: u32 },
    /// A value of `fn` or closure type (R7).
    ValueFn,
    /// Visited, but this increment does not type the callee (a method or a
    /// generic call: I4's / I5's). Silent and absorbing.
    Undecided,
}

/// A resolved member use (FMIR datum D4, §4.1).
///
/// I3.5 records struct fields and the `len` builtin. Projections behind a
/// bound and enum-variant construction through patterns are I6's; method
/// receivers are I4's.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MemberTarget {
    /// Never visited.
    None,
    /// `(head def, field index)` per projection.
    Field { head: DefId, index: u32 },
    /// The `len` builtin on `Array`/`Slice`/`vector` (R42).
    LenBuiltin { head: DefId },
}

/// One body's typed side table, indexed by `node - start` exactly like
/// [`BodyCx`](crate::body::BodyCx)'s other per-node vectors: one bounds
/// check, no hashing. Sized once from the declaration's subtree; nodes
/// outside the range are never recorded (closure bodies share the owner's
/// table when they lie inside it, and are dropped otherwise — I9's query
/// engine re-keys `check_body` before that matters).
#[derive(Debug)]
pub struct BodyFacts {
    /// The declaration this table belongs to.
    pub owner: DefId,
    start: u32,
    end: u32,
    /// D1: per-expression type. [`NO_TY`] = never visited.
    expr_ty: Vec<TyId>,
    /// D2: resolved callee per call node.
    callee: Vec<FactCallee>,
    /// D3: receiver convention per method call (I4 fills; I3.5 leaves
    /// [`None`]). Argument conventions live in [`BodyFacts::arg_convs`]:
    /// they are variable-length per call and do not fit the SoA.
    recv_conv: Vec<Option<Conv>>,
    /// D4: resolved member per projection/construction node.
    member: Vec<MemberTarget>,
    /// D3 (rest): `(call node, parameter convention per typed argument)`.
    /// Pushed in source order; at most one row per call node.
    pub arg_convs: Vec<(u32, Vec<Conv>)>,
    /// The body's retained use tape (I8's flow pass consumes it from here
    /// once lowering owns the pipeline; until then it is the same tape the
    /// checker always emitted).
    pub tape: UseTape,
}

impl BodyFacts {
    pub fn new(owner: DefId, decl: u32, end: u32) -> BodyFacts {
        let n = (end - decl) as usize;
        BodyFacts {
            owner,
            start: decl,
            end,
            expr_ty: vec![NO_TY; n],
            callee: vec![FactCallee::None; n],
            recv_conv: vec![None; n],
            member: vec![MemberTarget::None; n],
            arg_convs: Vec::new(),
            tape: UseTape::new(),
        }
    }

    fn idx(&self, node: u32) -> Option<usize> {
        if node >= self.start && node < self.end {
            Some((node - self.start) as usize)
        } else {
            None
        }
    }

    /// Records `node`'s decided type. Last write wins: `check` falls back
    /// to `synth` + subsumption for the same node, and the checked-against
    /// type is the node's type (R10 is applied once, at the outermost
    /// type, so what the wrapper returns is what lowering must see).
    pub fn record(&mut self, node: u32, ty: TyId) {
        if let Some(i) = self.idx(node) {
            self.expr_ty[i] = ty;
        }
    }

    /// Records a call node's callee (D2). First write wins: `call_expr`
    /// records the classification and the `check`/`synth` wrapper only
    /// touches [`BodyFacts::record`].
    pub fn set_callee(&mut self, node: u32, c: FactCallee) {
        if let Some(i) = self.idx(node)
            && self.callee[i] == FactCallee::None
        {
            self.callee[i] = c;
        }
    }

    /// Records a call node's per-argument conventions (D3, rest).
    pub fn set_arg_convs(&mut self, node: u32, convs: Vec<Conv>) {
        if self.idx(node).is_some() && !self.arg_convs.iter().any(|&(n, _)| n == node) {
            self.arg_convs.push((node, convs));
        }
    }

    /// Records a projection node's resolved member (D4). First write wins.
    pub fn set_member(&mut self, node: u32, m: MemberTarget) {
        if let Some(i) = self.idx(node)
            && self.member[i] == MemberTarget::None
        {
            self.member[i] = m;
        }
    }

    /// The decided type of `node`, or [`NO_TY`] when never visited.
    pub fn ty_of(&self, node: u32) -> TyId {
        self.idx(node).map(|i| self.expr_ty[i]).unwrap_or(NO_TY)
    }

    /// The recorded callee of a call node ([`FactCallee::None`] when never
    /// visited).
    pub fn callee_of(&self, node: u32) -> FactCallee {
        self.idx(node)
            .map(|i| self.callee[i])
            .unwrap_or(FactCallee::None)
    }

    /// The recorded member of a projection node.
    pub fn member_of(&self, node: u32) -> MemberTarget {
        self.idx(node)
            .map(|i| self.member[i])
            .unwrap_or(MemberTarget::None)
    }

    /// The recorded receiver convention of a method call (I4 fills this;
    /// I3.5 leaves [`None`]).
    pub fn recv_conv_of(&self, node: u32) -> Option<Conv> {
        self.idx(node).and_then(|i| self.recv_conv[i])
    }

    /// How many nodes have a decided type (the gate test's numerator).
    pub fn typed_nodes(&self) -> usize {
        self.expr_ty.iter().filter(|&&t| t != NO_TY).count()
    }

    /// The node range this table covers (the gate test's denominator walk).
    pub fn range(&self) -> (u32, u32) {
        (self.start, self.end)
    }
}
