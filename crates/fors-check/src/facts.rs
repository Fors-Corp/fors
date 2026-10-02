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

use crate::tape::{PlaceId, UseTape};

/// What a call's callee turned out to be (FMIR datum D2, §4.1).
///
/// I3.5 records the I3 subset: free functions, enum variants and `fn`
/// values. I4 adds method resolution (inherent-before-trait lookup,
/// `Method { def, owner }`); I5 adds the determined generic arguments.
/// A struct literal is not a call: it records [`FactCallee::Undecided`]
/// with one [`Conv::Let`]-like entry per field in
/// [`BodyFacts::arg_convs`] (post-F1 may add a dedicated variant; the
/// shape is frozen while F1 matches on it). An operator records
/// [`FactCallee::Undecided`] with an empty conv row: the operator
/// desugars to its trait method, but I4 resolves no method for it.
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
    /// A resolved method call (I4, R43-R46): the method and its owner
    /// (inherent impl or trait) for R46's diagnostic.
    Method { def: DefId, owner: DefId },
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
    /// F7 (fmir-interpreter.md §4.1's gap): the resolved `Index`/
    /// `IndexMut` impl for `a[i]` on a USER nominal type — `member.rs`'s
    /// `user_index` decided this (R29's unambiguous-impl case only, same
    /// scope as `Field`/`LenBuiltin`) but never recorded it, so lowering
    /// had no fact to read for `a[i]`/`a[i] = v` on e.g. `Buffer`/`Vec`.
    /// `at` is `Index::at`'s method `DefId`; `at_mut` is `IndexMut::
    /// at_mut`'s, when exactly one `IndexMut` impl also matches (absent
    /// otherwise — a write through that index is then unresolved, as
    /// before this fact existed).
    IndexImpl { at: DefId, at_mut: Option<DefId> },
}

// ----------------------------------------------- I8b: D7, D8, D9 (§4.1)

/// D7: which of the two statements a deferred body came from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeferKind {
    Defer,
    ErrDefer,
}

/// D7: the strongest access a deferred body makes to one place (ch01
/// R23d's `let` < `inout` < move summary).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Access {
    Let,
    Inout,
    Move,
}

/// D7: one `defer`/`errdefer` statement, in the shape
/// `fmir-interpreter.md` §3.8 gives `DeferRow` — `fors-lower` turns
/// `body` into a `BlockId` and `stmt_order` into its `u16` by
/// construction, and the verifier asserts against this, never re-derives
/// it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DeferRegionRow {
    /// The `block` (or arm) that directly contains the statement.
    pub scope: u32,
    pub kind: DeferKind,
    /// The statement's own CST node; its body is its `block` child.
    pub body: u32,
    /// Position among the statements of `scope`. Bodies run in ONE
    /// reverse `stmt_order` sequence interleaving both kinds (R23a, R23b).
    pub stmt_order: u32,
}

/// D7: `(body, place root, strongest access)` — R23d's summary, computed
/// once and applied at every exit where the body runs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DeferAccessRow {
    pub body: u32,
    pub root: u32,
    pub access: Access,
}

/// D7/D8: the kind of one exit edge (ch01 R22h, ch02 R16).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExitEdgeKind {
    BlockEnd,
    Return,
    Raise,
    Question,
    Break,
    Continue,
}

/// D7: one exit edge, with the scopes it leaves (innermost first) and the
/// multiset of deferred bodies that run on it, already in the order
/// R23a(2) fixes. `fors-lower` inlines them in exactly this order.
#[derive(Clone, Debug)]
pub struct ExitEdge {
    pub kind: ExitEdgeKind,
    /// The `return`/`raise`/`?`/`break`/`continue` node, or the block
    /// whose `}` this is.
    pub node: u32,
    pub scopes: Vec<u32>,
    /// Indices into [`DeferRegions::rows`], in run order. Only the bodies
    /// whose statement was EXECUTED on the path to this exit are here
    /// (ch01 R23a: it textually precedes the exit; a `}` is after every
    /// statement of its block). `fors_fmir::exit::expected_pending` has no
    /// such cut — it takes a `ScopeRow`'s whole `defers` range — so
    /// `fors-lower` must lay the pool out so that a scope's range at an
    /// edge holds exactly these rows.
    pub defers: Vec<u32>,
}

/// D7 — defer/errdefer decisions (design §13's "Interface to FMIR
/// lowering").
#[derive(Default, Debug)]
pub struct DeferRegions {
    pub rows: Vec<DeferRegionRow>,
    pub accesses: Vec<DeferAccessRow>,
    pub exits: Vec<ExitEdge>,
}

/// D8: what consumed an obligation on one exit edge. The names are
/// `fmir-interpreter.md` §3.5's `Discharge`, in checker coordinates:
/// `fors-lower` turns a node into an `InstId`/`BlockId`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Discharge {
    /// A whole-place move (R22d(i)): the node that moved it.
    MovedAt(u32),
    /// A `defer`/`errdefer` body (R22d(iii), R23d(b)).
    DeferredBody { scope: u32, body: u32 },
    /// A `match` that bound every linear component (R22d(ii)).
    Destructured(u32),
    /// The scope's tail value (R22d(i)'s "the function body's tail
    /// value", generalised to every scope).
    TailValue(u32),
}

/// D8: one obligation, as ch01 R22d states it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ObligationRow {
    /// The scope that owes it.
    pub scope: u32,
    /// The introducing node (`Binding`, `PatLet`, `FPat`, `Param`).
    pub root: u32,
    /// Its interned place, when the body ever used it.
    pub place: Option<PlaceId>,
    pub ty: TyId,
    /// The `let`/`var` statement that introduces the binding, as `(start,
    /// end)` nodes; `(root, root)` for a pattern binding or a parameter. An
    /// exit INSIDE this range — `var b: Own[..] = a.create(1)?;` — happens
    /// before the binding exists: the obligation is not owed there and
    /// carries no [`DischargeRow`] on that edge. Likewise a non-`}` exit
    /// that textually precedes `root` (a `break` written before the
    /// binding in the same loop body): owed means "the binding was
    /// initialised on the path to the edge", which in a structured body is
    /// exactly "declared before it, and not inside its own statement".
    pub decl: (u32, u32),
}

/// D8: one `(exit edge, obligation, discharge)` row. An obligation of a
/// scope being left with NO row on that edge is `fmir-interpreter.md`
/// §3.5's `linear-leak` — a compiler bug, never a trap — which is why the
/// checker reports it as ch01 R22i instead of letting it get here.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DischargeRow {
    /// Index into [`DeferRegions::exits`].
    pub exit: u32,
    pub root: u32,
    pub how: Discharge,
}

/// D8 — linear obligations and discharges.
#[derive(Default, Debug)]
pub struct LinearObligations {
    pub obligations: Vec<ObligationRow>,
    pub discharges: Vec<DischargeRow>,
    /// `lin(T)` per `TyId` this body asked about (ch01 R22a), so lowering
    /// sets `flags.LINEAR` from the checker's answer and never recomputes
    /// it.
    pub lin: Vec<(TyId, bool)>,
}

/// D9 — scoped sources (ch01 R19c(d), R19d): per value, the source place
/// ROOTS its accesses extend. R19a's extents stay M3; this is the source
/// SETS only, which is what R19c and R19d decide.
#[derive(Default, Debug)]
pub struct ScopedSources {
    pub rows: Vec<(u32, Vec<u32>)>,
}

impl ScopedSources {
    pub fn sources_of(&self, node: u32) -> &[u32] {
        self.rows
            .iter()
            .find(|(n, _)| *n == node)
            .map(|(_, v)| &v[..])
            .unwrap_or(&[])
    }
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
    /// [`None`]). In R45's qualified form the receiver is an ordinary first
    /// argument, so a qualified call records BOTH: `recv_conv` (the
    /// receiver parameter's own convention) and `arg_convs[0]` (the same
    /// convention as the first argument row). Argument conventions live in
    /// [`BodyFacts::arg_convs`]: they are variable-length per call and do
    /// not fit the SoA.
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
    /// D7 (I8b): the `defer`/`errdefer` regions and their exit edges.
    pub defer_regions: DeferRegions,
    /// D8 (I8b): the linear obligations, their discharges per exit edge,
    /// and `lin(T)` per `TyId`.
    pub linear_obligations: LinearObligations,
    /// D9 (I8b): the scoped source sets of ch01 R19c(d) and R19d.
    pub scoped_sources: ScopedSources,
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
            defer_regions: DeferRegions::default(),
            linear_obligations: LinearObligations::default(),
            scoped_sources: ScopedSources::default(),
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

    /// Records a projection node's resolved member (D4). First write wins:
    /// intermediate field segments of a greedy-path callee
    /// (`outer.inner.m()`) land here via path resolution; the method
    /// resolution itself overwrites through [`BodyFacts::overwrite_member`].
    pub fn set_member(&mut self, node: u32, m: MemberTarget) {
        if let Some(i) = self.idx(node)
            && self.member[i] == MemberTarget::None
        {
            self.member[i] = m;
        }
    }

    /// Overwrites a projection node's resolved member (D4). ONLY the method
    /// lookup's `record_method_member` may call this: on a 3+-segment
    /// greedy-path callee the intermediate field was already recorded
    /// first-wins, and the method is what lowering must see.
    pub fn overwrite_member(&mut self, node: u32, m: MemberTarget) {
        if let Some(i) = self.idx(node) {
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

    /// Records a call node's receiver convention (D3). First write wins.
    pub fn set_recv_conv(&mut self, node: u32, conv: Conv) {
        if let Some(i) = self.idx(node)
            && self.recv_conv[i].is_none()
        {
            self.recv_conv[i] = Some(conv);
        }
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
