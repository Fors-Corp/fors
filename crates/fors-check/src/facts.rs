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
//! Increment I10a keeps the two promises this table made and never kept:
//! D2's determined generic arguments ([`BodyFacts::generic_args`], the
//! `facts.rs` line "I5 adds the determined generic arguments") and D5/D6's
//! decided patterns ([`BodyFacts::patterns`] — I7 decided every pattern
//! and discarded the decision, so an enum or struct `match` could not be
//! lowered at all).
//!
//! Coverage contract: [`BodyFacts::record`] is called exactly once per
//! `synth`/`check` return (the two wrappers in `expr.rs`) and once per
//! `call_expr` return (the `?`-operand bypass in both judgements calls it
//! directly). A node whose type was decided therefore always has an entry;
//! [`NO_TY`] means "never visited", never "visited and unknown" — every
//! undecided form answers [`TY_ERROR`], which is absorbing and recorded.

use fors_fir::constval::ConstValue;
use fors_fir::sig::Conv;
use fors_fir::ty::{NO_TY, TyId};
use fors_index::ids::DefId;

use crate::tape::{PlaceId, UseTape};

/// What a call's callee turned out to be (FMIR datum D2, §4.1).
///
/// I3.5 records the I3 subset: free functions, enum variants and `fn`
/// values. I4 adds method resolution (inherent-before-trait lookup,
/// `Method { def, owner }`). The determined generic arguments were promised
/// to I5 and landed in I10a, beside the callee rather than inside it:
/// [`BodyFacts::generic_args`].
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

// --------------------------------------------- I10a: D5, D6, D2's arguments

/// D5: what one decided pattern node tests (I7's decision, published for
/// lowering by I10a). `Wild` tests nothing and binds nothing; everything
/// else is named by ids, never by text.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PatShape {
    /// Visited, but nothing was decided: a parse-error pattern node, or an
    /// error path that reported and stopped. Absorbing, exactly like
    /// [`FactCallee::Undecided`] — lowering must refuse the body rather
    /// than read it as a wildcard.
    Undecided,
    /// `_`, or an omitted component's stand-in: tests nothing.
    Wild,
    /// `let n`: binds the component it faces. [`PatFactRow::node`] is the
    /// `PatLet`/`Binding` node, which is the binding's slot in the body's
    /// local table (the same key [`ObligationRow::root`] uses).
    Bind {
        /// How lowering must take the component: [`Conv::Let`] when the
        /// checker answered `Copyable` for [`PatFactRow::ty`] (a copy),
        /// [`Conv::Sink`] otherwise (a move — ch01 R22d(ii)'s
        /// destructuring). The checker decides this; lowering never re-asks.
        conv: Conv,
    },
    /// A literal or `const` pattern, by its comptime value row (R53/R54
    /// make an equal constant and literal the same constructor).
    Lit(ConstValue),
    /// An enum variant, by its enum and the variant's member index.
    Variant { en: DefId, index: u32 },
    /// A struct pattern, by its declaration. Each child carries the FIELD
    /// index it matches in [`PatFactRow::slot`]; an omitted field has no
    /// child at all (ch09 R50's "omitted fields match anything").
    Struct { def: DefId },
    /// A tuple pattern of `len` components, in position order.
    Tuple { len: u32 },
}

/// [`PatFactRow::slot`] at a pattern root: no parent component.
pub const NO_PAT_SLOT: u32 = u32::MAX;

/// D5: one node of a decided pattern tree. Children are a contiguous span
/// of [`PatternFacts::subs`], exactly like [`PatStore`](crate::pat::PatStore)'s
/// own arena — but here `_` and `let n` are DISTINCT rows, because lowering
/// must bind the one and not the other.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PatFactRow {
    pub shape: PatShape,
    /// The pattern's own CST node.
    pub node: u32,
    /// The type the pattern faces, with the scrutinee's arguments already
    /// substituted (R51).
    pub ty: TyId,
    /// `(start, len)` into [`PatternFacts::subs`], in the order this node
    /// tests its components.
    pub subs: (u32, u32),
    /// Which component of the PARENT this node matches: the struct field
    /// index, the variant payload ordinal, or the tuple position.
    /// [`NO_PAT_SLOT`] at a root.
    pub slot: u32,
}

/// D6: one `match` arm, or one `let`/`var` destructuring (which is a
/// one-arm match by R31/R52).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PatArmRow {
    /// The `match` node, or the `let`/`var` statement.
    pub owner: u32,
    /// Position among `owner`'s arms, in source order: R54's order, which
    /// is the order lowering must test them in.
    pub order: u32,
    /// The arm's pattern node (`Arm`'s first child, or the `Binding`/
    /// `TupleBinding`).
    pub pat: u32,
    /// Index into [`PatternFacts::nodes`] of this arm's pattern root.
    pub root: u32,
}

/// D6: the scrutinee of one `match` (or one destructuring) and R53's
/// answer about it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ScrutineeRow {
    /// The `match` node, or the `let`/`var` statement.
    pub owner: u32,
    /// The scrutinee's decided type.
    pub ty: TyId,
    /// R53: whether the arms cover it. A `let` destructuring is
    /// irrefutable (R31/R52) and records `true`. A `match` the checker
    /// could not decide (R55's budget, a scrutinee that failed to type)
    /// records NO row at all, so lowering refuses the body instead of
    /// guessing.
    pub exhaustive: bool,
}

/// D5/D6 — the decided patterns (I10a). I7 decides every pattern and used
/// to discard the decision; lowering cannot lower an enum or struct match
/// without it.
#[derive(Default, Debug)]
pub struct PatternFacts {
    pub nodes: Vec<PatFactRow>,
    pub subs: Vec<u32>,
    pub arms: Vec<PatArmRow>,
    pub scrutinees: Vec<ScrutineeRow>,
    /// The rows still being filled, innermost last, each with the children
    /// registered under it so far. Empty between patterns: a pattern walk
    /// opens and closes every row it visits, and an arm's body is typed
    /// only after its pattern closed, so a nested `match` always starts
    /// from an empty stack.
    open: Vec<(u32, Vec<u32>)>,
    /// The last ROOT row closed, which is the arm the caller just checked.
    last_root: Option<u32>,
}

impl PatternFacts {
    /// The children of `node` (an index into [`PatternFacts::nodes`]).
    pub fn subs_of(&self, node: u32) -> &[u32] {
        let (s, l) = self.nodes[node as usize].subs;
        &self.subs[s as usize..(s + l) as usize]
    }

    /// Opens a row for one pattern node and makes it the parent of whatever
    /// its judgement visits next. Paired with exactly one
    /// [`PatternFacts::close`].
    pub(crate) fn open(&mut self, node: u32, ty: TyId) -> u32 {
        let idx = self.nodes.len() as u32;
        self.nodes.push(PatFactRow {
            shape: PatShape::Undecided,
            node,
            ty,
            subs: (0, 0),
            slot: NO_PAT_SLOT,
        });
        if let Some(frame) = self.open.last_mut() {
            frame.1.push(idx);
        } else {
            self.last_root = None;
        }
        self.open.push((idx, Vec::new()));
        idx
    }

    /// Closes the innermost open row, writing its children's span.
    pub(crate) fn close(&mut self) {
        let Some((idx, kids)) = self.open.pop() else {
            return;
        };
        let start = self.subs.len() as u32;
        self.subs.extend_from_slice(&kids);
        self.nodes[idx as usize].subs = (start, kids.len() as u32);
        if self.open.is_empty() {
            self.last_root = Some(idx);
        }
    }

    /// A childless row the judgement adds without recursing: an omitted
    /// component's wildcard stand-in, or the `{ x }` field shorthand's
    /// binding.
    pub(crate) fn leaf(&mut self, node: u32, ty: TyId, shape: PatShape) -> u32 {
        let idx = self.nodes.len() as u32;
        self.nodes.push(PatFactRow {
            shape,
            node,
            ty,
            subs: (0, 0),
            slot: NO_PAT_SLOT,
        });
        match self.open.last_mut() {
            Some(frame) => frame.1.push(idx),
            None => self.last_root = Some(idx),
        }
        idx
    }

    /// Sets the innermost open row's decided shape.
    pub(crate) fn shape(&mut self, shape: PatShape) {
        if let Some(&(idx, _)) = self.open.last() {
            self.nodes[idx as usize].shape = shape;
        }
    }

    /// Gives the child just registered its component index in this node.
    pub(crate) fn slot_last(&mut self, slot: u32) {
        if let Some((_, kids)) = self.open.last()
            && let Some(&k) = kids.last()
        {
            self.nodes[k as usize].slot = slot;
        }
    }

    /// Puts the open row's children into COMPONENT order: a `{ }` payload
    /// may name its fields in any order, and lowering wants field order.
    /// Stable, so a child with no component ([`NO_PAT_SLOT`], a name that
    /// is no field) keeps its written position at the end.
    pub(crate) fn sort_children(&mut self) {
        let Some(mut kids) = self.open.last_mut().map(|f| std::mem::take(&mut f.1)) else {
            return;
        };
        kids.sort_by_key(|&k| self.nodes[k as usize].slot);
        if let Some(f) = self.open.last_mut() {
            f.1 = kids;
        }
    }

    /// The root row of the pattern the caller just checked.
    pub(crate) fn last_root(&self) -> Option<u32> {
        self.last_root
    }

    /// The arms of one `match`/destructuring node, in source order.
    pub fn arms_of(&self, owner: u32) -> impl Iterator<Item = &PatArmRow> {
        self.arms.iter().filter(move |a| a.owner == owner)
    }

    /// R53's answer for one `match`/destructuring node, when the checker
    /// decided it.
    pub fn scrutinee_of(&self, owner: u32) -> Option<&ScrutineeRow> {
        self.scrutinees.iter().find(|r| r.owner == owner)
    }
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
    /// D2 (rest, I10a): `(call node, determined generic arguments)` — the
    /// `facts.rs` promise "I5 adds the determined generic arguments",
    /// finally kept. The arguments are `TyId`s in the checker's own
    /// `TyStore`, after R38-R41 and R20's normalisation, in R38(a)'s
    /// order: the CONTAINER's parameters (an inherent impl's, a trait's
    /// `Self` at ordinal 0) and then the callee's own. A brand argument is
    /// its brand type, a const argument its value row — both are already
    /// `TyId`s here. A non-generic callee records an EMPTY row, which marks
    /// the site visited and monomorphic; [`NO_TY`] in a row is a slot the
    /// call did not determine, and the call's own type is then [`crate::
    /// facts::BodyFacts::ty_of`]'s `TY_ERROR`. A struct literal records
    /// the struct's arguments the same way. Pushed in source order; at most
    /// one row per node.
    pub generic_args: Vec<(u32, Vec<TyId>)>,
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
    /// D5/D6 (I10a): the decided patterns, per `match` and per `let`
    /// destructuring.
    pub patterns: PatternFacts,
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
            generic_args: Vec::new(),
            tape: UseTape::new(),
            defer_regions: DeferRegions::default(),
            linear_obligations: LinearObligations::default(),
            scoped_sources: ScopedSources::default(),
            patterns: PatternFacts::default(),
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

    /// Records a call or struct-literal node's determined generic arguments
    /// (D2, rest). First write wins, like [`BodyFacts::set_callee`]: the
    /// node's own judgement records, and a re-visit of the same node (a
    /// `check` that fell back to `synth`) must not append a second row.
    pub fn set_generic_args(&mut self, node: u32, args: Vec<TyId>) {
        if self.idx(node).is_some() && !self.generic_args.iter().any(|&(n, _)| n == node) {
            self.generic_args.push((node, args));
        }
    }

    /// The determined generic arguments of a call node, or `&[]` when the
    /// callee is not generic (and when the node was never recorded: use
    /// [`BodyFacts::records_generic_args`] to tell the two apart).
    pub fn generic_args_of(&self, node: u32) -> &[TyId] {
        self.generic_args
            .iter()
            .find(|&&(n, _)| n == node)
            .map(|(_, v)| &v[..])
            .unwrap_or(&[])
    }

    /// Whether `node` has a determined-generic-arguments row at all.
    pub fn records_generic_args(&self, node: u32) -> bool {
        self.generic_args.iter().any(|&(n, _)| n == node)
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
