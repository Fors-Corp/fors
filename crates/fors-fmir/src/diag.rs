//! `verify()`'s output: "source-located diagnostics" (design item 5 of the
//! F0 task list; design §3.11: "A source-located diagnostic, never a trap").

use crate::ids::{BlockId, InstId, ValId};

/// What a [`Diagnostic`] is anchored to, for callers that want to point a
/// human at the offending row without this crate committing to one span
/// representation for every anchor kind (a `ValId` has no `SiteId` of its
/// own — only its defining instruction does; `verify.rs` resolves that
/// indirection when it can).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Anchor {
    Inst(InstId),
    Block(BlockId),
    Val(ValId),
    Decl,
}

/// One rejection reason. Named per the task's required list (`verify()`
/// "must reject at least: a missing secret field, a missing ct_region, a
/// detach without captures, any tile.* op ... two terminators in one block,
/// and a memory op with no alias seed") plus the ch05 Rule 6a/6b rows design
/// §3.11 assigns to the verifier.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagCode {
    MissingSecretField,
    MissingCtRegion,
    DetachWithoutCaptures,
    TileOpPresent,
    TwoTerminators,
    MemoryOpMissingAliasSeed,
    /// ch05 Rule 6a as a verifier-checkable consistency invariant rather
    /// than a computation: `fors-lower` is the one that *propagates* secret
    /// (design §3.11: "R6a, propagation (`fors-lower`)"), but nothing stops
    /// `verify()` from checking any given FMIR already satisfies it — which
    /// is what makes `secret_propagates` testable at F0, before `fors-lower`
    /// exists. [decision: `secret_propagates` is a verifier consistency
    /// check here, not a propagation pass]
    SecretPropagationViolated,
    /// ch05 Rule 6b: branch/loop-bound/`switch_discr`, or an `index`/
    /// `slice_range` bound, derived from secret.
    SecretBranchOrIndex,
    /// ch05 Rule 6b: a trapping arithmetic op or `conv_checked` on secret
    /// (the `wrap_`/`sat_`/`unchecked_` forms are the accepted escape).
    SecretTrappingOp,
    /// ch05 Rule 6b / ch02 Rule 9: secret operand of `check_pre`/`post`/`inv`.
    SecretInContractCheck,
    /// ch05 Rule 6b: a `raise`/`try_br` whose taken-ness depends on secret.
    SecretRaiseCondition,
    /// ch05 Rule 6b: secret argument to a host-effecting `intrinsic`.
    SecretIntrinsicArg,
    /// ch05 Rule 6a: `declassify` outside `@unsafe(invariant: ...)`.
    DeclassifyRequiresUnsafe,
    /// design §3.8: an exit edge whose pending-body SET differs from the
    /// `defer`/`errdefer` rows of the scopes it leaves (ch01 R23a, R23b).
    ExitEdgeWrongPendingMultiset,
    /// design §3.8: the right multiset in the wrong ORDER — not innermost
    /// scope first, or not one reverse `stmt_order` sequence per scope
    /// (ch01 R23a, R23b; `type-checker.md` §13 I8b step 2).
    ExitEdgeWrongPendingOrder,
    /// ch02 R16: a `raise` edge marked `normal`, a `ret` edge marked
    /// `error`, or a `try_br`'s ok/err edges marked the wrong way round.
    ExitEdgeWrongKind,
    /// `type-checker.md` §13 I8b step 2 / design §3.8: an exit edge's
    /// `scopes` list is not the parent chain from the `from` block's own
    /// scope outward (innermost FIRST, each entry the parent of the one
    /// before it, ending at an ancestor of the `to` block's scope). The
    /// pending order is derived from this list, so a list in the wrong
    /// order would make an outer scope's bodies run before an inner's
    /// with the per-scope check still passing.
    ExitEdgeScopesNotAChain,
    /// An exit edge whose `to` is not a successor of `from`'s terminator
    /// (`BlockId::NONE` being the only legal `to` for `ret`/`raise`).
    ExitEdgeNotASuccessor,
    /// Two exit-edge rows for the same `(from, to)` pair: the interpreter's
    /// lookup would be ambiguous.
    ExitEdgeDuplicate,
    /// ch01 R22h: an obligation of a scope being left with no `Discharge`
    /// record on the edge. The interpreter reports this as
    /// `ub: linear-leak`, never a trap (design §3.5, §5.2) — this is the
    /// same condition found statically.
    ExitEdgeMissingDischarge,
    /// Two `Discharge` records for one obligation on one edge
    /// (design §5.2's `ub: double-consume`, found statically).
    ExitEdgeDuplicateDischarge,
    /// A `Discharge` record for a place that is not an obligation of any
    /// scope the edge leaves.
    ExitEdgeUnknownDischarge,
    /// ch01 R23f, R22d, ch02 R7: a `trap` is not an exit — it has no
    /// successor, runs no body and discharges nothing, so no exit edge may
    /// leave a `trap`-terminated block.
    TrapHasExitEdge,
    /// A `DeferRow.body` that names no block, that can reach a `ret`/
    /// `raise`/`try_br` (ch01 R23c forbids all three inside a body), or
    /// from which no `br BODY_END` is reachable (see
    /// [`crate::scope::BODY_END`]).
    DeferBodyMalformed,
    /// A defensive catch-all for structurally malformed pools (e.g. an
    /// out-of-range index) that none of the named checks above cover more
    /// specifically — never expected from this crate's own builder or
    /// parser output, only from a pathologically hand-edited fixture.
    Malformed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: DiagCode,
    pub at: Anchor,
    pub message: String,
}

impl Diagnostic {
    pub fn new(code: DiagCode, at: Anchor, message: impl Into<String>) -> Self {
        Diagnostic {
            code,
            at,
            message: message.into(),
        }
    }
}
