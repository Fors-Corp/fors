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
