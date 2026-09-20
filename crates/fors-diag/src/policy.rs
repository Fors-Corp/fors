//! Where the compiler decides how far a tool may trust a suggested fix.

use crate::{Applicability, FixKind};

// DECIDED by the owner, 2026-09-20 (round 8), over the alternative of
// promoting did-you-mean as well. `MachineApplicable` means an agent applies
// the edit with NO reasoning step, so a kind that is ever wrong silently
// corrupts source; `MaybeIncorrect` charges a read-and-decide round trip at
// every occurrence. The bar is therefore NOT "the arbiter test passes" — all
// five kinds pass it (`crates/fors-cli/tests/fixes.rs`) — but "the compiler
// KNOWS rather than guesses intent" (PLAN R14). The evidence that settled it:
// on `03-numerics/svec-accepted-as-simd-local.fors` did-you-mean proposes
// `SVec` -> `Vec`, which compiles and so passes the arbiter, but `SVec` is the
// reserved scalable-vector type of PLAN R12, not a misspelling. A fix can be
// valid and still be wrong. `applicability_split_is_the_owners`, below, pins
// this; changing a line means changing that test deliberately.
pub fn applicability(kind: FixKind) -> Applicability {
    match kind {
        // The parser already parsed the rest of the file as if the `;` were
        // there; ch08 Rule 1 derives the module name from the file's own
        // location; the resolver named the std module that is missing.
        FixKind::InsertSemicolon => Applicability::MachineApplicable,
        FixKind::FixModuleHeaderPath => Applicability::MachineApplicable,
        FixKind::InsertStdImport => Applicability::MachineApplicable,
        FixKind::ReplaceIdentifier => Applicability::MaybeIncorrect,
        FixKind::CallMethod => Applicability::MaybeIncorrect,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins the owner's round-8 decision. The three machine-applicable kinds
    /// are the ones where the compiler knows the answer outright: the parser
    /// had already parsed the file as if the `;` were there, ch08 Rule 1
    /// derives the module name from the file's own location, and the resolver
    /// named the missing std module. The two others infer what the author
    /// meant, which no arbiter can check.
    #[test]
    fn applicability_split_is_the_owners() {
        for kind in [
            FixKind::InsertSemicolon,
            FixKind::FixModuleHeaderPath,
            FixKind::InsertStdImport,
        ] {
            assert_eq!(
                applicability(kind),
                Applicability::MachineApplicable,
                "{kind:?} is a fix the compiler knows, not one it guesses"
            );
        }
        for kind in [FixKind::ReplaceIdentifier, FixKind::CallMethod] {
            assert_eq!(
                applicability(kind),
                Applicability::MaybeIncorrect,
                "{kind:?} guesses the author's intent, so a tool must read it"
            );
        }
    }
}
