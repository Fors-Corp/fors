//! Where the compiler decides how far a tool may trust a suggested fix.

use crate::{Applicability, FixKind};

// MARC: this match is the whole learning-mode contribution point — rewrite
// it in a minute. `MachineApplicable` means an agent applies the edit with
// NO reasoning step, so a kind that is ever wrong silently corrupts source;
// `MaybeIncorrect` charges the agent a read-and-decide round trip at every
// occurrence, which is the most expensive thing we can charge it. The line
// is not "the arbiter passes" (today all five kinds pass its strict bar,
// `crates/fors-cli/tests/fixes.rs`) but "the compiler KNOWS rather than
// guesses intent" (policy R14): a name one edit away may be the wrong name
// and a method may take arguments, and both turn a loud error into a quiet
// wrong program. To promote one, move its line.
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
