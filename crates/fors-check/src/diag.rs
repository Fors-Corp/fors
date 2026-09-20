//! Diagnostic construction and the recovery policy (design §10).
//!
//! One `Diagnostic` per root cause: a file, a byte range, a [`Code`], the
//! rule number of the EMISSION SITE (which is not always the code's own
//! number — R21's "an operator trait has no `Output`" is emitted at R21's
//! site with R17's code, and R17's associated-type bound check is emitted at
//! R17's site with R21's code when the violated bound is one R21 declares),
//! and a message.

use fors_index::diag::Code;
use fors_index::ids::FileId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
    pub code: Code,
    /// The ch09 rule whose implementation emitted this (design §10: "the
    /// emission site's rule must be the cited rule").
    pub site: u16,
    pub message: String,
}

/// Design §10's bounded output. I2's budget is one diagnostic per
/// DECLARATION: a signature that is already wrong poisons the rest of its own
/// head (a struct whose field type did not lower has no meaningful field type
/// to check for infinite size), and the corpus's "exactly one diagnostic per
/// `check-error` test" is the same statement from the other side.
pub const PER_DECL_BUDGET: usize = 1;

#[derive(Default)]
pub struct Sink {
    out: Vec<Diagnostic>,
    /// How many diagnostics the declaration currently being checked has
    /// already produced.
    charged: usize,
}

impl Sink {
    pub fn new() -> Sink {
        Sink::default()
    }

    /// Starts a new declaration's budget.
    pub fn open(&mut self) {
        self.charged = 0;
    }

    /// Whether the current declaration has spent its budget — callers use it
    /// to skip work, never to decide correctness.
    pub fn poisoned(&self) -> bool {
        self.charged >= PER_DECL_BUDGET
    }

    pub fn emit(
        &mut self,
        file: FileId,
        range: (u32, u32),
        code: Code,
        site: u16,
        message: String,
    ) {
        if self.poisoned() {
            return;
        }
        self.charged += 1;
        self.out.push(Diagnostic {
            file,
            start: range.0,
            end: range.1,
            code,
            site,
            message,
        });
    }

    pub fn len(&self) -> usize {
        self.out.len()
    }

    pub fn is_empty(&self) -> bool {
        self.out.is_empty()
    }

    /// The diagnostics, sorted by `(file, offset, code)` as design §7.1 phase
    /// 7 requires.
    pub fn finish(mut self) -> Vec<Diagnostic> {
        self.out
            .sort_by_key(|d| (d.file.0, d.start, d.code.as_string()));
        self.out
    }
}

/// `T00nn`.
pub fn t(rule: u16) -> Code {
    Code::T(rule)
}
