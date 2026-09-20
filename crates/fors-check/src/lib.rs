//! `fors-check`: lowering and the two type-checking judgements (design
//! `docs/design/type-checker.md` §4.2). Depends on `fors-lex`,
//! `fors-syntax`, `fors-index`, `fors-resolve` and `fors-fir`.
//!
//! Increment I0 (plumbing only, §13) adds only [`rules`] (the ch09
//! rule-to-code traceability table, every row `Unimplemented`) and
//! [`check_build`], which runs and emits nothing: `DefTable`, `lower.rs`,
//! `wf.rs`, `body.rs`, `expr.rs`, `call.rs`, `member.rs`, `pat.rs`,
//! `exhaust.rs`, `tape.rs`, `flow.rs`, `diag.rs` and `facts.rs` are I2
//! onward's (§13's ordered increment plan).

pub mod rules;

/// The result of type-checking a whole build. Empty in I0: no phase runs
/// yet, so there is nothing to report. `docs/design/type-checker.md`
/// §4.2 gives `diag.rs`/`facts.rs` as this type's eventual home for a
/// checked build's diagnostics and typed side tables (`BodyFacts`); I0
/// carries only the one field every later increment already needs
/// somewhere to put its output.
#[derive(Default)]
pub struct CheckOutput {
    pub diagnostics: Vec<fors_index::diag::Code>,
}

// MARC: design §4.2/§4.4 gives `check_build`'s signature as
// `check_build(&ResolveOutput, ...) -> CheckOutput` without spelling out
// the `...`; a build-wide FIR pass needs the same `Interner` resolution
// already threaded through, so it is the one parameter added here ahead
// of I1 rather than guessed at that point. Nothing in I0 reads it.
/// Type-checks a whole resolved build (design §13, increment I0: "`fors
/// check` calls `check_build`, which emits nothing yet"). `resolved` is
/// [`fors_resolve::resolve`]'s output; `interner` is the same build-wide
/// interner threaded through resolution, unmodified here.
pub fn check_build(_resolved: &fors_resolve::ResolveOutput, _interner: &fors_index::Interner) -> CheckOutput {
    CheckOutput::default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_index::Interner;
    use fors_resolve::FileInput;
    use fors_syntax::parse_file;

    #[test]
    fn check_build_on_an_empty_package_emits_nothing() {
        let mut interner = Interner::new();
        let src = b"module m;\n";
        let parsed = parse_file(src);
        let name = vec![interner.intern(b"m")];
        let inputs = [FileInput { tree: &parsed.tree, tokens: &parsed.tokens, source: src, name }];
        let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
        let out = check_build(&resolved, &interner);
        assert!(out.diagnostics.is_empty());
    }
}
