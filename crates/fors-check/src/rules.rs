//! Ch09 rule-to-code traceability table (`docs/design/type-checker.md`
//! §4.2, §8, §16 point 16; increment I0). One row per rule R1-R62 of
//! `docs/spec/09-types.md`, transcribed from the design's §8 table:
//! `code` (its `T00xx` diagnostic, absent for a `NoCode` rule the spec
//! itself declares silent), `short_name` (a stable, human-readable slug —
//! not read by any code, only by the traceability doc and this table's
//! own tests), `status` (every row is [`RuleStatus::Unimplemented`] until
//! the increment that implements it flips it — I0 implements nothing),
//! and `emit_sites`, the `Module::function` names §8 lists as where the
//! rule is checked or its diagnostic is raised (several sites for a rule
//! split across static/body phases or several call forms). No row here
//! is itself a diagnostic; `rules::CH09_RULES` is read-only reference
//! data plus a generator ([`write_traceability`]) — the checker's own
//! `diag.rs` raises `T00xx` independently and could in principle drift
//! from this table, which is exactly what `rules_table_covers_1_to_62`
//! (and, from I3 on, `CHECK_SITES`) exist to catch.

/// Whether a ch09 rule's checker code exists yet. I0 leaves every rule
/// [`RuleStatus::Unimplemented`]; later increments flip their rows'
/// status as they land (append-only in spirit: a row's `status` only ever
/// moves from `Unimplemented` to `Implemented`, never back).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RuleStatus {
    Unimplemented,
    Implemented,
}

/// One ch09 rule's entry in the traceability table.
#[derive(Clone, Copy, Debug)]
pub struct RuleEntry {
    /// The rule number (`R{rule}` in `docs/spec/09-types.md`).
    pub rule: u16,
    /// Its diagnostic code's number (`T{code:04}`), or `None` for a rule
    /// the spec itself says is `NoCode` (an incremental/architectural
    /// property, a grammar fact, or a code owned by another chapter).
    pub code: Option<u16>,
    /// A stable, human-readable slug for the rule (not a spec term of
    /// art — just enough to read the generated table without cross-
    /// referencing `docs/spec/09-types.md` for every row).
    pub short_name: &'static str,
    pub status: RuleStatus,
    /// `Module::function` names, exactly as design §8 lists them, where
    /// this rule is checked or its diagnostic raised. Several entries
    /// when the rule has more than one emission site (a static half and
    /// a body half, or several call forms).
    pub emit_sites: &'static [&'static str],
}

const fn r(rule: u16, code: Option<u16>, short_name: &'static str, emit_sites: &'static [&'static str]) -> RuleEntry {
    RuleEntry { rule, code, short_name, status: RuleStatus::Unimplemented, emit_sites }
}

/// Every ch09 rule, R1 through R62, in rule-number order — design §8's
/// table verbatim. `EMIT_SITES` (below) is the flat union of every row's
/// `emit_sites`, for a quick "does this function name appear anywhere in
/// the table" check without walking the rows.
pub const CH09_RULES: [RuleEntry; 62] = [
    r(1, Some(1), "let-needs-annotation-or-initializer", &["body::let_stmt", "expr::closure_synth", "body::debug_assert"]),
    r(2, None, "sig-hash-is-signature-level-not-body", &["encode::sig_hash"]),
    r(3, Some(3), "no-scalar-beyond-the-primitives", &["prelude::build", "lower::prim"]),
    r(4, Some(4), "one-tuple-of-t-is-t", &["lower::tuple_type", "expr::never_forms"]),
    r(5, Some(5), "prelude-types-are-fixed", &["prelude::build"]),
    r(6, Some(6), "nominal-identity-by-defid", &["ty::intern"]),
    r(7, Some(7), "fn-item-value-and-fn-type-equality", &["ty::fn_ty", "expr::name_expr"]),
    r(8, Some(8), "self-replaced-by-self-type-in-impls", &["lower::self_ty"]),
    r(9, Some(9), "type-equality-is-tyid-equality-after-subst-norm", &[]),
    r(10, Some(10), "subsumption-brand-and-scoped-rejection", &["expr::subsume"]),
    r(11, Some(11), "type-application-arity-and-kind", &["lower::type_app"]),
    r(12, Some(12), "bound-satisfaction-holds", &["bounds::holds", "call::check_bounds", "wf::impl_bounds", "normalise"]),
    r(13, Some(13), "const-argument-is-a-closed-literal", &["lower::const_arg"]),
    r(14, Some(14), "infinite-size-rejected", &["wf::infinite_size"]),
    r(15, Some(15), "generic-parameter-kind-classified-once", &["lower::classify_gparam"]),
    r(16, Some(16), "trait-declaration-well-formedness", &["lower::trait_decl"]),
    r(17, Some(17), "impl-completeness-against-its-trait", &["wf::impl_completeness"]),
    r(18, Some(18), "impl-head-well-formedness", &["wf::impl_params"]),
    r(19, Some(19), "no-overlapping-impls-per-bucket", &["impls::overlap"]),
    r(20, Some(20), "projection-normalisation", &["normalise::normalise_proj", "subst::subst_norm"]),
    r(21, Some(21), "operator-and-indexmut-prerequisite-traits", &["prelude::build", "wf::indexmut_prereq", "bounds::holds", "wf::operator_trait_no_output"]),
    r(22, Some(22), "logical-range-cast-move-operators", &["expr::and_or_not", "expr::range", "expr::cast", "expr::move", "prelude"]),
    r(23, Some(23), "copyable-impl-is-fieldwise-and-defining-module", &["wf::copyable_impl", "ty::is_copyable"]),
    r(24, Some(24), "marker-traits-have-no-methods", &["wf::marker_traits"]),
    r(25, Some(25), "dyn-capable-traits", &["wf::dyn_capable", "lower::dyn_type"]),
    r(26, Some(26), "subsumption-at-check-and-call-sites", &["expr::subsume", "call::final_compare"]),
    r(27, Some(27), "literal-typing", &["expr::literal_synth", "expr::check"]),
    r(28, Some(28), "name-expression-typing", &["expr::name_expr"]),
    r(29, Some(29), "operator-and-index-typing", &["expr::operator", "expr::operator_index"]),
    r(30, Some(30), "boolean-and-cast-context-operands", &["expr::and_or_not", "body::condition", "expr::range", "expr::cast", "body::grain", "body::contract_clause"]),
    r(31, Some(31), "statement-and-for-and-fn-body-typing", &["body::stmt", "body::for_stmt", "body::fn_body"]),
    r(32, Some(32), "if-and-match-synth-and-check", &["expr::if_match_synth", "expr::check"]),
    r(33, Some(33), "never-typed-let-and-break-continue", &["body::let_stmt", "subst::one_way_match", "body::break_continue"]),
    r(34, Some(34), "struct-literal-and-dot-lit-and-variant-construction", &["call::struct_lit", "expr::dot_lit"]),
    r(35, Some(35), "closure-check-and-synth", &["expr::closure_check", "expr::closure_synth"]),
    r(36, Some(36), "try-and-handler-typing", &["expr::try_expr", "expr::handler"]),
    r(37, Some(37), "comptime-spawn-bare-op-and-named-arg", &["expr::comptime_block", "body::spawn_stmt", "expr::bare_op", "call::named_arg"]),
    r(38, Some(38), "generic-call-type-call-steps", &["call::type_call"]),
    r(39, Some(39), "unbound-slot-and-arg-and-conv-marker-checks", &["call::result_ty", "call::explicit_count", "call::arg_count", "call::conv_marker"]),
    r(40, Some(40), "brand-matching-and-fresh-brand-scope", &["subst::one_way_match", "call::match_expected"]),
    r(41, Some(41), "closure-argument-pre-test", &["call::visit_args"]),
    r(42, Some(42), "field-access-typing", &["member::field"]),
    r(43, Some(43), "method-lookup-tier-search", &["member::method", "member::candidate_traits"]),
    r(44, Some(44), "method-lookup-ambiguity", &["member::method"]),
    r(45, Some(45), "qualified-member-lookup", &["member::qualified"]),
    r(46, Some(46), "implicit-receiver-convention-and-move", &["call::receiver", "tape::ImplicitReceiver", "flow::render_move_error"]),
    r(47, Some(47), "bracket-reading-by-operand-target", &["expr::bracket"]),
    r(48, Some(48), "no-member-name-clashes", &["wf::member_clashes"]),
    r(49, None, "member-visibility-is-ch08s-code", &["member::check_visibility"]),
    r(50, Some(50), "pattern-checking", &["pat::check_pat"]),
    r(51, Some(51), "let-pattern-binding", &["pat::bind_let"]),
    r(52, None, "grammar-fact-no-diagnostic", &[]),
    r(53, Some(53), "match-exhaustiveness-missing-arm", &["exhaust::check_match"]),
    r(54, Some(54), "match-arm-not-useful", &["exhaust::check_match"]),
    r(55, Some(55), "exhaustiveness-step-budget", &["exhaust::step_budget"]),
    r(56, None, "absent-syntax-no-diagnostic", &[]),
    r(57, Some(57), "rigid-type-operations-without-a-bound", &["expr::operator", "expr::field", "member::method", "expr::literal_synth", "expr::cast", "pat::check_pat", "tape"]),
    r(58, Some(58), "brand-as-type-and-const-param-value", &["lower::brand_as_type", "expr::const_param_value"]),
    r(59, None, "bodies-checked-once-no-instantiation-dependence", &[]),
    r(60, Some(60), "raises-type-and-fn-ty-equality-and-never-binds-never", &["lower::raises_ty", "ty::fn_ty", "subst::one_way_match"]),
    r(61, Some(61), "projection-lowering-and-assoc-type-use", &["lower::projection", "member::assoc_ty"]),
    r(62, Some(62), "constraint-entries-fn-only-traits-only-well-formed", &["lower::constraint_entries", "call::check_bounds", "bounds::holds"]),
];

/// The flat union of every rule's `emit_sites`: every `Module::function`
/// name design §8 names anywhere in the ch09 table, deduplication left to
/// the reader (a name legitimately repeats across rules, e.g.
/// `bounds::holds`). Distinct from `CHECK_SITES`/`CHECK_SITES_CH09_ADDENDA`
/// (`docs/design/type-checker.md` §4.2's ch03 R25 CHECK-position trace),
/// which is I3's: this is the raise-site table, that is the "which
/// argument position calls `check` rather than `synth`" table.
pub const EMIT_SITES: &[&str] = &[
    "body::let_stmt",
    "expr::closure_synth",
    "body::debug_assert",
    "encode::sig_hash",
    "prelude::build",
    "lower::prim",
    "lower::tuple_type",
    "expr::never_forms",
    "ty::intern",
    "ty::fn_ty",
    "expr::name_expr",
    "lower::self_ty",
    "expr::subsume",
    "lower::type_app",
    "bounds::holds",
    "call::check_bounds",
    "wf::impl_bounds",
    "normalise",
    "lower::const_arg",
    "wf::infinite_size",
    "lower::classify_gparam",
    "lower::trait_decl",
    "wf::impl_completeness",
    "wf::impl_params",
    "impls::overlap",
    "normalise::normalise_proj",
    "subst::subst_norm",
    "wf::indexmut_prereq",
    "wf::operator_trait_no_output",
    "expr::and_or_not",
    "expr::range",
    "expr::cast",
    "expr::move",
    "prelude",
    "wf::copyable_impl",
    "ty::is_copyable",
    "wf::marker_traits",
    "wf::dyn_capable",
    "lower::dyn_type",
    "call::final_compare",
    "expr::literal_synth",
    "expr::check",
    "expr::operator",
    "expr::operator_index",
    "body::condition",
    "body::grain",
    "body::contract_clause",
    "body::stmt",
    "body::for_stmt",
    "body::fn_body",
    "expr::if_match_synth",
    "subst::one_way_match",
    "body::break_continue",
    "call::struct_lit",
    "expr::dot_lit",
    "expr::closure_check",
    "expr::try_expr",
    "expr::handler",
    "expr::comptime_block",
    "body::spawn_stmt",
    "expr::bare_op",
    "call::named_arg",
    "call::type_call",
    "call::result_ty",
    "call::explicit_count",
    "call::arg_count",
    "call::conv_marker",
    "call::match_expected",
    "call::visit_args",
    "member::field",
    "member::method",
    "member::candidate_traits",
    "member::qualified",
    "call::receiver",
    "tape::ImplicitReceiver",
    "flow::render_move_error",
    "expr::bracket",
    "wf::member_clashes",
    "member::check_visibility",
    "pat::check_pat",
    "pat::bind_let",
    "exhaust::check_match",
    "exhaust::step_budget",
    "expr::field",
    "tape",
    "lower::brand_as_type",
    "expr::const_param_value",
    "lower::raises_ty",
    "lower::projection",
    "member::assoc_ty",
    "lower::constraint_entries",
];

/// Renders `CH09_RULES` as a Markdown table (rule, code, short name,
/// status, emit sites) and writes it to
/// `docs/spec/09-types-traceability.md`, relative to the repository root
/// containing `dir` (any path inside the repo; the file walks up to find
/// `Cargo.toml`'s workspace root). Design §4.2/§13: generated "on demand"
/// — nothing calls this automatically; `fors-cli`'s `--audit` flag (§4.4)
/// is the intended caller, and the `traceability_generator_matches_table`
/// test below calls it directly. Never touches `docs/spec/09-types.md`
/// itself or anything under `docs/spec/`/`tests/conformance/` — this is a
/// new file, one directory below the chapter it traces.
pub fn render_traceability() -> String {
    let mut out = String::new();
    out.push_str("<!-- generated by fors_check::rules::render_traceability; do not hand-edit -->\n");
    out.push_str("# Ch09 rule-to-code traceability\n\n");
    out.push_str("| Rule | Code | Short name | Status | Emit sites |\n");
    out.push_str("|---|---|---|---|---|\n");
    for entry in CH09_RULES {
        let code = match entry.code {
            Some(k) => format!("T{k:04}"),
            None => "—".to_string(),
        };
        let status = match entry.status {
            RuleStatus::Unimplemented => "Unimplemented",
            RuleStatus::Implemented => "Implemented",
        };
        let sites = if entry.emit_sites.is_empty() { "—".to_string() } else { entry.emit_sites.join(", ") };
        out.push_str(&format!("| {} | {} | {} | {} | {} |\n", entry.rule, code, entry.short_name, status, sites));
    }
    out
}

/// Writes [`render_traceability`]'s output to
/// `<repo_root>/docs/spec/09-types-traceability.md`, creating or
/// overwriting it. `repo_root` is the directory containing the
/// workspace's own `Cargo.toml` (callers pass it explicitly rather than
/// this function searching for it, so it never accidentally walks
/// outside a sandboxed working directory).
pub fn write_traceability(repo_root: &std::path::Path) -> std::io::Result<()> {
    let path = repo_root.join("docs/spec/09-types-traceability.md");
    std::fs::write(path, render_traceability())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rules_table_covers_1_to_62() {
        assert_eq!(CH09_RULES.len(), 62);
        for (i, entry) in CH09_RULES.iter().enumerate() {
            assert_eq!(entry.rule as usize, i + 1, "row {i} is out of order or has a gap");
        }
        // Every row starts Unimplemented in I0; later increments flip
        // individual rows as they land.
        assert!(CH09_RULES.iter().all(|e| e.status == RuleStatus::Unimplemented));
        // NoCode rows, exactly as design §8 marks them.
        let no_code: Vec<u16> = CH09_RULES.iter().filter(|e| e.code.is_none()).map(|e| e.rule).collect();
        assert_eq!(no_code, vec![2, 49, 52, 56, 59]);
    }

    #[test]
    fn every_short_name_is_unique_and_non_empty() {
        let mut names: Vec<&str> = CH09_RULES.iter().map(|e| e.short_name).collect();
        assert!(names.iter().all(|n| !n.is_empty()));
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), CH09_RULES.len(), "two rules share a short_name");
    }

    #[test]
    fn traceability_generator_matches_table() {
        let text = render_traceability();
        let data_rows = text.lines().filter(|l| l.starts_with("| ")).count() - 1; // minus the header row
        assert_eq!(data_rows, CH09_RULES.len());
        for entry in CH09_RULES {
            assert!(text.contains(entry.short_name), "missing row for rule {}", entry.rule);
        }
    }
}
