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

const fn r(
    rule: u16,
    code: Option<u16>,
    short_name: &'static str,
    emit_sites: &'static [&'static str],
) -> RuleEntry {
    RuleEntry {
        rule,
        code,
        short_name,
        status: RuleStatus::Unimplemented,
        emit_sites,
    }
}

/// A rule whose checker code exists. Increment I2 flips the signature and
/// whole-head rules; the body rules stay [`RuleStatus::Unimplemented`] until
/// the increment that types a body reaches them.
const fn imp(
    rule: u16,
    code: Option<u16>,
    short_name: &'static str,
    emit_sites: &'static [&'static str],
) -> RuleEntry {
    RuleEntry {
        rule,
        code,
        short_name,
        status: RuleStatus::Implemented,
        emit_sites,
    }
}

/// Every ch09 rule, R1 through R62, in rule-number order — design §8's
/// table verbatim. `EMIT_SITES` (below) is the flat union of every row's
/// `emit_sites`, for a quick "does this function name appear anywhere in
/// the table" check without walking the rows.
pub const CH09_RULES: [RuleEntry; 62] = [
    imp(
        1,
        Some(1),
        "let-needs-annotation-or-initializer",
        &[
            "body::let_stmt",
            "expr::closure_synth",
            "body::debug_assert",
        ],
    ),
    r(
        2,
        None,
        "sig-hash-is-signature-level-not-body",
        &["encode::sig_hash"],
    ),
    imp(
        3,
        Some(3),
        "no-scalar-beyond-the-primitives",
        &["prelude::build", "lower::prim"],
    ),
    imp(
        4,
        Some(4),
        "one-tuple-of-t-is-t",
        &["lower::tuple_type", "expr::never_forms"],
    ),
    imp(5, Some(5), "prelude-types-are-fixed", &["prelude::build"]),
    imp(6, Some(6), "nominal-identity-by-defid", &["ty::intern"]),
    imp(
        7,
        Some(7),
        "fn-item-value-and-fn-type-equality",
        &["ty::fn_ty", "expr::name_expr"],
    ),
    imp(
        8,
        Some(8),
        "self-replaced-by-self-type-in-impls",
        &["lower::self_ty"],
    ),
    imp(
        9,
        Some(9),
        "type-equality-is-tyid-equality-after-subst-norm",
        &[],
    ),
    imp(
        10,
        Some(10),
        "subsumption-brand-and-scoped-rejection",
        &["expr::subsume"],
    ),
    imp(
        11,
        Some(11),
        "type-application-arity-and-kind",
        &["lower::type_app"],
    ),
    imp(
        12,
        Some(12),
        "bound-satisfaction-holds",
        &[
            "bounds::holds",
            "call::check_bounds",
            "wf::impl_bounds",
            "normalise",
        ],
    ),
    imp(
        13,
        Some(13),
        "const-argument-is-a-closed-literal",
        &["lower::const_arg"],
    ),
    imp(
        14,
        Some(14),
        "infinite-size-rejected",
        &["wf::infinite_size"],
    ),
    imp(
        15,
        Some(15),
        "generic-parameter-kind-classified-once",
        &["lower::classify_gparam"],
    ),
    imp(
        16,
        Some(16),
        "trait-declaration-well-formedness",
        &["lower::trait_decl"],
    ),
    imp(
        17,
        Some(17),
        "impl-completeness-against-its-trait",
        &["wf::impl_completeness"],
    ),
    imp(
        18,
        Some(18),
        "impl-head-well-formedness",
        &["wf::impl_params"],
    ),
    imp(
        19,
        Some(19),
        "no-overlapping-impls-per-bucket",
        &["impls::overlap"],
    ),
    imp(
        20,
        Some(20),
        "projection-normalisation",
        &["normalise::normalise_proj", "subst::subst_norm"],
    ),
    imp(
        21,
        Some(21),
        "operator-and-indexmut-prerequisite-traits",
        &[
            "prelude::build",
            "wf::indexmut_prereq",
            "bounds::holds",
            "wf::operator_trait_no_output",
        ],
    ),
    imp(
        22,
        Some(22),
        "logical-range-cast-move-operators",
        &[
            "expr::and_or_not",
            "expr::range",
            "expr::cast",
            "expr::move",
            "prelude",
        ],
    ),
    imp(
        23,
        Some(23),
        "copyable-impl-is-fieldwise-and-defining-module",
        &["wf::copyable_impl", "ty::is_copyable"],
    ),
    imp(
        24,
        Some(24),
        "marker-traits-have-no-methods",
        &["wf::marker_traits"],
    ),
    imp(
        25,
        Some(25),
        "dyn-capable-traits",
        &["wf::dyn_capable", "lower::dyn_type"],
    ),
    imp(
        26,
        Some(26),
        "subsumption-at-check-and-call-sites",
        &["expr::subsume", "call::final_compare"],
    ),
    imp(
        27,
        Some(27),
        "literal-typing",
        &["expr::literal_synth", "expr::check"],
    ),
    imp(28, Some(28), "name-expression-typing", &["expr::name_expr"]),
    imp(
        29,
        Some(29),
        "operator-and-index-typing",
        &["expr::operator", "expr::operator_index"],
    ),
    imp(
        30,
        Some(30),
        "boolean-and-cast-context-operands",
        &[
            "expr::and_or_not",
            "body::condition",
            "expr::range",
            "expr::cast",
            "body::grain",
            "body::contract_clause",
        ],
    ),
    imp(
        31,
        Some(31),
        "statement-and-for-and-fn-body-typing",
        &["body::stmt", "body::for_stmt", "body::fn_body"],
    ),
    imp(
        32,
        Some(32),
        "if-and-match-synth-and-check",
        &["expr::if_match_synth", "expr::check"],
    ),
    imp(
        33,
        Some(33),
        "never-typed-let-and-break-continue",
        &[
            "body::let_stmt",
            "subst::one_way_match",
            "body::break_continue",
        ],
    ),
    imp(
        34,
        Some(34),
        "struct-literal-and-dot-lit-and-variant-construction",
        &["call::struct_lit", "expr::dot_lit"],
    ),
    imp(
        35,
        Some(35),
        "closure-check-and-synth",
        &["expr::closure_check", "expr::closure_synth"],
    ),
    imp(
        36,
        Some(36),
        "try-and-handler-typing",
        &["expr::try_expr", "expr::handler"],
    ),
    imp(
        37,
        Some(37),
        "comptime-spawn-bare-op-and-named-arg",
        &[
            "expr::comptime_block",
            "body::spawn_stmt",
            "expr::bare_op",
            "call::named_arg",
        ],
    ),
    imp(
        38,
        Some(38),
        "generic-call-type-call-steps",
        &["call::type_call"],
    ),
    imp(
        39,
        Some(39),
        "unbound-slot-and-arg-and-conv-marker-checks",
        &[
            "call::result_ty",
            "call::explicit_count",
            "call::arg_count",
            "call::conv_marker",
        ],
    ),
    imp(
        40,
        Some(40),
        "brand-matching-and-fresh-brand-scope",
        &["subst::one_way_match", "call::match_expected"],
    ),
    imp(
        41,
        Some(41),
        "closure-argument-pre-test",
        &["call::visit_args"],
    ),
    imp(42, Some(42), "field-access-typing", &["member::field"]),
    imp(
        43,
        Some(43),
        "method-lookup-tier-search",
        &["member::method", "member::candidate_traits"],
    ),
    imp(44, Some(44), "method-lookup-ambiguity", &["member::method"]),
    imp(
        45,
        Some(45),
        "qualified-member-lookup",
        &["member::qualified"],
    ),
    imp(
        46,
        Some(46),
        "implicit-receiver-convention-and-move",
        &[
            "call::receiver",
            "tape::ImplicitReceiver",
            "flow::render_move_error",
        ],
    ),
    imp(
        47,
        Some(47),
        "bracket-reading-by-operand-target",
        &["expr::bracket"],
    ),
    imp(
        48,
        Some(48),
        "no-member-name-clashes",
        &["wf::member_clashes"],
    ),
    imp(
        49,
        None,
        "member-visibility-is-ch08s-code",
        &["member::check_visibility"],
    ),
    imp(50, Some(50), "pattern-checking", &["pat::check_pat"]),
    imp(51, Some(51), "let-pattern-binding", &["pat::bind_let"]),
    r(52, None, "grammar-fact-no-diagnostic", &[]),
    imp(
        53,
        Some(53),
        "match-exhaustiveness-missing-arm",
        &["exhaust::check_match"],
    ),
    imp(
        54,
        Some(54),
        "match-arm-not-useful",
        &["exhaust::check_match"],
    ),
    imp(
        55,
        Some(55),
        "exhaustiveness-step-budget",
        &["exhaust::step_budget"],
    ),
    r(56, None, "absent-syntax-no-diagnostic", &[]),
    imp(
        57,
        Some(57),
        "rigid-type-operations-without-a-bound",
        &[
            "expr::operator",
            "expr::field",
            "member::method",
            "expr::literal_synth",
            "expr::cast",
            "pat::check_pat",
            "tape",
            "flow::drop_rigid",
        ],
    ),
    r(
        58,
        Some(58),
        "brand-as-type-and-const-param-value",
        &["lower::brand_as_type", "expr::const_param_value"],
    ),
    imp(
        59,
        None,
        "bodies-checked-once-no-instantiation-dependence",
        &[],
    ),
    imp(
        60,
        Some(60),
        "raises-type-and-fn-ty-equality-and-never-binds-never",
        &["lower::raises_ty", "ty::fn_ty", "subst::one_way_match"],
    ),
    imp(
        61,
        Some(61),
        "projection-lowering-and-assoc-type-use",
        &["lower::projection", "member::assoc_ty"],
    ),
    imp(
        62,
        Some(62),
        "constraint-entries-fn-only-traits-only-well-formed",
        &[
            "lower::constraint_entries",
            "call::check_bounds",
            "bounds::holds",
        ],
    ),
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

// ------------------------------------------------ I10: chapters 2 and 3

/// The ch02 (failure) rules the checker emits a code for (increment I10,
/// half A; design §8's inherited-obligation rows, §14 Q1's `F00nn`, the
/// rule number is the code). Same shape as [`CH09_RULES`]; `code` is the
/// number after `F`. A rule of the chapter that is not the checker's —
/// R4's ABI classifier, R6-R8's trap lowering, R11-R12's check deletion and
/// release tagging, R14's C++ boundary, R15-R17's trap kinds, error exits
/// and `main`'s runtime path — has no row, because no checker site emits
/// for it.
pub const CH02_RULES: [RuleEntry; 7] = [
    imp(
        1,
        Some(1),
        "raises-declared-and-every-raising-call-handled",
        &["call::call_expr_inner", "body::raise_stmt", "expr::subsume"],
    ),
    imp(
        2,
        Some(2),
        "postfix-try-only-on-a-raising-call",
        &["call::call_expr_inner", "expr::synth_inner"],
    ),
    imp(
        3,
        Some(3),
        "try-performs-one-errorfrom-lookup",
        &["failure::try_edge", "failure::error_from_impl"],
    ),
    // The handler block's own value mismatch keeps ch09 R36/R26's T0026
    // (`09-types/handler-block-type-rejected` asserts it); F0005 is the
    // handler written after a call that does not raise.
    imp(
        5,
        Some(5),
        "handler-only-after-a-raising-call",
        &["call::handler"],
    ),
    imp(
        9,
        Some(9),
        "contract-has-no-secret-subexpression",
        &["body::check_contracts", "failure::contract_secret"],
    ),
    imp(
        10,
        Some(10),
        "proved-contract-must-be-discharged",
        &["lower::contract_policy"],
    ),
    imp(
        13,
        Some(13),
        "extern-c-declares-no-raises",
        &["lower::lower_fn", "lower::extern_abi_is_c"],
    ),
];

/// The ch03 (numerics) rules the checker emits a code for (I10, half A;
/// `D00nn`). Rules 2, 3, 7, 10-14 (trapping, IEEE strictness, determinism,
/// `reduce`'s shape) and 16-17 (monomorphisation) are lowering's and the
/// interpreter's; R23's `.splat` and R24a's repeat form are typed but R23
/// has no failure of its own, and R24a reports under R24's code.
pub const CH03_RULES: [RuleEntry; 15] = [
    imp(
        1,
        Some(1),
        "integers-are-fixed-width-no-128-bit",
        &["lower::rejected_width"],
    ),
    imp(
        4,
        Some(4),
        "unchecked-op-only-in-an-unsafe-declaration",
        &["numerics::unchecked_site"],
    ),
    imp(
        5,
        Some(5),
        "no-implicit-numeric-conversion",
        &["expr::subsume", "numerics::numeric_mismatch"],
    ),
    imp(
        6,
        Some(6),
        "lossy-conversion-to-a-numeric-primitive",
        &["numerics::numeric_call_done"],
    ),
    imp(
        8,
        Some(8),
        "fastmath-flags-are-a-closed-set",
        &["numerics::fastmath_flags"],
    ),
    imp(
        9,
        Some(9),
        "comptime-value-does-not-escape-implicitly",
        &[
            "expr::subsume",
            "numerics::numeric_mismatch",
            "numerics::comptime_binding",
        ],
    ),
    imp(11, Some(11), "reduce-call-form", &["numerics::reduce_call"]),
    imp(
        15,
        Some(15),
        "no-implicit-parallel-accumulator",
        &["numerics::accumulator_in_parallel"],
    ),
    imp(
        18,
        Some(18),
        "specialize-enforced-in-simd",
        &["numerics::specialize_in_simd"],
    ),
    imp(
        19,
        Some(19),
        "vector-and-mask-lane-count-is-a-power-of-two",
        &["lower::bad_lane_count"],
    ),
    imp(20, Some(20), "svec-is-reserved", &["lower::svec_misuse"]),
    imp(
        21,
        Some(21),
        "array-literal-count-equals-n",
        &["expr::check_array"],
    ),
    imp(
        22,
        Some(22),
        "empty-array-literal-in-synth-mode",
        &["expr::synth_array"],
    ),
    imp(
        24,
        Some(24),
        "slice-only-by-range-index-and-repeat-form",
        &["expr::check_array", "expr::repeat_element"],
    ),
    imp(
        25,
        Some(25),
        "synth-literal-later-element-checked-against-first",
        &["expr::check_array"],
    ),
];

// ------------------------------------------------ I10: chapters 4 and 1

/// The ch04 (authority) rules the CHECKER emits a code for (I10, half B;
/// `A00nn`, the rule number is the code; a lettered clause reports under
/// its rule's number and names the clause in the message). R1's `needs`
/// vocabulary and R8's `main` shape are decided from names alone and stay
/// `fors_resolve::authority`'s (A0001, A0008), so they have no row here.
/// R2b and R3 (the manifest policy) and R17-R19 (the lockfile) need a
/// manifest this build does not have; R14's step budget, R11 and R15 are
/// comptime EVALUATION (FMIR F9); R4, R24-R26 are codegen's and ch05's.
pub const CH04_RULES: [RuleEntry; 8] = [
    imp(
        2,
        Some(2),
        "r2a-sealed-operation-not-generic-not-comptime-and-declared",
        &["authority::authority_call", "authority::asm_expr"],
    ),
    imp(
        7,
        Some(7),
        "root-capability-type-has-no-constructor",
        &["authority::authority_struct_lit"],
    ),
    imp(
        10,
        Some(10),
        "unsafe-is-a-declaration-attribute-with-an-invariant",
        &[
            "authority::unsafe_attributes",
            "authority::unsafe_block_form",
            "authority::authority_struct_lit",
        ],
    ),
    imp(
        12,
        Some(12),
        "comptime-reaches-no-run-time-binding",
        &["authority::comptime_reach"],
    ),
    imp(
        13,
        Some(13),
        "comptime-file-read-listed-in-inputs",
        &["authority::authority_call"],
    ),
    imp(
        22,
        Some(22),
        "asm-only-in-unsafe-declaration-of-an-asm-holder",
        &["authority::asm_expr"],
    ),
    imp(
        23,
        Some(23),
        "syscall-class-asm-needs-syscall",
        &["authority::asm_expr"],
    ),
    imp(
        27,
        Some(27),
        "asm-expr-is-check-only-typed",
        &["authority::asm_expr", "body::stmt_inner"],
    ),
];

/// The ch01 rules increment I10 gave a checker code of their own
/// (`O00nn`): an arena's or allocator's constructor and whole move (R15a,
/// under R15's code, which `lower::type_app` and `member::gparam_value`
/// already use for R15d), the arena subscript (R16), `deinit`'s brand (R18)
/// and `Shared` (R21, and R21a under R21's code). A brand-only mismatch at a
/// call or a binding stays ch09's T0026 (the ch09 corpus asserts it), with a
/// message citing R15/R15d.
pub const CH01_RULES: [RuleEntry; 4] = [
    imp(
        15,
        Some(15),
        "arena-and-allocator-have-no-constructor-and-never-move",
        &["authority::authority_struct_lit", "authority::arena_move"],
    ),
    imp(
        16,
        Some(16),
        "ref-used-only-against-an-arena-of-its-brand",
        &["authority::arena_index"],
    ),
    imp(
        18,
        Some(18),
        "deinit-through-an-allocator-of-the-owns-brand",
        &["authority::authority_call"],
    ),
    imp(
        21,
        Some(21),
        "atomic-only-in-shared-and-shared-is-fieldwise",
        &["authority::atomic_fields", "authority::shared_impls"],
    ),
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
    out.push_str(
        "<!-- generated by fors_check::rules::render_traceability; do not hand-edit -->\n",
    );
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
        let sites = if entry.emit_sites.is_empty() {
            "—".to_string()
        } else {
            entry.emit_sites.join(", ")
        };
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            entry.rule, code, entry.short_name, status, sites
        ));
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
            assert_eq!(
                entry.rule as usize,
                i + 1,
                "row {i} is out of order or has a gap"
            );
        }
        // A row's status only ever moves from `Unimplemented` to
        // `Implemented`, so this is the exact set an increment edits: I2
        // lands the signature and whole-head rules.
        let implemented: Vec<u16> = CH09_RULES
            .iter()
            .filter(|e| e.status == RuleStatus::Implemented)
            .map(|e| e.rule)
            .collect();
        // I2 flipped the signature and whole-head rows; I3 flips the body
        // rows it decides. I4 adds R12 (`wf::holds` plus the use site at a
        // call), R43/R44 (the two-tier lookup and its ambiguity, nominal,
        // rigid and PRIMITIVE heads) and R45 (the qualified form). R38-R41
        // stay unimplemented (R38's inference is I5's — I4 determines a
        // callee's parameters only in the bare-parameter argument
        // positions R12's bound check needs), and so does R46: its typing
        // side is in, but the rule's normative message is I8's, over a
        // tape this increment only writes.
        //
        // I5 adds R38-R41 (`call::type_call`'s steps (a)-(f), the
        // expected-type pre-binding, R40's brand identity and fresh
        // `with` brands, R41's closure pre-test), R59 (bodies checked
        // once — `no_error_depends_on_instantiation` in `probes.rs` is
        // the statement of it) and R60 (`raises` as a type through a
        // call, and `one_way_match`'s "`never` binds nothing"). R39's
        // row keeps `call::conv_marker` among its sites: that half is
        // ch01 R2's, reported with ch01's own `O0002` at I8 (§8's
        // inherited-obligations table), while the three T0039 sites —
        // the unbound slot, the explicit-argument count and the argument
        // count — are this increment's and are in. R57 and R58 stay
        // unimplemented: their remaining sites are `pat::check_pat`
        // (I7), the tape's rigid `Move` (I8) and `lower::brand_as_type`
        // (`brand-param-as-value-type-rejected`, still pending).
        //
        // I6 adds R20, the only row it flips: `normalise.rs`'s
        // `normalise_proj` and the `ProjSolver` every `subst_norm` in the
        // checker now carries. The rest of I6's GATE is use sides of rows
        // already `Implemented` — R12 for projection subjects and R62's
        // constraint entries at a call (`call::check_bounds` /
        // `call::check_constraint_entries`), R43 on a neutral projection
        // (`methods::lookup_on_rigid`), R38's steps with the container's
        // slots (`call::call_owners`) — so they have no row to flip.
        // R57 stays unimplemented: its remaining sites are `pat::check_pat`
        // (I7) and the tape's rigid `Move` (I8), as I5 recorded.
        //
        // I7 adds R50 (`pat::check_pat`), R51 (`pat::bind_let`), R53/R54
        // (`exhaust::check_match`'s two diagnostics over the same
        // usefulness computation) and R55 (`exhaust::step_budget`). R52
        // and R56 stay unimplemented: both are grammar facts with no
        // diagnostic of their own (design §8: "NoCode"), proven by the
        // absence of the production in ch07's grammar rather than by any
        // code this crate runs, so there is no row to flip for them. R57
        // still has `pat::check_pat` left unimplemented in its own row:
        // that site is the "rigid types without a bound" half (matching a
        // generic parameter's pattern needs a bound this increment does
        // not check), not the ordinary case I7 built.
        //
        // I8 (the flow pass) adds R46, the ONE row it flips: the typing
        // side (`call::receiver`) and the tape's cause
        // (`tape::ImplicitReceiver`) were already in, and
        // `flow::render_move_error` is the rule's normative message, the
        // last of its three sites. The rest of I8's GATE is ch01's, not
        // ch09's, and has no row in this table: R2's markers at a call
        // (`call::conv_marker`, O0002 — R39's row already lists that
        // site, and R39 is `Implemented` for its own three T0039 sites),
        // R3 and R4a(a)-(e) (`flow.rs`, O0003 and O0004) and R8's
        // two-valued merge at every join, loop head and loop exit
        // (`flow::merge`, `flow::loop_head`, O0008 — the corpus's
        // `merge-liveness-disagreement-rejected` is 01.R8's own test).
        //
        // I8b (round-6 flow, 2026-10-02) flips R57, the ONE row it flips.
        // Its last two sites are now in: `pat::check_pat` rejects a `_`
        // or a literal pattern facing a linear component (ch01 R22d(ii)),
        // and the new `flow::drop_rigid` site — `flow::render_linear_leak`
        // and the scope-exit check behind it — is R57's round-6 drop
        // clause, "letting a value of rigid type go out of scope,
        // `discard`ing it, matching it with `_`, or evaluating it as an
        // expression statement MUST be rejected unless the type is
        // `Droppable`" (ch01 R22c). `rigid-{drop,discard,expression-
        // statement}-without-droppable-rejected`,
        // `neutral-projection-drop-without-bound-rejected` and
        // `linear-bound-adds-no-operation-rejected` came off `PENDING_09`
        // with it. The rest of I8b's GATE is ch01's and has no row here:
        // R22-R22i (O0022, `flow::scope_exit` / `flow::render_linear_leak`
        // / `wf::is_linear` over `fors_fir::ty::lin`), R23-R23f (O0023,
        // `flow::static_linear_checks` and `flow::scope_exit`) and
        // R19c/R19d (O0019, `flow::closure_sources`). The ch09 rows those
        // clauses amend — R10(c) at `expr::to_dyn`, R11's linear element
        // at `wf::linear_elements`, R23 at `wf::copyable_impl`, R24 at
        // `wf::marker_traits`, R50 at `pat::check_pat` — were already
        // `Implemented` and keep their sites.
        //
        // R58 stays unimplemented, although I10b landed the body half of
        // both its clauses at `member::path_head`'s `gparam_value` (§8's
        // row 58 names the site `expr::const_param_value`; the judgement
        // lives with the rest of the path-head reading instead): a CONST
        // parameter is now a constant of its declared type in a body —
        // which is what made `a[0 ..< N]` type rather than absorb — and a
        // BRAND parameter in VALUE position now reports ch01 R15d's own
        // code beside `lower::brand_as_type`'s type position. What is left
        // is the clause's reach: `LocalKind::ConstParam` is still unread,
        // the value a const parameter denotes is not folded, and no ch09
        // corpus test asks for either, so the row does not yet flip.
        assert_eq!(
            implemented,
            vec![
                1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
                25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
                46, 47, 48, 49, 50, 51, 53, 54, 55, 57, 59, 60, 61, 62
            ]
        );
        // NoCode rows, exactly as design §8 marks them.
        let no_code: Vec<u16> = CH09_RULES
            .iter()
            .filter(|e| e.code.is_none())
            .map(|e| e.rule)
            .collect();
        assert_eq!(no_code, vec![2, 49, 52, 56, 59]);
    }

    #[test]
    fn every_short_name_is_unique_and_non_empty() {
        let mut names: Vec<&str> = CH09_RULES.iter().map(|e| e.short_name).collect();
        assert!(names.iter().all(|n| !n.is_empty()));
        names.sort_unstable();
        names.dedup();
        assert_eq!(
            names.len(),
            CH09_RULES.len(),
            "two rules share a short_name"
        );
    }

    /// I10: the ch02/ch03/ch04/ch01 tables follow design §14 Q1 — the code
    /// IS the rule number — in rule order, every row implemented, names
    /// unique.
    #[test]
    fn ch02_and_ch03_tables_are_rule_numbered() {
        for table in [
            &CH02_RULES[..],
            &CH03_RULES[..],
            &CH04_RULES[..],
            &CH01_RULES[..],
        ] {
            let mut last = 0u16;
            let mut names: Vec<&str> = Vec::new();
            for e in table {
                assert_eq!(e.code, Some(e.rule), "rule {} is not its own code", e.rule);
                assert!(e.rule > last, "rule {} is out of order", e.rule);
                assert_eq!(e.status, RuleStatus::Implemented);
                assert!(!e.emit_sites.is_empty() && !e.short_name.is_empty());
                last = e.rule;
                names.push(e.short_name);
            }
            names.sort_unstable();
            let n = names.len();
            names.dedup();
            assert_eq!(names.len(), n, "two rules share a short_name");
        }
    }

    #[test]
    fn traceability_generator_matches_table() {
        let text = render_traceability();
        let data_rows = text.lines().filter(|l| l.starts_with("| ")).count() - 1; // minus the header row
        assert_eq!(data_rows, CH09_RULES.len());
        for entry in CH09_RULES {
            assert!(
                text.contains(entry.short_name),
                "missing row for rule {}",
                entry.rule
            );
        }
    }
}
