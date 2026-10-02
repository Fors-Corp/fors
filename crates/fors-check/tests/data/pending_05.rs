// Generated beside the harness: the ch05 corpus tests `fors check` does not
// yet decide, each with why. Unlike ch09's `PENDING_09` (whose rows move to
// Present as the TYPE CHECKER's own increments land), every one of these is
// pending for an architectural reason: ch05's rules are enforced by
// `fors-fmir`'s verifier over LOWERED FMIR, and `fors-cli check` runs only
// parse + resolve + `fors-check` -- it never calls `fors-lower` or
// `fors-fmir::verify` (docs/design/fmir-interpreter.md's "why three crates"
// note, section 2: the verifier must not see the checker, so nothing wires
// the other way either). Each row's FMIR-level enforcement already exists
// and is cited; what is pending is ONLY the future integration that would
// let `fors check` surface it, which design doc section 9's increments
// F0-F10 do not yet name.
//
// `pending_05_is_shrinking` asserts the bound never rises, matching
// `pending_09_is_shrinking`'s invariant: a future integration increment
// deletes rows here, never adds them.
const PENDING_05_MAX: usize = 6;
const PENDING_05: &[(&str, &str)] = &[
    (
        "ct-no-branch-or-index-on-secret",
        "fors-fmir::verify's branch_on_secret_is_rejected; ch05_secret_rules.rs's ct_no_branch_or_index_on_secret",
    ),
    (
        "secret-propagates",
        "fors-fmir::verify's secret_add_rejected_unless_result_marked_secret; ch05_secret_rules.rs's secret_propagates",
    ),
    (
        "secret-trapping-op-rejected",
        "fors-fmir::verify's secret_trapping_add_is_rejected_but_wrap_add_is_accepted; ch05_secret_rules.rs's secret_trapping_op_rejected",
    ),
    (
        "secret-raise-condition-rejected",
        "ch05_secret_rules.rs's secret_raise_condition_rejected",
    ),
    (
        "secret-forbidden-in-device",
        "a drafting decision, not yet a numbered rule or an F0 fixture; @device has no checker semantics at all yet",
    ),
    (
        "asm-secret-input-taints-outputs",
        "ch05 Rule 20a(a); unimplemented, no F0 fixture yet (asm secret-taint tracking is unbuilt)",
    ),
];
