// Generated beside the harness: the ch09 corpus tests this increment has
// not reached, each with the increment (design §13) that owns it.
// `pending_09_is_shrinking` asserts the bound never rises; every
// increment deletes rows, never adds them.
//
// I4b deleted three rows (`bound-unsatisfied-rejected`,
// `adaptor-provided-method-shadowed-by-inherent-rejected` and
// `index-literal-with-two-impls-rejected`, which carried a stale "I3" tag:
// design §13's I4 GATE names it under R29, and `member.rs` already said
// "Two impls (R29's "several") ... are I4's") and RETAGGED
// the five it found were not I4's. The reasons, once, here:
//
// - `adaptor-map-closure-returns-linear-rejected` I4 -> I8b. The bound
//   that fails is `U: Droppable` with `U := Res` and `impl Linear for
//   Res` (spec ch09 line "R12 `adaptor-map-closure-returns-linear-
//   rejected` T0012 (`U: Droppable`)"). `Droppable`/`lin` are design §13's
//   I8b row ("ch01 R22c | `Droppable` has no impls ... | I8b"), and the
//   subject comes from a closure BODY, which is I5's.
// - `adaptor-name-clash-two-traits-rejected` I4 -> I8b. R44 needs TWO
//   candidate traits declaring `take`; the second is `Iterator`'s PROVIDED
//   `take`, which exists only in `std/mem/seq.fors`. The ch09 harness
//   checks each file alone, where `Iterator` is the prelude row and
//   declares `next` and nothing else, and `methods.rs`'s silence contract
//   forbids guessing at a declaration this build does not have. §13's I4
//   GATE names "R44 (1)" — `two-traits-same-method-rejected`, which is on
//   — and the only §13 sentence that assigns THIS file is I8's: "Round 6
//   added 58 more files to `09-types` (244 now) ...; they stay
//   `Pending(I8b)` here".
// - `constraint-entry-unsatisfied-at-call-rejected` I4 -> I6. Its rule is
//   R62 and its subject is the constraint entry `I.Item: Add` normalised
//   at the call; §13 I6 owns "R62 use side" and its GATE lists "R61, R62".
// - `neutral-projection-does-not-match-concrete-impl-rejected` I4 -> I6.
//   §13's I4 paragraph names it: "every projection-dependent test of these
//   groups, such as R20's `neutral-projection-does-not-match-concrete-
//   impl-rejected`, is I6's".
// - `projection-head-without-impl-rejected` I4 -> I6. §13 I6 owns "R20 ...
//   R12 for projection subjects" and its GATE lists "R20 (8)"; the file's
//   "one root cause, reported once" couples the R12 failure to suppressing
//   the normalisation of `Plain.Item`, which is that machinery.
const PENDING_09_MAX: usize = 51;
const PENDING_09: &[(&str, &str)] = &[
    ("adaptor-annotated-binding-mismatch-rejected", "I3"),
    ("adaptor-generic-fn-item-uninstantiated-rejected", "I5"),
    ("adaptor-map-closure-returns-linear-rejected", "I8b"),
    ("adaptor-name-clash-two-traits-rejected", "I8b"),
    ("adaptor-on-field-receiver-rejected", "I8"),
    ("adaptor-on-inout-receiver-rejected", "I8"),
    ("arm-after-let-pattern-unreachable-rejected", "I7"),
    ("binding-never-revised-rejected", "I3"),
    ("brand-identity-mismatch-rejected", "I3"),
    ("brand-param-as-value-type-rejected", "I8"),
    ("callable-bound-cannot-bind-result-rejected", "I5"),
    ("cannot-infer-rejected", "I5"),
    ("closure-before-its-iterator-rejected", "I3"),
    ("closure-before-its-type-source-rejected", "I3"),
    ("const-pattern-equal-to-literal-unreachable-rejected", "I7"),
    ("constraint-entry-unsatisfied-at-call-rejected", "I6"),
    ("copy-without-copyable-rejected", "I8"),
    ("generic-fn-value-without-args-rejected", "I5"),
    ("implicit-receiver-move-in-closure-rejected", "I8"),
    ("implicit-receiver-move-in-loop-rejected", "I8"),
    ("implicit-receiver-move-of-field-rejected", "I8"),
    ("implicit-receiver-move-of-inout-param-rejected", "I8"),
    ("implicit-receiver-move-of-let-param-rejected", "I8"),
    ("implicit-receiver-move-then-use-rejected", "I8"),
    ("linear-bound-adds-no-operation-rejected", "I5"),
    ("linear-match-literal-component-rejected", "I8"),
    ("linear-match-omitted-field-rejected", "I8"),
    ("linear-match-underscore-rejected", "I8"),
    ("literal-against-neutral-projection-rejected", "I3"),
    ("match-budget-exceeded-rejected", "I7"),
    ("match-const-pattern-needs-wildcard-rejected", "I7"),
    ("match-int-needs-wildcard-rejected", "I7"),
    ("match-non-exhaustive-enum-rejected", "I7"),
    ("neutral-projection-does-not-match-concrete-impl-rejected", "I6"),
    ("neutral-projection-drop-without-bound-rejected", "I5"),
    ("neutral-projection-to-dyn-rejected", "I3"),
    ("never-not-inferred-rejected", "I5"),
    ("none-in-synth-rejected", "I5"),
    ("param-only-under-projection-rejected", "I5"),
    ("pattern-bare-fn-name-rejected", "I7"),
    ("pattern-bare-prelude-type-rejected", "I7"),
    ("pattern-bare-struct-name-rejected", "I7"),
    ("pattern-float-literal-rejected", "I7"),
    ("projection-arg-before-head-final-check-rejected", "I3"),
    ("projection-head-without-impl-rejected", "I6"),
    ("qualified-call-sink-receiver-needs-move-rejected", "I8"),
    ("rigid-discard-without-droppable-rejected", "I5"),
    ("rigid-drop-without-droppable-rejected", "I5"),
    ("rigid-expression-statement-without-droppable-rejected", "I5"),
    ("two-brands-one-param-rejected", "I3"),
    ("unreachable-arm-rejected", "I7"),
];
