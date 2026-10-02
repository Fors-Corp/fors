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
// I5 (generic calls and generic bodies) deleted THIRTEEN rows —
// `adaptor-generic-fn-item-uninstantiated-rejected`,
// `binding-never-revised-rejected`, `brand-identity-mismatch-rejected`,
// `cannot-infer-rejected`, `closure-before-its-iterator-rejected`,
// `closure-before-its-type-source-rejected`,
// `generic-fn-value-without-args-rejected`,
// `literal-against-neutral-projection-rejected`,
// `never-not-inferred-rejected`, `none-in-synth-rejected`,
// `param-only-under-projection-rejected`,
// `projection-head-without-impl-rejected` and
// `two-brands-one-param-rejected` — and RETAGGED the six it found were
// not its own. After it no row is tagged `I5`. The reasons, once, here:
//
// - `callable-bound-cannot-bind-result-rejected` I5 -> I8b. R38 as
//   §7.4 writes it ACCEPTS this program: `return apply(2, double)` is a
//   CHECK position, so step (c) matches the declared result `U` against
//   the expected `i32` and binds it — the file's own premise ("`F:
//   fn (...) -> U` leaves `U` uninferable") holds only in SYNTH
//   position, which is how the spec's R41 example writes it (`let d =
//   apply(...)`). No §13 GATE names this file; the only §13 sentence
//   that assigns it is I8's "Round 6 added 58 more files to `09-types`
//   (244 now) ...; they stay `Pending(I8b)` here", and `git log` shows
//   it arrived in round 6 (ede5dad). I8b owns the round-6 flip.
// - `linear-bound-adds-no-operation-rejected` I5 -> I8b. §13's I8b GATE
//   names the file verbatim, in its "R22-R22c, R22e, R22f, declarations
//   and types (19)" group, and I8b is the increment that BUILDS
//   `ty::droppable` (§8's ch01 R22c row: "`ty::droppable`,
//   `flow::drop_rigid` (T0057, amends row 57) | I8b").
// - `rigid-drop-without-droppable-rejected`,
//   `rigid-discard-without-droppable-rejected` and
//   `rigid-expression-statement-without-droppable-rejected` I5 -> I8b.
//   All three are named verbatim in the same I8b GATE group, beside the
//   `rigid-drop-with-droppable-accepted` that is already on.
// - `neutral-projection-drop-without-bound-rejected` I5 -> I8b. The file
//   drops the result of `h.get()`, whose type is the neutral projection
//   `H.A`: the OPERATION is R22c's "dropping a rigid value needs a
//   bound", which §8's ch01 R22c row assigns to I8b's `ty::droppable` /
//   `flow::drop_rigid`; I6 contributes only the `holds` Proj arm that
//   supplies the bound set, so the later of the two increments owns it.
// I6 (associated types, projections, normalisation, constraint entries)
// deleted FOUR rows and retagged none. Two were already tagged I6
// (`constraint-entry-unsatisfied-at-call-rejected`,
// `neutral-projection-does-not-match-concrete-impl-rejected`); the other
// two carried a stale I3 tag that design §13's I6 GATE overrides, and the
// reasons, once, here:
//
// - `projection-arg-before-head-final-check-rejected` I3 -> I6, deleted.
//   §13's I6 GATE names it verbatim in its R38 group ("R38 (`map-sum-
//   closure-checked-accepted`, `projection-arg-before-head-accepted`,
//   `-final-check-rejected`, `projection-result-against-expected-
//   accepted`)"). It needs R20: the literal is synthesised as `i32`
//   before `I` is bound, and only `subst_norm` with a real projection
//   solver turns `I.Item` into the `i64` the final check compares it
//   against.
// - `neutral-projection-to-dyn-rejected` I3 -> I6, deleted. No §13 GATE
//   names it (its rule is R10), but it is I6's by machinery and not by
//   tag: `h.get()` on a rigid `H: Has` is a GENERIC TRAIT METHOD, which
//   §7.4's container slots (I6) are what make typable at all — before
//   this increment `methods.rs` answered `Candidate::Generic` and the
//   whole call was untyped, so the `as dyn Tr` had nothing to reject. The
//   row is deleted rather than retagged because it now passes.
//
// Nothing in I6 moved a row the other way: the 34 rows below were each
// re-tested with the list emptied and every one of them still fails for
// its own increment's reason.
//
// The I6 verifier retagged ONE row, for the reason I4b gave its sibling:
//
// - `adaptor-annotated-binding-mismatch-rejected` I3 -> I8b. R38(b)'s
//   receiver binding is on since I5, and its `Self := Mapped[SliceIter[i32],
//   i32]` needs `Iterator`'s PROVIDED `map`/`take` and the `Mapped`/`Taken`
//   adaptors, which exist only in `std/mem/seq.fors`. The ch09 harness
//   checks each file alone, where `Iterator` is the prelude row declaring
//   `next` and nothing else, so no call in the body types and nothing can
//   be compared. No §13 GATE names it (I6's R38 group lists four files and
//   this is not one); the only §13 sentence that assigns a round-6
//   `09-types` file is I8b's. The I3 tag was stale by the same argument
//   that moved `adaptor-name-clash-two-traits-rejected` to I8b.
// I7 (patterns and exhaustiveness) deleted the ELEVEN rows tagged `I7`
// (`pat::check_pat`/`exhaust::check_match` now decide R50, R53, R54, R55
// themselves) and retagged none: every remaining row was re-tested with
// the list emptied and still fails for its own increment's reason. The
// `linear-match-*` rows stay `I8` — R50's "linear components" clause
// (ch01 R22d(ii)) is explicitly not this increment's (design §13 I7's
// GATE names only R50 (4)/R51 (1)/R53 (6)/R54 (3)/R55 (2), none of them
// the three `linear-match-*` files), so `pat.rs` does not inspect
// linearity at all and these three still fail for I8's reason, unchanged.
const PENDING_09_MAX: usize = 23;
const PENDING_09: &[(&str, &str)] = &[
    ("adaptor-annotated-binding-mismatch-rejected", "I8b"),
    ("adaptor-map-closure-returns-linear-rejected", "I8b"),
    ("adaptor-name-clash-two-traits-rejected", "I8b"),
    ("adaptor-on-field-receiver-rejected", "I8"),
    ("adaptor-on-inout-receiver-rejected", "I8"),
    ("brand-param-as-value-type-rejected", "I8"),
    ("callable-bound-cannot-bind-result-rejected", "I8b"),
    ("copy-without-copyable-rejected", "I8"),
    ("implicit-receiver-move-in-closure-rejected", "I8"),
    ("implicit-receiver-move-in-loop-rejected", "I8"),
    ("implicit-receiver-move-of-field-rejected", "I8"),
    ("implicit-receiver-move-of-inout-param-rejected", "I8"),
    ("implicit-receiver-move-of-let-param-rejected", "I8"),
    ("implicit-receiver-move-then-use-rejected", "I8"),
    ("linear-bound-adds-no-operation-rejected", "I8b"),
    ("linear-match-literal-component-rejected", "I8"),
    ("linear-match-omitted-field-rejected", "I8"),
    ("linear-match-underscore-rejected", "I8"),
    ("neutral-projection-drop-without-bound-rejected", "I8b"),
    ("qualified-call-sink-receiver-needs-move-rejected", "I8"),
    ("rigid-discard-without-droppable-rejected", "I8b"),
    ("rigid-drop-without-droppable-rejected", "I8b"),
    ("rigid-expression-statement-without-droppable-rejected", "I8b"),
];
