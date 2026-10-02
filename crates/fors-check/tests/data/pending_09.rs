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
// I8 (the flow pass) deleted the NINE rows that are the design §13 I8
// GATE's "9 ch01-coded ch09 tests" — and they are exactly the nine
// pending files that pre-date round 6, which is the same GATE's other
// half ("`PENDING_09` empty over the **186** pre-round-6 ch09 tests").
// `git log --diff-filter=A` dates every pending row: these nine arrived
// with 9dcfbb4 ("Round-4 ... 186 chapter-09 tests") and the other
// fourteen with ede5dad ("Round 6 ... 191 new corpus tests").
//
//   brand-param-as-value-type-rejected                (ch01 R15d, O0015)
//   copy-without-copyable-rejected                    (ch01 R3,   O0003)
//   implicit-receiver-move-in-closure-rejected        (ch01 R4a(e))
//   implicit-receiver-move-in-loop-rejected           (ch01 R4a(b))
//   implicit-receiver-move-of-field-rejected          (ch01 R4a(c))
//   implicit-receiver-move-of-inout-param-rejected    (ch01 R4a(d))
//   implicit-receiver-move-of-let-param-rejected      (ch01 R3)
//   implicit-receiver-move-then-use-rejected          (ch01 R4a(a))
//   qualified-call-sink-receiver-needs-move-rejected  (ch01 R2,   O0002)
//
// It RETAGGED the five rows that still carried `I8` although they are
// round-6 files, which §13's I8 paragraph assigns elsewhere in so many
// words ("Round 6 added 58 more files to `09-types` (244 now) ...; they
// stay `Pending(I8b)` here"). The reasons, once, here:
//
// - `adaptor-on-field-receiver-rejected`,
//   `adaptor-on-inout-receiver-rejected` I8 -> I8b. Both arrived in
//   ede5dad, and both need `Iterator`'s PROVIDED `take`, which exists
//   only in `std/mem/seq.fors`: in the ch09 harness, where each file is
//   checked alone, `Iterator` is the prelude row declaring `next` and
//   nothing else, so `it.take(2)` does not resolve and there is no
//   receiver move for the flow pass to judge. This is the argument I4b
//   already applied to `adaptor-name-clash-two-traits-rejected`.
// - `linear-match-literal-component-rejected`,
//   `linear-match-omitted-field-rejected`,
//   `linear-match-underscore-rejected` I8 -> I8b. All three arrived in
//   ede5dad and all three cite ch01 R22d(ii), which §8's "ch01
//   R22d-R22g" row assigns to I8b (`flow::linear` over I8's tape plus
//   `pat::binds_every_linear` for (ii)). §16 amendment 10 states I8's
//   scope as "R3/R4a/R8/R46 only", so linearity was never this
//   increment's; I7's note that they "stay `I8`" read the tag rather
//   than §8's row.
//
// After I8 every remaining row is tagged `I8b`.
//
// I8b (round-6 flow) deleted SEVEN rows — `linear-bound-adds-no-operation-
// rejected`, `linear-match-{literal-component,omitted-field,underscore}-
// rejected`, `neutral-projection-drop-without-bound-rejected`,
// `rigid-{discard,drop}-without-droppable-rejected` — and
// `rigid-expression-statement-without-droppable-rejected` with a one-token
// repair to the corpus file, recorded here because it is a change to the
// corpus and not to the checker:
//
// - `rigid-expression-statement-without-droppable-rejected`. The file's
//   helper was `fn make[T](let t: T) -> T { return t; }`, which is itself
//   ill-formed: `return t` moves out of a `let` parameter, ch01 R3, the
//   very violation `copy-without-copyable-rejected` asserts — which is
//   what `PENDING_SPEAKS` recorded while the row was pending. A file
//   cannot yield "exactly one diagnostic" with a second, unrelated
//   violation in another declaration, so the helper now reads
//   `fn make[T](sink t: T) -> T { return move t; }` and the call
//   `make(move x)` (ch01 R2's marker). The test's own subject — an
//   expression statement dropping a value of rigid type, T0057 — is
//   unchanged, and it is now the file's single diagnostic.
//
// THREE rows stay, each blocked on something that is not this increment's
// to decide:
//
// - `callable-bound-cannot-bind-result-rejected` needs an OWNER decision.
//   R38 as design §7.4 writes it ACCEPTS this program (the I5 verifier's
//   note above): `return apply(2, double)` is a CHECK position, so step
//   (c) matches the declared result `U` against the expected `i32` and
//   binds it. The file's premise ("`F: fn (...) -> U` leaves `U`
//   uninferable") holds only in SYNTH position. Either the corpus file
//   moves the call into a `let` (SYNTH) or §7.4 gains a clause; I8b
//   implements neither, because both are the owner's call.
// - `adaptor-name-clash-two-traits-rejected` and
//   `adaptor-on-{field,inout}-receiver-rejected`,
//   `adaptor-annotated-binding-mismatch-rejected` need `Iterator`'s
//   PROVIDED adaptors (`map`, `take`, `Mapped`, `Taken`), which exist only
//   in `std/mem/seq.fors`; the ch09 harness checks each file alone, where
//   `Iterator` is the prelude row declaring `next` and nothing else. The
//   MECHANISMS they test are implemented and are proved by probes that
//   supply the adaptor trait locally (`probes.rs`:
//   `linear_closure_result_fails_its_droppable_bound`,
//   `adaptor_receiver_conventions_are_decided_with_a_local_trait`). The
//   rows stay until the harness can build a file against `std`.
// - `adaptor-map-closure-returns-linear-rejected` is the same: its `U:
//   Droppable` bound with `U := Res` and `impl Linear for Res` is decided
//   by `ty::lin`/`ty::droppable` as of this increment, and the probe
//   above proves it, but the file's `v.iter().map(..)` needs std's
//   adaptors to type at all.
const PENDING_09_MAX: usize = 6;
const PENDING_09: &[(&str, &str)] = &[
    ("adaptor-annotated-binding-mismatch-rejected", "I8b"),
    ("adaptor-map-closure-returns-linear-rejected", "I8b"),
    ("adaptor-name-clash-two-traits-rejected", "I8b"),
    ("adaptor-on-field-receiver-rejected", "I8b"),
    ("adaptor-on-inout-receiver-rejected", "I8b"),
    ("callable-bound-cannot-bind-result-rejected", "I8b"),
];

/// A pending test on which the checker nonetheless SPEAKS, because a
/// declaration OTHER than the one the test is about violates a rule this
/// increment did reach. The default for a pending row is silence — an
/// increment that has not reached a rule must not guess at it — and this
/// list is the explicit, asserted-live exception: the diagnostic must be
/// real and must NOT be the code the test expects, so a row cannot be
/// parked here to hide a wrong answer about its own rule.
const PENDING_SPEAKS: &[(&str, &str)] = &[];
