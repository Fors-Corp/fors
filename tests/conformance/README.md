# Fors conformance corpus

One test = one `.fors` file, or a directory whose `main.fors` carries the
directives (siblings are the build's other modules).

Module names (ch08 R1, R24): a directory test is a manifest-less build
whose source root is the test directory, so its file names are real and
must obey ch08 R24. A single-file test is built as if its file were named
after its `module` header (`main.fors` when it has none); the hyphenated
corpus file name is the test's name, not the module's file name.

## Directives (leading `//!` lines)

- `name:` spec conformance-test name.
- `rule:` owning rule: `NN.Rk`; ch07 uses `07.Dk` (disambiguation), `07.Lk`
  (lexical item) or a section name (`07.Grammar`, `02.Definitions`).
- `expect:` a kind below. `detail:` its payload; text after ` -- ` is comment.
- `manifest:` optional; following `//!` lines are the manifest (placeholder
  schema, unspecified so far).

## Expectation kinds

- `parse-ok`: zero lexical/syntax diagnostics. Says nothing about the
  checker, even in `*-accepted` files.
- `check-ok`: parses with zero lexical/syntax diagnostics AND passes name
  resolution with zero diagnostics; used by ch08's name-resolution corpus.
- `parse-error`: a lexical/syntax diagnostic, for the reason in `detail`.
- `check-error`: parses; checker or build rejects, reason in `detail`.
- `run-ok`: exits 0, stdout equals `detail` (`(no output)` = empty). A
  `\n` in the directive stands for a line break (round-6 verification:
  `3\n2\n1` is the three lines `3`, `2`, `1`, each ending in a newline).
- `run-error`: added in round 6 (2026-09-20, O4; ch02 Rule 17). The
  program is built and run, it MUST exit with status 1, and its standard
  error MUST equal the directive's `detail` followed by a newline (the
  directive carries the line without its trailing newline). A program that
  exits 2 — `main` RETURNED but the final `Stdout` flush failed or an error
  was latched (ch10 Rule 40(d)) — is expected with `run-error` plus an
  explicit `status: 2` field, which then replaces the stderr comparison.
  A `status: 2` test is run with the standard OUTPUT descriptor closed
  before `main` starts (the harness's only way to make the final flush
  fail deterministically; ch02 Rule 17 makes the entry shim ignore
  `SIGPIPE`), and its stderr is not compared.
- `trap`: aborts with the trap kind in `detail`.

Run tests assume `io.Writer.write_line`, which no chapter defines. A
`Slice[T]` is obtained only by range-indexing a bound array (ch03 Rule 24);
`main` takes root capabilities by type (ch04 Rules 8, 21).

## Counts: 921 tests, 1010 files

(Round-6 verification (2026-09-20): +26 tests. 01-ownership +19 — the
five `run-ok` `defer`/`errdefer` behaviour tests ch01 listed but the
implementation stage never wrote, plus `defer-nested-scope-order-run-ok`;
the R19c tests that were listed but missing (`scoped-through-generic-
{inout-param,raises}-rejected`, `scoped-copy-into-field-via-let-param-
rejected`, `closure-returned-with-local-capture-rejected`); the closure-
capture tests of the new ch01 R19d; `zip-two-scoped-sources-local-
accepted` (ch01 R19c(d): a result keeps EVERY scoped source, so the
rejected zip test is now the RETURNED form, here and in 10-std);
`errdefer-{without-error-exit,after-fallible-call}-rejected` (ch01 R23b:
an `errdefer` no error exit follows is an error);
`linear-enum-payload-one-arm-unconsumed-rejected`;
`adaptor-chain-for-mutates-source-rejected`. 08-names +1
(`linear-impl-outside-defining-module-rejected`, N0021). 09-types +4
(`adaptor-map-closure-returns-linear-rejected` T0012 — `map` and
`Mapped` now carry `U: Droppable`, forced by ch09 R17/R21;
`adaptor-impl-unbounded-item-rejected`; `adaptor-annotated-binding-
mismatch-rejected`; `adaptor-generic-fn-item-uninstantiated-rejected`,
which also corrected `adaptor-chain-rigid-receiver-accepted` to write
`same[I.Item]`). 10-std +1 (`zip-two-scoped-sources-local-accepted`);
`try-for-each-error-propagates-run-ok` now obtains its iterator with
`mem.iter(xs)`, since a `Slice` has no inherent `iter`.)

(Round 6 (2026-09-20): applied the linearity, `defer`/`errdefer`,
iterator-method-chaining and `main`-error decisions. +165 tests:
01-ownership +52 (Rules 19c, 22-22i, 23-23f), 02-failure +11 (Rules 16-17
and the new `run-error` kind), 07-grammar +13 (the two productions, the two
reserved words, Disambiguation 9 and the recovery case), 09-types +54
(Rules 10c, 11, 21, 23, 24, 31, 33, 43, 50, 57, including the whole O3
method-chaining derivation) and 10-std +35 (Rules 11, 11c, 32-35, 40).
Eight files were MIGRATED: the three free-function adaptor/consumer tests
became method chains (`mem.map` … `mem.try_for_each` are deleted), four
ch10 tests that held a linear value across a `?` gained `defer`/`errdefer`,
and `linear-element-container-deinit-trap` became
`vec-deinit-empty-nonempty-trap`, round 6 having made the rest of ch10 Rule
11c static. `fors-resolve`'s harness gained
`ch01_ownership_corpus_resolver_view`: a ch01 `check-ok`/`check-error` test
must be resolver-CLEAN, as ch09's and ch10's already must, because ch01's
codes are the checker's. The table below now also counts 10-std, which
round 5's table omitted.)

(Round-5 verification (2026-09-20): +7 tests. 04-authority
`main-forged-std-module-rejected` (a user module `io` cannot forge
`io.Stdout`; ch04 R8 now judges the head by its binding) and
`main-aliased-std-import-accepted` (`use std.io as w;` then `w.Stdout`);
07-grammar `reserved-{spmd,kernel}-as-member-access-reject` (`x.spmd`);
08-names `closure-param-named-self-{shadows-receiver-rejected,in-free-fn-
accepted}` and `body-mention-of-std-module-adds-no-edge-accepted` (the
module graph is exactly the `use` edges: a body's `io.` and a header's
`needs { env }` add none).)

(Round 5 (2026-09-19): applied the grammar and std-module decisions --
D1 the receiver shorthand `convention "self"` (ch07 Disambiguation 21),
D2 `spmd`/`kernel` reserved-unused, D3 std modules require an import.
+13 in 07-grammar (7 receiver-shorthand, 6 reserved-word tests); +15 in
08-names (10 "std module used without `use`" tests, one per known module
name; `use-std-{module,mem,item-path}-accepted`,
`use-std-{unknown-module,alone}-rejected`,
`item-named-as-std-module-with-import-rejected`,
`local-shadows-imported-std-module-rejected`,
`param-shadows-imported-std-module-rejected`), with four round-2/3 tests
flipped or renamed as ch08's list records and one
(`local-shadows-prelude-module-path-head-accepted`) deleted, its premise
being impossible now. 37 files gained a `use std.<m>;` header line and 62
files took the receiver shorthand; ch09's
`local-shadowing-prelude-module-as-type-head-rejected` was re-aimed at a
prelude type and renamed. Three tests keep the explicit `self: Self`
receiver on purpose.)

(Round 4 (2026-09-19): applied the type-system decisions -- integer literal
default `i32`, homogeneous operators, associated types with projections
and constraint entries, implicit `sink self` receiver move; new directory
09-types (186 tests, ch09's list plus the verification round's soundness
probes); +19 in 07-grammar (associated-type items, constraint entries,
`type` reserved, recovery), +12 in 08-names (deferred projections,
round-4 prelude names, constraint-entry heads, shared member tables).
A 09-types `detail` starts with the expected code: `T00nn` (ch09), an
ch08 `N00nn`, or `ch01 Rk` when ch01's rule decides; text after ` -- ` is
comment. Until a type checker exists, `fors check` must be CLEAN on every
T-coded or ch01-coded 09-types test and report exactly the named N-code
on the others (crates/fors-resolve/tests/conformance.rs).)

| Dir | parse-ok | check-ok | parse-error | check-error | run-ok | run-error | trap |
|---|---|---|---|---|---|---|---|
| 01-ownership (128) | 24 | 25 | 2 | 70 | 6 | 0 | 1 |
| 02-failure (36) | 8 | 1 | 2 | 10 | 2 | 7 | 6 |
| 03-numerics (46) | 7 | 0 | 0 | 13 | 19 | 0 | 7 |
| 04-authority (34) | 9 | 1 | 0 | 21 | 3 | 0 | 0 |
| 07-grammar (172) | 71 | 0 | 97 | 4 | 0 | 0 | 0 |
| 08-names (176) | 0 | 61 | 0 | 115 | 0 | 0 | 0 |
| 09-types (246) | 0 | 95 | 0 | 151 | 0 | 0 | 0 |
| 10-std (83) | 0 | 26 | 0 | 44 | 7 | 1 | 5 |
| total (921) | 119 | 209 | 101 | 428 | 37 | 8 | 19 |

## Change rule

A test is ground truth for the rule it cites: change or delete it only
together with that spec rule, never to make an implementation pass.
