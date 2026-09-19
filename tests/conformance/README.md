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
- `run-ok`: exits 0, stdout equals `detail` (`(no output)` = empty).
- `trap`: aborts with the trap kind in `detail`.

Run tests assume `io.Writer.write_line`, which no chapter defines. A
`Slice[T]` is obtained only by range-indexing a bound array (ch03 Rule 24);
`main` takes root capabilities by type (ch04 Rules 8, 21).

## Counts: 683 tests, 771 files

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

| Dir | parse-ok | check-ok | parse-error | check-error | run-ok | trap |
|---|---|---|---|---|---|---|
| 01-ownership (58) | 24 | 0 | 2 | 31 | 0 | 1 |
| 02-failure (25) | 8 | 0 | 2 | 9 | 1 | 5 |
| 03-numerics (46) | 7 | 0 | 0 | 13 | 19 | 7 |
| 04-authority (34) | 9 | 1 | 0 | 21 | 3 | 0 |
| 07-grammar (159) | 65 | 0 | 90 | 4 | 0 | 0 |
| 08-names (175) | 0 | 61 | 0 | 114 | 0 | 0 |
| 09-types (186) | 0 | 69 | 0 | 117 | 0 | 0 |
| total | 113 | 131 | 94 | 309 | 23 | 13 |

## Change rule

A test is ground truth for the rule it cites: change or delete it only
together with that spec rule, never to make an implementation pass.
