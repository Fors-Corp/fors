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

## Counts: 648 tests, 710 files

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
| 04-authority (32) | 9 | 0 | 0 | 20 | 3 | 0 |
| 07-grammar (144) | 60 | 0 | 80 | 4 | 0 | 0 |
| 08-names (157) | 0 | 58 | 0 | 99 | 0 | 0 |
| 09-types (186) | 0 | 69 | 0 | 117 | 0 | 0 |
| total | 108 | 127 | 84 | 293 | 23 | 13 |

## Change rule

A test is ground truth for the rule it cites: change or delete it only
together with that spec rule, never to make an implementation pass.
