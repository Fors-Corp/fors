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

## Counts: 349 tests, 395 files

| Dir | parse-ok | check-ok | parse-error | check-error | run-ok | trap |
|---|---|---|---|---|---|---|
| 01-ownership (58) | 24 | 0 | 2 | 31 | 0 | 1 |
| 02-failure (25) | 8 | 0 | 2 | 9 | 1 | 5 |
| 03-numerics (46) | 7 | 0 | 0 | 13 | 19 | 7 |
| 04-authority (32) | 9 | 0 | 0 | 20 | 3 | 0 |
| 07-grammar (109) | 48 | 0 | 57 | 4 | 0 | 0 |
| 08-names (79) | 0 | 24 | 0 | 55 | 0 | 0 |
| total | 96 | 24 | 61 | 132 | 23 | 13 |

## Change rule

A test is ground truth for the rule it cites: change or delete it only
together with that spec rule, never to make an implementation pass.
