# Fors conformance corpus

One test = one `.fors` file, or a directory whose `main.fors` carries the
directives (siblings are the build's other modules).

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
- `parse-error`: a lexical/syntax diagnostic, for the reason in `detail`.
- `check-error`: parses; checker or build rejects, reason in `detail`.
- `run-ok`: exits 0, stdout equals `detail` (`(no output)` = empty).
- `trap`: aborts with the trap kind in `detail`.

Run tests assume `io.Writer.write_line`, which no chapter defines. A
`Slice[T]` is obtained only by range-indexing a bound array (ch03 Rule 24);
`main` takes root capabilities by type (ch04 Rules 8, 21).

## Counts: 270 tests, 274 files

| Dir | parse-ok | parse-error | check-error | run-ok | trap |
|---|---|---|---|---|---|
| 01-ownership (58) | 24 | 2 | 31 | 0 | 1 |
| 02-failure (25) | 8 | 2 | 9 | 1 | 5 |
| 03-numerics (46) | 7 | 0 | 13 | 19 | 7 |
| 04-authority (32) | 9 | 0 | 20 | 3 | 0 |
| 07-grammar (109) | 48 | 57 | 4 | 0 | 0 |
| total | 96 | 61 | 77 | 23 | 13 |

## Change rule

A test is ground truth for the rule it cites: change or delete it only
together with that spec rule, never to make an implementation pass.
