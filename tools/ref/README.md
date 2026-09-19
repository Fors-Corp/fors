# Reference tools (non-normative)

Small Python oracles written while auditing the conformance corpus. The specification in `docs/spec/` is the
authority; these exist so the real compiler can be tested differentially against an independent implementation.

- `fors_parse.py <dir>`: recursive-descent lexer + parser for `docs/spec/07-grammar.md`. Walks a directory of
  `.fors` files, reads each file's `//! expect:` directive and reports any file whose parse outcome disagrees
  (`bad: 0` on `tests/conformance` as of 2026-09-19). The Rust parser must agree with it on accept/reject for
  every corpus file; a disagreement means one of the two, or the grammar chapter, is wrong.
- `reduce_ref.py`: the `reduce` association from `docs/spec/03-numerics-determinism.md` (8 lanes per 256-element
  block, adjacent-pair combine, odd block carries up). Use it to compute expected outputs for reduce tests.
