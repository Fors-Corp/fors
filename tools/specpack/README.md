# specpack

Generates `docs/spec/PACK.md`, the spec-in-context pack an AI agent should
load before writing Fors. No model has seen Fors before, so an agent left to
guess will reach for Rust/Zig/Swift syntax and be wrong; this pack condenses
the normative spec, the conformance corpus and the standard library into one
file sized to actually fit in context.

## Usage

```sh
python3 tools/specpack/gen.py --write   # regenerate docs/spec/PACK.md
python3 tools/specpack/gen.py --check   # exit 1 if PACK.md is stale (CI runs this)
```

Python 3.10+, standard library only.

## What goes in, and where it comes from

| Section | Source |
|---|---|
| 1. Orientation | `tools/specpack/orientation.md` (hand-written; see below) |
| 2. Grammar | `docs/spec/07-grammar.md`: every EBNF block, the keyword lists, the operator table — verbatim |
| 3. Rule index | every numbered rule of chapters 01-06 and 08-10, one line each |
| 4. Standard-library surface | every top-level declaration under `std/`, bodies elided |
| 5. Complete examples | the smallest ACCEPTED single-file tests that together cover the most distinct top-level keywords |
| 6. Common mistakes | the most frequent diagnostic codes in the REJECTED corpus, each with a minimal offending example |
| 7. Tools | a fixed summary of `fors check` / `fors explain` / `fors fmt` |

Everything is derived at generation time: sorted traversal, no timestamps, no
absolute paths, so `--write` twice in a row produces byte-identical output.
The header carries a SHA-256 over every input file, so a stale pack is
detectable without diffing 100KB of prose.

## `orientation.md`

This is the only hand-written part of the pack, and it is the one place an
agent's syntax guesses get corrected before it writes a line of Fors. To
keep it honest, every fenced ` ```fors ` block MUST be preceded by
`<!-- from: tests/conformance/<path> -->` naming an ACCEPTED corpus file, and
`gen.py` FAILS the build if that block is not a verbatim, contiguous run of
lines from that file. You cannot invent an example here — only quote one.
Keep it at or under 120 lines; it is read in full on every load.

## Size gate

`gen.py` fails if `PACK.md` would exceed 130,000 bytes. If a corpus change
pushes it over, `gen.py` first shortens section 6 (fewer diagnostic codes),
then section 5 (fewer examples, down to a floor of 16) — never sections 1-3,
which are the parts most worth the space.
