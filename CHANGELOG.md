# Changelog

Two streams, per [CONTRIBUTING.md](CONTRIBUTING.md): the **language** is what a
`.fors` program is written against; the **compiler** is this repository's
implementation of it. Entries before 2026-09-20 are reconstructed from the
commit history, which predates the Conventional Commits convention.

| Language | Compiler | Meaning |
|---|---|---|
| `lang-v0.5.0` | `compiler-v0.1.0` | current |

## Language

### lang-v0.5.0 — 2026-09-20 (round 6)

**BREAKING.** Three owner decisions, each invalidating programs that compiled
under 0.4.0.

- **Linear types.** Because allocators are explicit, a `Vec`/`Own`/`String`/
  `File` cannot free itself; a type may now carry a cleanup obligation, and
  every path on which such a value dies unconsumed is an error (ch01 R22–R22i).
- **`defer` / `errdefer`.** Scope-exit statements so cleanup is written once
  rather than on every `?` path; `errdefer` runs only on an error exit, and a
  trap (whole-process abort) runs neither (ch01 R23–R23f, ch07, ch02 R16).
- **Iterator adaptors became methods.** `it.map(f).take(3)` replaces the free
  functions `mem.map(&it, f)`; provided methods on `Iterator` returning
  concrete adaptor types, proved sound without blanket impls, plus one new
  scope-inheritance rule (ch01 R19c–R19d, ch09 R21/R43, ch10 R32–R35).
- An error raised out of `main` prints one line on stderr and exits 1.

### lang-v0.4.0 — 2026-09-19 (round 5, grammar freeze)

**BREAKING.** Mandatory `;`; flat bitwise tier (mixing needs parentheses);
receiver shorthand `inout self`; `spmd`/`kernel` reserved; **std modules
require `use std.<m>;`** — the prelude keeps no modules, so the module graph is
exactly the explicit `use` edges and the resolver's body scan is gone;
allocators are explicit values with the process heap arriving as a `main`
parameter; trap = whole-process abort confirmed; overlapping `let`/`let`
accepted. Chapter 10 (the std surface, 57 rules) is added.

### lang-v0.3.0 — 2026-09-19 (round 4)

**BREAKING.** Associated types with containments that keep type-checking
near-linear (no projections in impl heads, structural normalisation, no
equality bounds, no GATs); a `sink self` method call moves a named receiver
implicitly; unsuffixed integer literals default to `i32`; operators are
homogeneous. Chapter 09 (types, 62 rules) is added.

### lang-v0.2.0 — 2026-09-19 (round 3)

**BREAKING.** A binding in a pattern is written `let n`, so a bare name is
always a reference; `use a.b as c;` import aliases; a local may shadow a
prelude name.

### lang-v0.1.0 — 2026-09-19

First normative specification: chapters 01–08 (ownership and conventions,
failure and traps, numerics and determinism, capabilities, the IR contract,
measurement, the grammar, names and visibility), with a conformance corpus and
an independent reference parser.

## Compiler

### compiler-v0.1.0 — 2026-09-20

Implements `lang-v0.5.0` at the front end; there is no code generator yet.

- **Front end.** Zero-dependency SoA lexer, recursive-descent parser to a
  lossless flat syntax tree (110k lines in ~21 ms), declaration index with
  separate signature and body fingerprints, module graph, name resolver, and
  `fors check`. 95k lines index + resolve in 48 ms.
- **Types.** `fors-fir`: hash-consed interned types, canonical index-free
  signature encoding, `sig_hash`/`decl_fingerprint`, one-way matching and
  substitution-normalisation. The `fir-normalise` spike found the designed
  substitution memo key **unsound** (two instantiations sharing one cache slot)
  before any checker code existed.
- **Tools.** `fors-fmt` — one canonical style, 4-space indent, 100 columns;
  lossless, idempotent and diagnostic-neutral across 1010 corpus files and the
  std tree. `fors-lsp` — JSON-RPC over stdio, hand-written JSON, UTF-16
  positions, diagnostics, symbols, folding and formatting.
- **Verification.** 158 Rust tests, ~920 conformance tests, the two parsers
  checked against each other on every file.
- **Backend feasibility: GO.** `spikes/aarch64-macho` compiles a Fors subset to
  a signed arm64 Mach-O executable with no LLVM, no assembler, no linker and no
  `codesign`: four programs build and run with an empty `PATH`, 0.4 ms
  in-process against 63–93 ms through the system toolchain.
- **Benchmark harness.** 10 kernels × 10 toolchains with a correctness gate, a
  thermal canary, same-file baselines, and compile-speed plus incremental
  rebuild comparators. No performance claim without a results file.
