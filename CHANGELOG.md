# Changelog

Two streams, per [CONTRIBUTING.md](CONTRIBUTING.md): the **language** is what a
`.fors` program is written against; the **compiler** is this repository's
implementation of it. Entries before 2026-09-20 are reconstructed from the
commit history, which predates the Conventional Commits convention.

| Language | Compiler | Meaning |
|---|---|---|
| `lang-v0.5.2` | `compiler-v0.5.0` | current |
| `lang-v0.5.2` | `compiler-v0.4.0` | checker I5 |
| `lang-v0.5.2` | `compiler-v0.3.0` | FMIR F5 |
| `lang-v0.5.1` | `compiler-v0.2.0` | checker I3.5–I4b, FMIR F1–F2 |
| `lang-v0.5.0` | `compiler-v0.1.1` | type checker I2–I3 |
| `lang-v0.5.0` | `compiler-v0.1.0` | first tagged front end |

## Language

### lang-v0.5.2 — 2026-10-02

Clarification only; no program changes meaning.

- ch03 R12 now reads that `reduce` MUST be given its final shape in FMIR as
  a function of `(n, B, L)` before parallel lowering, the tree explicit where
  `n` is comptime-known. The old wording ("MUST lower to this explicit tree")
  was unimplementable for a runtime-length input; the `--serial-elide`
  bit-exactness clause is unchanged (FMIR owner decision Q3).

### lang-v0.5.1 — 2026-10-02

Clarification only; no program changes meaning.

- ch10's conformance index names `sigpipe-ignored-write-latches-run-error`:
  a write to a closed pipe latches `io.Error.closed` (SIGPIPE is ignored)
  and `main` exits with status 2 per R40(d) — the test had asked for 0 and
  applied `else` to a total function (FMIR owner decision Q8).

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

### compiler-v0.5.0 — 2026-10-02

Type checker increment **I6** and the interpreter halves of FMIR **F4** and
**F6**, each produced by one agent and independently verified by another;
plus the chapter 05 conformance directory. Implements `lang-v0.5.2`; still
no code generator.

- **I6 — associated types, projections, normalisation.** `normalise.rs` is
  design §7.5: exact impl probe, bucket scan, memoised structural descent,
  a per-query work budget reported as T0020. Projections on concrete heads
  collapse everywhere; neutral ones match only themselves (ch09 R20);
  constraint entries are checked at the call (R62); generic method calls
  are typed. Measured through the real checker: normalisation cost is
  exactly `depth+1` and identical for 1 to 256 impls per bucket.
- **F4 (interpreter half) — exit edges.** Each edge carries the scopes
  left, the pending `defer`/`errdefer` bodies, the drops and the
  obligation discharges; the verifier asserts the list against ch01
  R23a/R23b's order instead of re-deriving it; execution follows I8b's
  order and a trap runs nothing. Lowering waits for I8b.
- **F6 (interpreter half) — arenas, allocators, `ub:`.** Byte-granular
  initialisation, arena generations with a trapping ceiling, region-scoped
  arenas, a closed nine-class `ub:` vocabulary (status 70, disjoint from
  the trap kinds), a two-kind borrow stack, provenance keyed by frame
  activation. Owner decision Q7: one trap line, backtrace opt-in.
- **Corpus.** `tests/conformance/05-ir/` holds all 22 tests chapter 05
  names (owner decision Q5): 943 tests, 1032 files. Six are real
  source-level violations that `fors check` cannot see yet because it
  never runs lowering or the IR verifier — recorded as `PENDING_05`.
- **Coverage.** 212 of chapter 09's 246 conformance tests on, 34 pending;
  672 Rust tests.
- **Verification found and fixed before merge.** I6: three over-acceptances
  (a silent method lookup when the only unifying impl was refused by its
  bounds; bounds skipped for subjects containing a neutral projection; an
  empty candidate tier accepted). F4/F6, from fifteen adversarial FMIR
  fixtures: exit edges listing scopes outer-first passed the verifier;
  nested arena regions retired the wrong arena; a root write never popped
  the borrow stack; a pointer into a returned frame panicked the
  interpreter; a `raise` from a non-entry frame was settled as `main`'s.

### compiler-v0.4.0 — 2026-10-02

Type checker increment **I5**, generic calls and generic bodies, produced by
one agent and independently verified by another. Implements `lang-v0.5.2`;
still no code generator.

- **R38 literally.** Explicit `[..]` arguments with R39's count and kind
  checks and R13 const arguments; receiver match; expected-type pre-binding
  that skips brand positions (R40) and is adopted only on success; the
  argument pass with R41's closure rule; the pending re-check with the bound
  check folded in (one path); the substituted result or T0039. Bindings are
  never revised; `never` binds nothing; generic struct literals take their
  arguments from the expected type; `with arena a:` introduces a fresh brand.
- **`fors-fir`.** `one_way_match` gains a match mode and `first_unbound`,
  and loses an equality fast path that had made every recursive generic
  call un-inferable.
- **Coverage.** 208 of chapter 09's 246 conformance tests on, 38 pending
  (was 51); R38–R41, R59, R60 enforced; `no_error_depends_on_instantiation`
  is a real 0/1/2/3-instantiation metamorphic test.
- **Verification found and fixed before merge (all over-acceptance):** a
  callable parameter's signature was never compared with what the call
  bound (`apply(2, 5)` passed); R39 fired only for slots a pending argument
  mentioned; a generic struct literal in synthesis position was silent; a
  value in a type slot absorbed the call instead of T0011.
- **Open for the owner.** `callable-bound-cannot-bind-result-rejected`
  expects T0039 in a check position where R38(c) binds `U` from the expected
  type; kept pending rather than papered over.

### compiler-v0.3.0 — 2026-10-02

FMIR increment **F5**, the `reduce` tree, produced by one agent and
independently verified by another. Implements `lang-v0.5.2`; still no code
generator.

- **One owner for the shape.** `fors-fmir::reduce`: `REDUCE_BLOCK = 256`,
  `REDUCE_LANES = 8`, `reduce_tree(n, B, L)`, the pairwise combine with the
  accumulator, lower lane and left partial on the left, a single empty side
  passing through with no op call, no identity padding (ch03 R13a), the
  independently walked comptime-`n` form, and a committed shape-table hash
  over `n ∈ 0..1024`. `[1.0, 1e16, -1e16, 1.0]` is `0.0` by the tree and
  `1.0` by a fold, as the spec requires.
- **Interpreter and lowering.** `reduce_tree` reads `B` and `L` from the
  instruction, never the host; `n = 0` traps `empty-reduce` unless an
  identity is present (R11a); array literals, `base[lo ..< hi]` with its
  alias seed, the explicit tree for a comptime-known `n`. All eight
  `03-numerics/reduce-*` conformance tests run end to end.
- **Verification found and fixed before merge, a pre-existing miscompile:**
  `fors-lower` laid out blocks by id while emitting in seal order, so an
  `if` nested in a then-branch ran the inner `else`. Regression probe added.
- `Cargo.lock` refreshed for the workspace version.

### compiler-v0.2.0 — 2026-10-02

Type checker increments **I3.5, I4a, I4b** and FMIR increments **F1, F2** of
the two design contracts, each produced by one agent and independently
verified by another; the first increments that *run* a Fors program.
Implements `lang-v0.5.1`; still no code generator.

- **I3.5 — `BodyFacts`.** The checker's side table for lowering: per-body
  expression types, callees, receiver and argument conventions, member
  indices (D1–D4). `fors-lower` reads nothing else.
- **I4a/I4b — traits, impls, member lookup.** Method resolution on nominal
  and primitive heads (ch09 R43–R46), bound satisfaction at calls (R12),
  R29's several-`Index` rule, a trait's methods exactly as visible as the
  trait (ch08 R11 — a false N0011 on every cross-module trait-method call is
  gone). Chapter 08's pending set is empty.
- **F1 — lowering and the interpreter core.** `fors-lower` walks checked
  bodies into FMIR; `fors-interp` executes it with exact integer semantics
  (`MIN / -1` traps `overflow`; a shift traps at `count >= width` — FMIR
  owner decision Q4), a bit-exact `frem`, and an in-memory `Stdout`.
- **F2 — contracts, the entry shim, exit statuses.** `pre`/`post`/
  `invariant` under the module `contracts:` policy (`.off` emits no check
  instruction); the ch02 R17 / ch10 R40(d) exit table; `SIGPIPE → SIG_IGN`
  through a real pipe in the conformance runner. Owner decision Q8: a write
  to a closed pipe latches and `main` exits 2.
- **`fors-layout`.** Type layout per FMIR owner decision Q1: declaration
  order, natural alignment, `align ≤ 16`, smallest fitting discriminant.
- **Coverage.** 195 of chapter 09's 246 conformance tests on, 51 pending
  later increments; 16 runtime conformance tests run end to end; 492 Rust
  tests; 1011 corpus files.
- **Harness.** `matmul-blocked` (cache-blocked companion to `matmul`, nine
  languages) and a `java-stream` column — sources only, no results file:
  a tuned-vs-naive claim waits for a calibrated run on a quiet machine.
- **Verification found and fixed before merge:** a method-lookup carve-out
  that stayed silent even when the impl table was complete (over-acceptance,
  I4b); a closed-pipe test that never closed a pipe (F2).
- **Process.** The repository is public. Each feature increment is followed
  by a release and a `compiler-vX.Y.Z` tag. CodeQL no longer uploads its
  database (the scheduled run failed on that upload, not on analysis).

### compiler-v0.1.1 — 2026-09-20

Type checker increments **I2** and **I3** of `docs/design/type-checker.md`,
independently verified. Still implements `lang-v0.5.0`; still no code
generator.

- **I2 — signature lowering.** Every declaration's signature is lowered to
  FIR: generics with a trait's `[Self, P1 ..]` row, bounds, projections
  (`I.Item`) with the R61 restrictions, well-formedness, the receiver rules.
- **I3 — bodies.** The two judgements (`synth` / `check`) over expressions,
  calls, member access and literals, on a flat tape with no solver.
- **Coverage.** 40 of chapter 09's 62 rules enforced; 184 chapter-09
  conformance tests on, 62 pending later increments. 240 Rust tests.
- **Measured.** Checking cost is flat in program size: x1.004 spread from 13k
  to 211k lines, t(200k)/t(100k) = 2.03. **Missed budgets, recorded rather
  than hidden:** signature lowering costs +56% time against a +50% budget and
  +2.32 B/byte against +1.5; a trait-heavy shape retains 6.77 B/byte against
  6.0.
- **A release-only defect found by I3.** `TyStore::new` interned its reserved
  rows inside `debug_assert_eq!`, so a release build rejected `let n = 1;`.
- `fors --version` reports both streams; the compiler version now lives in
  `[workspace.package]` and every crate inherits it.
- **Process.** `main` is protected: six required checks (tests and parser
  gates, rustfmt plus `fors fmt` over `std/`, clippy with warnings denied,
  CodeQL for Rust, Python and Actions), linear history, everything by pull
  request.

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
