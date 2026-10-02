# Changelog

Two streams, per [CONTRIBUTING.md](CONTRIBUTING.md): the **language** is what a
`.fors` program is written against; the **compiler** is this repository's
implementation of it. Entries before 2026-09-20 are reconstructed from the
commit history, which predates the Conventional Commits convention.

| Language | Compiler | Meaning |
|---|---|---|
| `lang-v0.5.3` | `compiler-v0.16.0` | current |
| `lang-v0.5.3` | `compiler-v0.15.0` | checker I10b, the silent-TY_ERROR sweep gate |
| `lang-v0.5.3` | `compiler-v0.14.0` | FMIR F4/F6, defer and arena lowering |
| `lang-v0.5.3` | `compiler-v0.13.0` | FMIR F-mono, monomorphisation and pattern lowering |
| `lang-v0.5.3` | `compiler-v0.12.0` | checker I9, the query engine and the M1 exit |
| `lang-v0.5.3` | `compiler-v0.11.0` | checker I10a |
| `lang-v0.5.3` | `compiler-v0.10.0` | FMIR F1-completion |
| `lang-v0.5.3` | `compiler-v0.9.0` | checker I8b, the round-6 flow |
| `lang-v0.5.2` | `compiler-v0.8.0` | FMIR F7 in part |
| `lang-v0.5.2` | `compiler-v0.7.0` | checker I8, the flow pass |
| `lang-v0.5.2` | `compiler-v0.6.0` | checker I7 |
| `lang-v0.5.2` | `compiler-v0.5.0` | checker I6, F4/F6 interpreter halves, ch05 corpus |
| `lang-v0.5.2` | `compiler-v0.4.0` | checker I5 |
| `lang-v0.5.2` | `compiler-v0.3.0` | FMIR F5 |
| `lang-v0.5.1` | `compiler-v0.2.0` | checker I3.5–I4b, FMIR F1–F2 |
| `lang-v0.5.0` | `compiler-v0.1.1` | type checker I2–I3 |
| `lang-v0.5.0` | `compiler-v0.1.0` | first tagged front end |

## Language

### lang-v0.5.3 — 2026-10-02

Clarification (PATCH). Chapter 10 S0027: `Option.unwrap_or` is declared in
a `T: Droppable` block — its `some` arm drops `fallback`, which chapter 01
Rule 22c forbids for a rigid `T`; the same round-6 move the chapter already
made for `clear` and `deinit`. No rule's meaning changes. (Surfaced by the
type checker's increment I8b, the first to check `std` under Rule 22.)

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

### compiler-v0.16.0 — 2026-10-02

Type checker increment **I10**, the other chapters' obligations, produced
by two agents in sequence (ch02 + ch03, then ch04 + ch01) and
independently verified by a third. Implements `lang-v0.5.3`; still no
code generator.

- **Chapter 02, failure (`F00nn`).** A raising call must be followed by
  `?` or `else |e|`; `?` and `raise` only inside a `raises` function and
  only on a raising call; `?` across two error types needs one
  `ErrorFrom` impl; a `secret` value may not appear in a contract; a
  contract in a `.proved` module is an error (there is no proof
  engine); an `extern "c"` function may not raise. The checker publishes
  what FMIR F3 lowers from: per `?` site the callee's error set and the
  propagation edge, per `else |e|` the handler arm and binding, per
  `raise` the variant.
- **Chapter 03, numerics (`D00nn`).** The explicit-arithmetic family
  (`wrap_*`, `sat_*`, `unchecked_*`, `wrap_as`/`sat_as`/`trunc_as`) is
  now *declared* on every numeric primitive instead of being a spelling
  the checker stayed silent on; `unchecked_*` outside an `@unsafe`
  declaration, implicit numeric conversion, lossy conversion to a
  non-numeric target, an unknown `@fastmath` flag, a `comptime_int`
  escaping to runtime without `as`, malformed `reduce`, a scalar
  accumulator in `parallel for`, an unspecialised generic call in a
  `simd` body, a non-power-of-two lane count, `SVec` outside a `simd`
  local and the array-literal rules are all reported. `comptime_int`,
  `comptime_float`, `SVec`, `i128` and `u128` resolve as prelude names.
  A new fix-it, `convert-with-as`, is attached to the conversion rules.
- **Chapter 04, authority (`A00nn`).** Extern calls and inline `asm`
  inside generic functions or `comptime`, extern calls from a module
  without `ffi`, construction of any of the twelve root-capability types,
  malformed `@unsafe`, a `comptime` block reading a run-time binding, a
  comptime file read not listed in `inputs {}`, `asm` placement and
  `syscall` needs, and `asm` result typing. Four ch04 tests stay pending
  with a stated reason (two need the manifest, one is comptime
  evaluation — F9's — and one is a corpus layout defect).
- **Chapter 01, brands and `Shared`.** Arena and allocator values may not
  be moved or constructed by hand; brand kinds are closed and a non-brand
  type in a brand slot is rejected (previously a silent `TY_ERROR`);
  arena subscripts are typed; `with allocator` brands are checked;
  `atomic[T]` fields only in `Shared` types, with the field-wise `Shared`
  checks (and `@unsafe impl` skipping them).
- **Coverage.** Every ch02 (10) and ch03 (13) check-error test and 17 of
  21 ch04 ones report their code; the ch01 brand/`Shared` subset (11
  files) is on. Per-chapter harness views with pending tables that may
  only shrink; the query DAG's oracle now covers the ch02/ch03/ch04
  corpora too; 28 accepted/rejected probe pairs; the silent-`TY_ERROR`
  allow-list shrank from 188 to 166 rows. 938 Rust tests (20 held out
  with a stated reason).
- **Verification found and fixed before merge** (190 mutation programs):
  a non-brand type passed for a brand parameter was accepted; a
  `comptime_int` written as a parameter, result, field or generic
  argument type was accepted; a `comptime_int` passed through a generic
  parameter escaped unreported. One fors-lower gate test asserted the
  old checker silence on `unchecked_add` and now expects the diagnostic.
- **For the owner.** `PENDING_04` has four rows where the design wrote
  two; four corpus files declare module names their paths contradict or
  use placeholder attributes; several files draw one code where their
  directive cites another rule (listed in the harness tables); ch08's
  "closed prelude" versus the five names ch03 uses; the numeric methods'
  callee row stays undecided until the next FMIR increment lowers from
  the published numeric facts.

### compiler-v0.15.0 — 2026-10-02

Type checker increment **I10b**, produced by one agent and independently
verified by another. Implements `lang-v0.5.3`; still no code generator.

- **The no-silent-`TY_ERROR` gate.** A new test sweeps every typed node
  of the whole `std` package and of every check-ok/run-ok conformance
  target (245, built with `std`): a node that was typed and ended
  `TY_ERROR` while its declaration produced no diagnostic is a failure,
  named by its own span. Baseline before the increment: 210 absorbed
  nodes (17 in `std`); now 0 in `std` and 188 over the corpus, each
  carried by a named allow-list row that must stay live, so a fix
  deletes its row rather than leaving it stale.
- **Six families of silent absorption, fixed at the root.** Methods of
  a trait with parameters (`s.conv()`, `Allocator[A: brand]`'s `free`);
  explicit type arguments on a value head (`Option[i64].none`,
  `Bag[i64].of(1)`); `self.items_mut()[i]` inside an `IndexMut` impl
  (the sibling `Index` impl's `Output` is read, and a missing one is
  reported); a const generic parameter as a value, with a brand
  parameter in value position reported as O0015; `Self { .. }` inside an
  impl; `Option.some(1)` and `Option[i64].none` as variant constructors.
- **Verification found and fixed before merge.** Two impls of a
  parameterised trait at different arguments silently resolved to the
  first (now R44's ambiguity); explicit arguments with the wrong count
  on a value head were silent (now R11); the producer's own change
  regressed a called unit variant from T0043 to silence; `Self { .. }`
  in a trait default body, a bare tuple variant, and a type named as a
  value were silent or silently accepted; `impl IndexMut` written before
  `impl Index` was wrongly rejected. Reverting one family makes the
  gate name ten offenders, so the gate is not tautological.
- **Finding for the owner.** 137 of the 188 allow-list rows are one
  unimplemented binding: the eight prelude-opaque names (`Vec`, `Map`,
  `Buffer`, `String`, `Allocator`, …) stay opaque even when package
  `std` is in the build, so every expression over them is absorbed and
  ~70 Iterator-adaptor corpus files pass check-ok vacuously. That is the
  next increment, I10c.
- **Coverage.** 14 new probes (six families plus eight verifier
  repairs); 920 Rust tests (20 held out with a stated reason).

### compiler-v0.14.0 — 2026-10-02

FMIR increments **F4** and **F6**, the lowering halves, produced by one
agent and independently verified by another. Implements `lang-v0.5.3`;
still no code generator.

- **`defer` / `errdefer` lowering (F4).** Lowering builds the FMIR scope
  tree and the defer pool from the checker's published D7 rows, emits
  each defer body once as its own sub-CFG, and records an exit edge on
  every static exit (block end, `return`, fall-through, `break`,
  `continue`, loop-body end, branch and arm ends). The textual cut of
  ch01 R23a is structural: one scope per `defer` statement, so a
  scope's pending bodies at an edge are exactly those whose statement
  precedes it, innermost first. The return operand is read before any
  body runs; a trap-terminated block has no edge; bodies nest.
- **By-reference arguments.** `f(&x)` and `f(&out x)` lower to the
  borrow instructions with the parameter-convention alias seed; scalar
  `inout`/`set` parameters are indirect roots read and written through
  `[Deref]`. The F1 `LowerError::Defer` refusal is gone.
- **Arenas and allocators (F6).** `with arena` / `with allocator` open a
  branded scope; the arena form is a region whose entry mints the one
  live arena value and whose exit retires it. D8 obligations are wired:
  a linear `let` opens a scope that owes its obligation and every exit
  edge discharges it as the checker published (moved, deferred,
  destructured or tail value); a corpus-wide test asserts no obligation
  is left undischarged on any edge.
- **Coverage.** 27 new lowering gate tests (F4's run-ok rows, trap runs
  no defer, arena-generation trap, aliasing and reset twins, the
  whole-corpus pending/discharge checks); 905 Rust tests (20 held out
  with a stated reason). Growth counter for design risk R6: the
  one-copy form adds 0.020× of body size over the corpus, against
  0.019× for inlining every body at every edge.
- **Verification found and fixed before merge.** `inc(&n); inc(&n);`
  left `n` unchanged — the callee read its own root slot while the
  caller passed a pointer (silent wrong result on accepted code);
  every function with a `set` parameter failed to lower because the
  lexer's contextual `set` was bound as the parameter name
  (pre-existing); a nested `defer` was refused; the corpus-wide pending
  assertion was tautological; a by-reference gate test asserted the
  wrong contract.
- **Held out, with the evidence.** `errdefer`-skipped-on-return and
  main-raises-after-defer need `else |e|` / `raise` propagation (F3,
  after I10's ch02 typing) and are pinned as named refusals; the
  use-after-free, allocator-mismatch and uninitialised-read twins stay
  fixture-driven with the reason beside each. Known: lowered
  instructions still carry site 0, so traps from source programs render
  at `0:0`; a `return`/`break` out of a `with arena` block emits no
  region exit on that path.

### compiler-v0.13.0 — 2026-10-02

FMIR increment **F-mono**, produced by one agent and independently
verified by another. Implements `lang-v0.5.3`; still no code generator.

- **Monomorphisation.** Every call whose `BodyFacts::generic_args` row is
  non-empty lowers to an instance of the callee at those arguments,
  lowered once per distinct `(callee, args)` and cached; generic free
  functions, methods and associated functions of generic impls, generic
  struct literals, trait methods through a bound (the impl selected on
  the determined `Self` and the trait's own arguments), fields of generic
  structs, const parameters read as values, and associated-type
  projections normalised at the instance. Instantiated types live in a
  lowering-owned clone of the checker's frozen type store; a gate test
  asserts the frozen store's digest is unchanged by lowering. An
  undetermined slot is a `LowerError`, never a default. With `std` in the
  build the lowering refusals fell from ~160 to the ~44 that are F3's
  `?`/`raise`.
- **Pattern lowering** from `BodyFacts::patterns`, never re-derived: enum
  arms by the discriminant `fors-layout` decides with payload projection,
  struct and tuple arms by field projection, literal arms (negatives
  narrowed, `Str` by bytes), bindings with the published copy-or-move,
  R54's source order, R53's exhaustiveness read and asserted;
  `let`/`var` destructurings; enum construction and tuple literals.
- **`Buffer.empty`** has a real body over the uninitialised-aggregate
  primitive; a read before write is `ub: uninit-read` with its site,
  never a silent zero.
- **Coverage.** 32 lowering gate tests for the above; 883 Rust tests
  (18 held out with a stated reason).
- **Verification found and fixed before merge.** Projections through a
  bound never normalised at an instance; impl selection ignored the
  trait's own arguments (`impl Conv[i64] for S` + `impl Conv[bool] for S`
  refused both); a name-only interception hijacked a user method; a
  trait method on a parameter-free impl was lowered twice under one name.
- **Held out, with the evidence.** `buffer-index-past-len-trap`: `Buffer`
  is a ch08 R17 prelude type name, so `Buffer.empty()`/`Buffer { .. }`
  are a silent checker `TY_ERROR` even with `std` (a checker defect for
  the next increment), and `IndexMut::at_mut` returns a place where FMIR
  calls produce values (a design question). Explicit generic arguments
  at a call site are not lowered yet.

### compiler-v0.12.0 — 2026-10-02

Type checker increment **I9**, `fors-query` and the M1 exit, produced by
one agent and independently verified by another. Implements
`lang-v0.5.3`; still no code generator.

- **The engine (`fors-query`).** `QueryKey`, `Revision`, input vs derived
  nodes with a value hash in SoA columns (no `Arc<dyn Any>`), dependency
  recording by read-tracking, red-green verification with early cutoff,
  an explicit in-flight stack with a caller-declared `on_cycle` value
  that is never memoised, cancellation that writes nothing, `compact`,
  `--stats`; `decl_fingerprint()` with the §14 Q4–Q6 fallbacks.
- **The query DAG.** Design §9.1's node set over the checker, with
  `check_body(k)` a real per-declaration node (`check_build` split into
  signatures + bodies, one code path), stable content keys per
  declaration, declaration-relative cached diagnostics re-rendered by a
  printing walk in canonical order, and `fors check --stats`. Coarse by
  design and stated so: whole-build resolve and signature phase (M2
  makes them per-module), `name_uses` as a slice of the whole-build
  resolve, `infinite_size()` the one whole-build query R14 asks for.
- **M1 exit gates.** (a) a 105k-line corpus checks clean cold through the
  DAG in ~0.3 s; (b) the counter gate — re-executions per edit class
  identical at 30/60/120 declarations — and a wall slope of ≈1.02 over
  13k→211k lines (release build, box load ≈4) against the ≤1.05 gate;
  (c) every §9.2 row as a set equality of re-executed queries,
  `adding_an_impl_invalidates_only_its_head_bucket`,
  `assoc_type_def_edit_is_signature_level`, cold-vs-incremental output
  byte-identical over an 8-edit script with a breaking edit and its
  revert, determinism under file and declaration permutation, and a
  deterministic oracle: 244 chapter-09 files, diagnostic for diagnostic,
  DAG vs `check_build`.
- **Three latent defects the oracle found.** An impl's key was derived
  from token positions, so an insertion above it changed its canonical
  `sig_hash` and every member's; impls with identical headers collapsed
  to one key and printed twice; a quadratic bucket scan made the cold
  slope super-linear.
- **Coverage.** 863 Rust tests (18 held out with a stated reason).
- **Verification found and fixed before merge.** Seven silent stale-output
  defects, each proved by a cold-vs-incremental test that failed before
  the repair: `impls_for` with no edge to its rows' signatures;
  cross-module empty buckets never woken (ch08 R21); `impl_holds`
  recording no bucket on its exact path; `signature_of(impl)` with no
  edge to its trait; whole-head diagnostics cached without bucket edges;
  R14 cached on the wrong node; prelude impl rows keyed by a renumbering
  `DefId`. Also a panic on file removal and two sources of
  nondeterminism across processes.
- **Flagged, not changed.** A `const`'s comptime value is in no
  fingerprint yet (Q4 implemented, not wired); a qualified path spelling
  is over-hashed; design §9.1's `impls_for` row understates its reads.

### compiler-v0.11.0 — 2026-10-02

Type checker increment **I10a**, the facts lowering was missing, produced
by one agent and independently verified by another. Implements
`lang-v0.5.3`; still no code generator.

- **Determined generic arguments.** `BodyFacts::generic_args` records, for
  every call the checker resolves to a generic callee and every generic
  struct literal, the arguments R38(a)–(f) determined, normalised through
  R20, in R38(a)'s order; one column covers type, brand and const
  arguments; a monomorphic callee records an empty row, an undetermined
  slot `NO_TY`.
- **Pattern facts.** `BodyFacts::patterns` publishes what the checker
  already decided: per pattern node its shape (wild, binding with its
  copy-or-move convention, literal, variant, struct in field order,
  tuple), the faced type and parent component; per `match` the arm order
  and R53's exhaustiveness; `let`/`var` destructurings as one-arm matches.
- **A silent `TY_ERROR` fixed.** R45's qualified form on a generic head
  (`Buffer.empty()`, the commonest `std` constructor shape) resolved to
  nothing with no diagnostic; the head is applied to its own parameters
  and the impl's parameters enter the binding, so R38(c) determines them
  from the expected type and R39 speaks where nothing does. `std`'s own
  `return Buffer.empty();` types for the first time.
- **Coverage.** 803 Rust tests; PENDING_09 unchanged at 6.
- **Verification found and fixed before merge.** A second silent shape:
  R38(a) explicit arguments on the function segment of a qualified call
  to a non-generic head (`Layout.of[T]()`).
- **Listed for the next increment.** A sweep of `std` found 17 more silent
  `TY_ERROR` nodes in three pre-existing families (parameterised-trait
  methods, explicit type arguments on a type path used as a value head,
  `[ ]` on a scoped slice through an `inout` receiver) — I10b adds a
  permanent sweep gate and fixes them at the root.

### compiler-v0.10.0 — 2026-10-02

FMIR increment **F1-completion**, produced by one agent and independently
verified by another. Implements `lang-v0.5.3`; still no code generator.

- **Loops.** `for` over ranges, arrays and slices, `while`, `break` and
  `continue`, with loop-carried values in frame-local slots and the
  induction advance in the latch block, so `continue` advances exactly
  once and nested loops keep their own advance.
- **Scalar index.** Reads on arrays and slices (`Op::Index`) and through a
  resolved non-generic `Index::at` (F7's `IndexImpl` fact, now read);
  bounds-trapping writes including the two-segment `self.data[i]` place;
  slice bases that are a field projection; ch10 R42's `len`.
- **Scalar `match`** through `switch_discr` with literal and wildcard arms.
- **ch03 R4 and R6.** Explicit arithmetic (`wrap_`/`sat_`/`unchecked_` over
  add, sub, mul, div, rem, shl, shr, neg) and the three lossy conversions
  (`wrap_as`/`sat_as`/`trunc_as`), intercepted only for calls the checker
  resolved no callee for (the family's typing is I10's); `unchecked_*` is
  refused outside an `@unsafe(invariant:)` declaration.
- **`@fastmath(flags)` blocks** carry the Relax mask on every float
  instruction and restore it at the brace; the interpreter computes strict
  throughout (design E7).
- **Coverage.** 18 of F1's 19 gate tests wired and green (the 19th fails at
  resolve: `comptime_int` is unknown to every crate — I10 and F9); F2's 8,
  F5's 8 and F7's `str-index-is-bytes` unchanged; 35 new lowering gate
  tests; 797 Rust tests.
- **Not landed, with the evidence.** Generic monomorphisation (the checker
  records no call-site type arguments, and the FIR is frozen during
  lowering — two decisions for the next checker increment); enum and
  struct `match` (I7's pattern facts are not published); `Buffer.empty`'s
  uninitialised-aggregate primitive.
- **Verification found and fixed before merge.** The claimed
  `self.data[i] = v` shape panicked the compiler (a `NO_TY` index);
  an assignment `total = total.wrap_add(..)` retyped the local;
  `wrap_as`/`trunc_as` zero-extended a negative source; `sat_shl` wrapped
  instead of clamping; `unchecked_add` ran outside `@unsafe`;
  `0.1f64 as f32` did not trap although ch03 R6 requires exact
  representability (pre-existing F1 code); `verify.rs` never saw a secret
  `switch_discr` scrutinee.
- **Documented limitations.** A ch03 R4/R6 call inside a compound
  expression is refused (`CheckErrors`) until I10 types the family; a
  by-reference free-function argument and a three-segment projection are
  `Unsupported`. `wrap_shl`/`sat_shl` at `count >= width` still trap
  (design §11.1 Q4) — an owner call against ch03 R3's wording.

### compiler-v0.9.0 — 2026-10-02

Type checker increment **I8b**, the round-6 flow, produced by one agent and
independently verified by another, then checked against `std` under its
own rules on the branch. Implements `lang-v0.5.3`; still no code generator.

- **Linear obligations (ch01 R22–R22i).** `lin(T)` lives in `fors-fir`
  (`ty::lin`, `droppable`, `open_leaves`, `lin_components`): a memoised
  structural descent over a normalised type with its arguments
  substituted, true at a head with an `impl Linear` or `Own`, at any
  component, and at a rigid parameter or neutral projection that is not
  `Droppable`; it never enters `Own`/`Ref`/`Arena`/`Slice`/`Range`/mask.
  The flow pass owes each linear binding at its scope and settles it at
  every static exit (block end, `return`, `raise`, the error edge of `?`,
  `break`, `continue`) by R22d's discharge set — a whole-place move,
  destructuring that binds every linear component, or a deferred body —
  and reports R22i's five-field message (name or "the result of `f()` at
  L:C", the type as R20 shows it, the exit, its location, the consumers
  computed from the head's defining module).
- **`defer`/`errdefer` regions (R23–R23f)** and R19d's closure source sets.
- **D7/D8/D9 for lowering.** `BodyFacts` publishes `defer_regions`,
  `linear_obligations` (one `Discharge` per owed obligation per exit edge,
  decided from the reaching path) and `scoped_sources`; D7 is
  cross-checked against `fors_fmir::exit::expected_pending` over eight
  corpus files, and `ExitEdge` documents the R23a textual cut lowering
  must reproduce.
- **`std` under the new rules.** The five container releases
  (`Vec.deinit`/`deinit_empty`, `String.deinit`, `Map.deinit`/
  `deinit_empty`) have real bodies that destructure `self` and free the
  block; `Option.unwrap_or` moved to a `T: Droppable` block (`lang-v0.5.3`);
  the five allocator `free` stubs are documented stand-ins until the
  deallocation primitive exists. **Two diagnostics stay, listed and
  visible:** `Vec.push` and `Map.insert` lose the sunk value on their
  allocation-failure exit, which R22c forbids for a rigid `T` — the
  declared signatures (ch10 S0024/S0025) are unimplementable for a linear
  `T` and wait for the owner.
- **Coverage.** 240 of chapter 09's 246 conformance tests on, 6 pending
  (one owner decision on R38(c) in CHECK position; five `adaptor-*` files
  whose `Iterator.map`/`take` live only in `std`, mechanisms proved by
  local-trait probes); `PENDING_SPEAKS` is empty; 732 Rust tests.
- **Verification found and fixed before merge.** From a 71-program
  mutation set: a linear binding born inside an outer `let`'s initialiser
  (an arm binding, a closure-body local) was never checked at its own
  scope's exit; a linear temporary in a non-consuming call position was
  dropped silently (R22h); `sink self` was exempt even when `self` has a
  linear component; D8's discharges were path-insensitive; D7's
  `stmt_order` was a node index.
- **Readings recorded, not changed.** R23b is read as "a visible
  error-exit context and the `errdefer` body consumes something" (three
  corpus files contradict its letter); R22c's rigid clause applies at
  depth 0 only, forced by a chapter-09 `check-ok` file.

### compiler-v0.8.0 — 2026-10-02

FMIR increment **F7** in part, `std` in Fors, produced by one agent and
independently verified by another, then checked under I8's flow pass on
the branch. Implements `lang-v0.5.2`; still no code generator.

- **`Str` has real bodies** (`len`, `at`, `is_boundary`, `slice`, `eq`,
  `starts_with`, `find`, `from_utf8` with the overlong, surrogate and range
  checks) over three interpreter intrinsics scoped to the prelude `Str`
  impl; a string literal's `\xHH` escapes are validated as UTF-8 in
  lowering (ch10 R26).
- **`MemberTarget::IndexImpl`.** `BodyFacts` records which `Index`/`IndexMut`
  impl an `a[i]` on a user type resolved to — the fact `fors-lower` needs
  for `Buffer` and `Vec`.
- **`std` checks clean the way a consumer builds it** (`std`-prefixed
  module names, real cross-module resolution), pinned by `std_checks_clean`;
  the cross-chapter conflict list for `std` is empty. `fors check std`, the
  CLI's package-`std` mode, is a false negative for cross-submodule
  resolution and is not that gate.
- **Four latent bugs fixed.** `fors-resolve` rejected a real item under one
  of ch10 R2's eight prelude names even inside package `std`, poisoning
  every cross-submodule `std` import; `is_trait_impl` took a `for` loop in a
  method body for an `impl … for`; `lower::trait_ref` lowered a brand
  argument of a trait application as a type, so every `impl[A: brand]
  alloc.Allocator[A] for …` in `std` was ch01 R15d's O0015 the moment the
  flow pass saw it; and `std`'s two partial moves are gone
  (`Buffer.into_iter` in the destructuring form ch01 R22d(ii) prescribes;
  `BufferIter.take_at` a documented stand-in, since `move self.data[i]` is
  the partial move R4a(c) forbids).
- **Scope, stated plainly.** 1 of F7's 6 gate tests runs end to end
  (`str-index-is-bytes-run-ok`); five are held out with their reason:
  `fors-lower` lowers no loop, no generic call, no scalar index, no handler
  or `try`, and `Buffer.empty` needs an uninitialised-aggregate primitive.
  Those are F1-era gaps and the next FMIR increment.
- **Coverage.** 706 Rust tests (14 held out with a stated reason).
- **Verification found and fixed before merge.** A name-only intrinsic
  interception hijacked any user method spelled `str_byte_len`; `Str.slice`
  bottomed out in a self-recursive stand-in; two `trap.rs` tests raced on
  the process-global `FORS_BACKTRACE`.

### compiler-v0.7.0 — 2026-10-02

Type checker increment **I8**, the flow pass, produced by one agent and
independently verified by another. Implements `lang-v0.5.2`; still no code
generator.

- **The flow pass (ch01 R2, R3, R4a, R8; ch09 R46).** One forward walk over
  each body's use tape: a move out of a `let` parameter, use after move in
  all five R4a shapes, and R8's two-valued merge at `if`/`match` joins, loop
  heads and loop exits — one dead-set, no third state, no drop flag, no
  second analysis. R46's normative sentence names the consuming call and
  its `sink self` declaration for both the implicit and the explicit form.
  Convention markers (`&x`, `move x`, `&out x`) are checked at the call.
- **Coverage.** 232 of chapter 09's 246 conformance tests on, 14 pending
  (all I8b); every pre-round-6 chapter-09 file is decided; 690 Rust tests.
- **Verification found and fixed before merge.** The first cut forgot a
  move made inside a branch at the join, so a use after a one-branch move
  — and the corpus's own `merge-liveness-disagreement-rejected` — were
  accepted; the pass was rewritten. Three latent tape defects surfaced
  once something read the tape (`Slice[T]` is Copyable; discarding a
  Copyable is a copy; a variant construction carries no conventions).
- **Documented limitation.** `while true { …; break; }` reports R8 at the
  loop exit because the pass does not sniff a literal `true` condition.

### compiler-v0.6.0 — 2026-10-02

Type checker increment **I7**, patterns and exhaustiveness, produced by one
agent and independently verified by another. Implements `lang-v0.5.2`;
still no code generator.

- **Patterns (ch09 R50–R52).** Bindings, literals, wildcards, tuples,
  struct patterns with omitted fields, enum variant payloads, nested
  patterns, `some`/`none`, typed against the scrutinee with one diagnostic
  at the position ch03 R25 fixes.
- **Exhaustiveness (R53–R55).** The standard usefulness algorithm with no
  early exit; witnesses for missing constructors; unreachable arms; the
  R55 step budget, whose count an independent reference reproduces exactly
  on both corpus files. An oracle enumerates every value of 10 000 seeded
  nested scrutinee types and agrees with the algorithm on exhaustiveness,
  per-arm reachability and the diagnostic's line.
- A nested explicit generic argument (`id[Option[i64]](true)`) is now
  checked; it used to be accepted silently.
- **Coverage.** 223 of chapter 09's 246 conformance tests on, 23 pending
  (I8 and I8b); 680 Rust tests.
- **Verification found and fixed before merge.** A `const` pattern of a
  `Str` or a negative integer lowered to a wildcard, so `match s { S => 1 }`
  passed as exhaustive; an unknown, duplicated or private field in a struct
  pattern was silent; witnesses could name a covered string.
- **Open for the owner.** R55's prose admits two step counts
  (`match-budget-within-accepted` says "about 4 000", the no-early-exit
  reading gives 6150); the count is normative across implementations.

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
