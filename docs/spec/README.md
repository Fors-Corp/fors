# Fors specification (M0.5 draft)

Authority order: `docs/PLAN.md` §4.2/§4.3 > these chapters > `docs/design/*`.

**Citation rule.** Every fact below is defined in exactly one chapter. Any
other document (chapter, design doc, comment, test) MAY only cite it
(`ch03 Rule 11`), never restate or redefine it.

## Chapters

1. `01-ownership.md` — conventions, exclusivity, qualifiers, the `brand` kind, arenas/allocators, scoped return
2. `02-failure.md` — `raises`/`raise`/`?`, failure ABI, traps, contracts, check removal
3. `03-numerics-determinism.md` — integers, floats, D1, `reduce` (blocks and lanes), generics lowering
4. `04-authority.md` — capabilities, sealed capabilities, `needs` vs manifest, comptime, build graph
5. `05-ir-contract.md` — IR levels, alias classes, secret/CT, tiles, differential agreement
6. `06-measurement.md` — benchmark tiers and metrics
7. `07-grammar.md` — lexical grammar, keywords (reserved and contextual), operator table, complete EBNF, disambiguation rules (LL(2)), error-recovery synchronisation set. Present; verified 2026-09-19 against every example in ch01-05 (ch06 has none); round-5 owner decisions applied (receiver shorthand, `spmd`/`kernel` reserved, `;`/bitwise confirmed).
8. `08-names.md` — file-to-module mapping, `use`/`pub use`, module graph edges and acyclicity, visibility, module scope, lookup, no-shadowing, path and pattern resolution, prelude, orphan rule, resolver/checker boundary. Draft, verified 2026-09-19; round-5 owner decisions applied (std modules need `use std.<m>;`); decidable from syntax plus the set of module names.
9. `09-types.md` — type universe and equality, the closed coercion list, well-formedness, traits and impls with associated types, overlap, the closed operator-trait table, `Copyable`, the two typing judgements per form, generic-argument determination, member lookup and receivers, pattern typing and exhaustiveness, generic bodies, the signature-only interface. Draft, 2026-09-19; round-4 owner decisions applied.
10. `10-std.md` — the standard-library SURFACE (signatures and guarantees, never implementations): the closed module and prelude lists, the allocator interface and the concrete allocators, the core types (`Buffer`, `Vec`, `Map`, `String`, `Str`, `Slice`), iteration, the operations each capability module unlocks with their failure behaviour, concurrency and determinism, and the rules std itself obeys. Draft, 2026-09-20; implements round 5's D5 (explicit allocators, root heap at `main`, allocation is not authority) and closes the type half of ch08 Q1.

## Fact -> owning chapter

| Fact | Owner |
|---|---|
| Qualifier set (`iso`, `imm`; `secret` orthogonal), sendability | ch01 R10-14 |
| `brand` kind, fresh brands (`with arena` / `with allocator`), brand parameters, brand erasure | ch01 R15-15e, R16, R18 |
| Call-site markers (`&x`, `move x`, `&out x`), `scoped(p)` | ch01 R2, R19-19b |
| Failure ABI, trap = whole-process abort | ch02 R4, R6-7 |
| Reduction tree, `REDUCE_BLOCK` = 256, `REDUCE_LANES` = 8, tail rules | ch03 R11-13 |
| Comptime engine (one: FMIR interpreter) | ch04 R11-15 |
| Capability declaration sites (`needs` ⊆ manifest policy) | ch04 R1-3 |
| Sealed capabilities (`syscall`, `asm`, `ffi`), permitted holder packages, `ffi` taint | ch04 R2-2b, R9, R17-18 |
| Tokens, literals, comments, maximal-munch rules (`&out` is two tokens, `1..<2`, `\\` strings) | ch07 Lexical grammar |
| Reserved and contextual keyword sets, each contextual slot and its lookahead | ch07 Keywords |
| Operator precedence table; flat bitwise tier (`cmp_expr`/`bit_expr`) | ch07 Operator table |
| Every syntax production; header order `module`, `contracts:`, `needs`, `inputs`, `use` | ch07 Grammar |
| Inline-`asm` grammar (`asm_expr`/`asm_item`, at least one string = parse error), `asm` reserved but legal as a `needs_item`, `out`/`clobber` contextual slots | ch07 Grammar |
| Struct-literal-free heads (`expr_ns`), `\|`/`&`/`[` roles, statement start, generic-argument type-vs-expression rule, lookahead bound (2 tokens) | ch07 Disambiguation 1-18 |
| Receiver shorthand (`convention "self"` = `self: Self`), legal only in a `trait`/`impl` body, one-token lookahead, fixed diagnostic | ch07 Grammar, Disambiguation 21 |
| `fors fmt`: one canonical style, 4-space indent, 100-column target | ch07 Drafting decisions (round 5, D5) |
| Explicit allocator values, no ambient allocation, root heap as a `main` parameter, allocation is not authority | ch01 (round 5, D5), ch04 R21 |
| Syntax of associated types (`type A: B;`, `type A = T;`), constraint entries in `generics` (`I.Item: Add`) and their `.`-versus-`:` lookahead; `type` reserved | ch07 Grammar, Disambiguation 19-20 |
| Parser synchronisation sets (missing `;` / `}`) | ch07 Error recovery |
| Benchmark tiers, metric definitions | ch06 |
| IR home of tiles, secrets, alias-class sources | ch05 R5-6b, R12 |
| Secret propagation and CT rejection rules | ch05 R6a-6b, R15 |
| `FAILURE_TAG_REG` (x9), `FAILURE_INLINE_MAX` (24) | ch02 R4 |
| `MONOMORPHIZE_SIZE_MAX` (16), `MONOMORPHIZE_INSTR_THRESHOLD` (unset) | ch03 R16 |
| `COMPTIME_STEP_BUDGET`, `COMPTIME_ALLOC_BUDGET` (unset) | ch04 R14 |
| `@unsafe(invariant:)` form | ch04 R10 |
| Check deletion, contract policy | ch02 R10-12 |
| Std module list (the ten), prelude additions (the eight), std's naming and convention conventions | ch10 R1-5 |
| Failure discipline of std (total / one `raises` type / `Option`); allocation failure is an error value | ch10 R6-7, R6d |
| Allocator interface (`Allocator[A]`, `Layout`, `Block[A]`), alignment, zeroing, reallocation, freeing | ch10 R12-16 |
| Concrete allocators: `mem.Heap` (root heap, no capability), `PageAllocator`, `mem.Bump`, `mem.Fixed[N]`, `mem.Counting[N]` | ch10 R17-21 |
| Linearity (a linear value MUST be consumed); `Own[T, A]`'s surface | ch10 R11, R22 |
| Core types: `Buffer[T, N]`, `Vec[T, A]`, `Map[K, V, A]`, `String[A]`, `Str`, slice primitives | ch10 R23-28 |
| Iterator surface: the three yield forms, the closed adaptor and consumer sets, `try_*` | ch10 R32-37 |
| Per-module operations, their `needs` and their failure behaviour (io fs net proc time rand env gpu ffi) | ch10 R38-49 |
| What std adds to concurrency; which std types are `Shared`; no locks/channels in v0.1 | ch10 R50-52 |
| The rules std itself obeys; std's sealed `syscall`/`ffi` holders; v0.1 stability; "not in v0.1" | ch10 R9-10, R53-57 |
| Root-capability types (closed list of twelve, type -> capability pairing; `mem.Heap` pairs with none), opacity, `main`-param rules (the type's head judged by what the header binds it to — `use std.io;` or an alias — never by spelling, so a user module named `io` cannot forge one), no `World` value | ch04 R7-8, R21 |
| Inline-`asm` authority (sealed `asm`/`syscall`, architecture, register, secret-input rules) | ch04 R22-26 (sealed-operation bans: R2a) |
| Inline-`asm` value and type (CHECK mode only; statement form checks against `()`) | ch04 R27 |
| Inline-`asm` opaque-region IR contract, `unknown` alias class, CT inventory entry, secret taint of `out`/`clobber` registers | ch05 R19-20a |
| `Shared` marker trait, field-wise check (enum payloads, generic fields need `P: Shared`, no blanket impl), unsafe escape hatch, atomics vs `imm`/sendability | ch01 R21-21d |
| Array-literal typing, `[x; n]`, `.splat`, `Slice[T]` by range-index | ch03 R21-24a |
| CHECK/SYNTH mode positions (the two typing judgements) | ch03 R25 |
| Trap-kind identifier set (closed); `nesting-limit` is not a trap | ch02 R15 |
| Comptime file-read declaration (`inputs { ... };` header clause) | ch04 R13 |
| File-to-module mapping, optional `module` header must match, legal (lowercase) file names, case-insensitive file systems | ch08 R1, R24 |
| What a `use` path binds (module or `pub` item, never a member), optional `"as" ident` alias (binds the alias only), `pub use` re-export, imports not transitive | ch08 R3-6 |
| Module-graph edge set (EXACTLY the explicit `use` edges; no implicit edge, no body scan), acyclicity, cycle diagnostic (capability flow along edges stays ch04 R2-2a) | ch08 R7-8 |
| Order-independent module scope; order-dependent bindings; scope of every binding form; implicit `Self` | ch08 R9, R19, R26 |
| Visibility: `pub` items, fields, variants, inherent and trait-impl methods; private item in a public signature | ch08 R10-12 |
| One namespace per module scope; item/import/prelude collisions are eager errors | ch08 R13, R15 |
| Lookup, segment-by-segment path resolution, deferred (type-directed) segments | ch08 R14, R16 |
| Prelude: closed list of types and traits (operator traits, `Eq Ord Copyable never Iterator Index IndexMut Range RangeIncl` included) and values (`some none reduce`); NO modules | ch08 R17 |
| Std modules require an import (`use std.io;`); the synthetic `std` table (`io fs net proc time rand env gpu mem ffi`) until `std` ships, member accesses deferred, unknown module = N0017 | ch08 R17 |
| No shadowing (total, except a function-local binding may shadow a prelude name; generic parameters excepted from the exception); pairwise-distinct bindings | ch08 R18 |
| `scoped(p)` names a parameter only | ch08 R20 (semantics: ch01 R19) |
| Orphan rule; impls are not names | ch08 R21 |
| Resolver/checker boundary: what needs a type; identifiers that are not names | ch08 R22-23 |
| Binding versus reference in patterns (`"let" ident` binds; a bare one-segment name is always a reference) | ch08 R25 |
| Member tables (fields, variants, methods, associated types) and their duplicate rule | ch08 R27 |
| Scope of a constraint entry's head (an earlier parameter of the list, an enclosing `impl`/`trait` parameter, or `Self`) | ch08 R26 |
| Single-pass discipline (no solver, no surviving variable); signatures — associated-type definitions included — as the only inter-declaration interface | ch09 R1-2 |
| Type universe, primitive sizes, `never`, nominal types, `fn`/closure/`dyn` types, type equality (after normalisation), the closed coercion list | ch09 R3-10 |
| Well-formedness: arity and kinds, bounds hold at every use (impl lookup), const parameters, infinite-size test, `gparam` classification | ch09 R11-15 |
| Traits and impls: methods and associated types, impl completeness, unconstrained impl parameter, no projections in impl heads, overlap | ch09 R16-19 |
| Normalisation of projections, neutral projections, its termination argument | ch09 R20 |
| Closed operator-trait table (homogeneous), `Iterator`/`Index`/`IndexMut` declarations, non-overloadable forms and built-in impls, `Copyable`, marker traits, dyn-capability | ch09 R21-25 |
| `synth`/`check` for every expression, statement and literal form; integer literal default `i32` | ch09 R26-37 |
| Generic-argument determination (one-way matching, projections never bind, final check), callable parameters | ch09 R38-41 |
| Member lookup, qualified forms, receivers (no marker; implicit move for `sink self` and its required diagnostic), Bracket reading, member clashes | ch09 R42-49 (move legality: ch01 R2) |
| Pattern typing, exhaustiveness and unreachable arms, `MATCH_STEP_FACTOR` (256) | ch09 R50-56 |
| What a generic body may do with a rigid type; no instantiation-dependent error; generic `raises` | ch09 R57-60 |
| Projection well-formedness (`P.A`, `Self.A`; ambiguity; no concrete head); constraint entries (only on `fn` generics) | ch09 R61-62 |

## Closed by owner decision 2026-09-19

D1 brand abstraction (ch01 R15-15e), D2 sealed capabilities (ch04 R2-2b),
D3 `reduce` lane shape (ch03 R11, R13), D4 `raise expr;`, `scoped(p)`,
structured-`spawn` capture extent (ch02 R1, ch01 R19, R13).

## Closed by owner decision 2026-09-19, round 2

R2-1 authority enters only through `main`'s parameters, no `World` value,
closed root-capability type list (ch04 R7-8, R21); R2-2 `Shared` as a
checked marker trait (ch01 R21-21d); R2-3 array-literal typing, `.splat`,
`Slice[T]` by range-index (ch03 R21-25); R2-4 inline assembly from v0.1
(ch07 grammar; ch04 R22-27 authority and typing; ch05 R19-20a IR contract). Also:
trap-kind identifiers enumerated (ch02 R15); comptime budget constants
named, values still unset (ch04 R14); comptime file reads declared via an
`inputs { ... };` header clause (ch04 R13, ch07 grammar).

## Closed by owner decision 2026-09-19, round 3

D1 pattern bindings: a pattern binds a name only via `"let" ident` (ch07
grammar: `pattern`/`fpat` gain `"let" ident`; the bare `fpat` shorthand
is removed, a parse error); a bare one-segment pattern name is always a
reference (ch08 R25, N0025/N0014). `"var" ident` is not a pattern form
(mutable pattern bindings stay open, recommendation "no"). D2 import
aliases: `use p as c;` / `pub use p as c;` (ch07 grammar `use_item`; ch08
R3-6) bind `c` only, not any earlier segment; participate in R13/R15
collisions; `"as" "_"` is a parse error (`_` is not an `ident`) and
aliasing to a prelude name is an R13 error. D3
prelude shadowing: a function-local binding (not a generic parameter, not
an item or import) may shadow a prelude name (ch08 R18); the implicit
prelude-module edge scan (ch08 R17) may over-approximate harmlessly when
a local shadows a prelude module. Consequence recorded in ch08 R26:
parameters come into scope left to right, so a parameter's own type
annotation (and earlier ones) never see it.

## Closed by owner decision 2026-09-19, round 4

Type system (ch09). Owner: T1 unsuffixed integer literals default to `i32`
(ch09 R27; ch03's indexing example now writes `1usize ..< 8`, indexing
stays `usize`-only); T2 operator traits are homogeneous in v0.1, `Add` has
no `Output` (ch09 R21); T3 full associated types in v0.1 — `type A: B;` in
traits, `type A = T;` in impls, projections `P.A` / `Self.A`, constraint
entries `[I: Iterator, I.Item: Add]`, `type` reserved (ch07 grammar and
Disambiguation 19-20; ch08 R16, R22, R26, R27; ch09 R16-20, R38, R61-62),
replacing the draft's self-determined traits and bound propagation;
`Iterator { type Item; }`, `Index[I] { type Output; }`; T4 a `sink self`
receiver moves its place implicitly, `x.finish()`, with a mandatory
diagnostic detail (ch09 R46; ch01 R2's single exception). Drafting
defaults taken with them: the prelude gains the operator traits, `Eq Ord
Copyable never Iterator Index IndexMut Range RangeIncl` (ch08 R17; settles
`Copyable` of ch08 Q1); a variant and an associated function of one name
is an error (ch09 R48; closes ch08 Q5); `MATCH_STEP_FACTOR` = 256 until
measured (ch09 R55).

## Closed by owner decision 2026-09-19, round 5

D1 receiver shorthand: `param` gains `convention "self"`, meaning
`self: Self`; legal only for the identifier `self` and only inside a
`trait_item`/`impl_item`, decided on one token of lookahead, with a fixed
diagnostic for every other missing annotation (ch07 grammar and
Disambiguation 21; ch09 R16). D2 `spmd` and `kernel` are RESERVED from
v0.1, used by no production (ch07 reserved list and reserved-unused
table; ch08 R23-24 consequences; closes ch07 Q3). D3 std modules require
an import: the prelude keeps only types, values and traits and NO
modules, the module graph is exactly the explicit `use` edges (no
implicit edge, no body scan), using a std module without importing it is
N0014, and `std` is a known package whose module names live in a
synthetic table (`io fs net proc time rand env gpu mem ffi`) until
`std` ships, with `use std.<unknown>;` an N0017 error (ch08 R7, R14, R16, R17,
R18, R23; ch04 R21's import note; closes the module half of ch08 Q1).
D4 confirmations, each closing an open question as drafted: mandatory
`;` and no ASI, and the flat bitwise tier (ch07 Q1); the reserved set
plus D2's two words, `set` contextual (ch07 Q2); trap = whole-process
abort, no unwinder, nothing catchable, no reserved domain-recovery
boundary, expected errors travel as values (ch02 Q1, R7); overlapping
`let`/`let` accepted, so no-alias facts never come from a `let`
parameter (ch01 Q1, R7); the self-referential arena header
`with arena nodes: Arena[Node[nodes]]` kept (ch01 Q3). D5 recorded for
the next milestone, not designed: heap-allocating std types take an
explicit allocator value, branded per PLAN R2, with no default global
allocator and no ambient allocation, the root heap arriving as a `main`
parameter and carrying no `needs` entry (ch01 round-5 section, ch04
R21); `fors fmt` has one canonical style, 4-space indent, 100-column
target (ch07, chosen over ch06 because ch06 owns measurement only).
**D5 is now DESIGNED, in ch10** (2026-09-20): the allocator interface is
ch10 R12, the root heap is `mem.Heap` (ch10 R17; ch04 R21's list, no
capability, its `main` binding naming a fresh brand), and ch10's open
questions 1-2 name the three one-clause edits the frozen chapters still
need — ch01's second origin for an allocator value, ch01's linearity
rule, and ch03 R24's exception for ch10 R28's `@unsafe` slice primitives.

## Open owner questions (most blocking first)

1. ~~Syntax calls of PLAN §4.3(3) (ch07 Q1-3).~~ CLOSED by owner
   decision 2026-09-19, round 5 (D4, D2): mandatory `;` and no ASI, the
   flat bitwise tier, the reserved set as drafted plus `spmd`/`kernel`
   reserved-unused, `set` contextual. `fors-lex`/`fors-parse` are
   unblocked.
2. Header and keyword leftovers: `contracts:` placement (ch02 Q3, encoded
   in ch07 `file`); `recover` reserved-unused vs dropped (ch01 Q2).
   One-line grammar changes, but they touch every module header.
3. ch08 calls needed before the name resolver is frozen: ~~prelude
   contents — `Buffer`, `Vec`, `PageAllocator` used unqualified but
   defined nowhere~~ CLOSED by ch10 R2 (2026-09-20): all three enter the
   prelude with `Allocator AllocError Map String Utf8Error`, eight names
   from `std.mem`; the module half of that question is CLOSED by round 5's D3 (mandatory `use std.io;`, no
   prelude modules, a synthetic `std` table until `std` ships). The
   manifest must still define package name and source root (ch08 Q3).
   (ch08 Q2, no-shadowing, closed round 3 above.)
4. ~~Self-referential brand in the `with` header, `Arena[Node[nodes]]`
   (ch01 Q3).~~ CLOSED by owner decision 2026-09-19, round 5 (D4): kept
   as drafted; ch08 R19 scopes the name over the header accordingly.
5. ~~Confirm trap = whole-process abort (ch02 Q1).~~ CLOSED by owner
   decision 2026-09-19, round 5 (D4): confirmed plainly (ch02 R7); no
   unwinder, nothing catchable, no reserved recovery boundary.
6. ~~Overlapping `let`/`let` default (ch01 Q1).~~ CLOSED by owner
   decision 2026-09-19, round 5 (D4): accepted (ch01 R7); a `let`
   parameter yields no no-alias fact.
7. `FAILURE_*` defaults; float return class (ch02 Q2, Q4). Blocks `fors-abi`.
8. Deliberately absent syntax: char literals, labelled `break`, match
   guards, tuple index fields, type aliases (ch07 Q4). Blocks nothing
   until std needs one.
9. `REDUCE_BLOCK`/`REDUCE_LANES` overridability (ch03 Q2).
10. `@declassify` gate; secret in `@device`; CT denylist (ch05 Q1-3).
11. Tunables: `MONOMORPHIZE_INSTR_THRESHOLD`, comptime budgets (ch03 Q1, ch04 Q1).
12. Security-release signer; `dyn.load` (ch04 Q2-3).
13. Round-2 verifier decisions to confirm (2026-09-19): statement-form
    `asm` checks against `()` rather than being a SYNTH error (ch04 R27);
    `env.Args` pairs with capability `env`, `fs.Dir` with `fs.read` or
    `fs.write` (ch04 R21); the CHECK-position list (ch03 R25), in
    particular that an argument to a generic-typed parameter is SYNTH;
    whether `main` may be called by user code. Blocks nothing: the
    checker can start on the drafted answers.
14. Measurement: Tier A additions, Tier B order, canary `N`, FLOP calibration, blocked `matmul` (ch06 Q1-5).
15. Globs and package-level visibility still open (ch08 Q4; aliases
    closed round 3 above — two modules with the same last segment can
    now both be imported, under different aliases). (ch08 Q5, variant
    versus associated function, closed round 4 above.) Blocks nothing yet.
16. Mutable pattern bindings (`"var" ident` in a pattern): round 3's D1
    recommends "no" but leaves it open (ch08 Q6).
17. ch09 leftovers of round 4, none blocking the checker: a qualified
    projection `(P as Tr).A` for ambiguous projections, and a spelling for
    nested ones (ch09 Q2, Q7; needs a ch07 production, so best decided
    before the grammar freeze); projections headed by a concrete type
    (Q3); constraint entries beyond `fn` generics (Q4, a drafting
    restriction that protects impl-lookup termination); associated consts
    (Q5); `IndexMut`'s language-known `Index` prerequisite versus general
    supertraits (Q6); the remaining v0.1 restrictions (Q1); the
    verification round's two containments — a bounded impl parameter must
    occur in the self type (ch09 R18) and the infinite-size test's
    associated-type node (ch09 R14) — and ch01 Rule 4a's three
    conservative move bans (partial moves, moves out of `inout`, moving
    closure captures), ch09 Q8 and ch01 Q4.
