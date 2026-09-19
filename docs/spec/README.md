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
7. `07-grammar.md` — lexical grammar, keywords (reserved and contextual), operator table, complete EBNF, disambiguation rules (LL(2)), error-recovery synchronisation set. Present; verified 2026-09-19 against every example in ch01-05 (ch06 has none).

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
| Every syntax production; header order `module`, `contracts:`, `needs`, `use` | ch07 Grammar |
| Struct-literal-free heads (`expr_ns`), `\|`/`&`/`[` roles, statement start, generic-argument type-vs-expression rule, lookahead bound (2 tokens) | ch07 Disambiguation 1-15 |
| Parser synchronisation sets (missing `;` / `}`) | ch07 Error recovery |
| Benchmark tiers, metric definitions | ch06 |
| IR home of tiles, secrets, alias-class sources | ch05 R5-6b, R12 |
| Secret propagation and CT rejection rules | ch05 R6a-6b, R15 |
| `FAILURE_TAG_REG` (x9), `FAILURE_INLINE_MAX` (24) | ch02 R4 |
| `MONOMORPHIZE_SIZE_MAX` (16), `MONOMORPHIZE_INSTR_THRESHOLD` (unset) | ch03 R16 |
| `COMPTIME_STEP_BUDGET`, `COMPTIME_ALLOC_BUDGET` (unset) | ch04 R14 |
| `@unsafe(invariant:)` form | ch04 R10 |
| Check deletion, contract policy | ch02 R10-12 |

## Closed by owner decision 2026-09-19

D1 brand abstraction (ch01 R15-15e), D2 sealed capabilities (ch04 R2-2b),
D3 `reduce` lane shape (ch03 R11, R13), D4 `raise expr;`, `scoped(p)`,
structured-`spawn` capture extent (ch02 R1, ch01 R19, R13).

## Open owner questions (most blocking first)

1. Syntax calls of PLAN §4.3(3), drafted in ch07 and needed before the
   lexer/parser freeze: mandatory `;`; flat bitwise tier; the reserved
   set (`iso imm secret raises in as extern inout sink consume discard
   break continue dyn true false`; `set` contextual); `spmd`/`kernel` as
   keyword vs attribute (ch07 Q1-3). Blocks `fors-lex`/`fors-parse` and
   every line of std.
2. Header and keyword leftovers: `contracts:` placement (ch02 Q3, encoded
   in ch07 `file`); `recover` reserved-unused vs dropped (ch01 Q2).
   One-line grammar changes, but they touch every module header.
3. Self-referential brand in the `with` header, `Arena[Node[nodes]]`
   (ch01 Q3). Blocks the checker's `with` scoping and std tree/graph
   containers.
4. Confirm trap = whole-process abort (ch02 Q1). Blocks the ABI and std.
5. Overlapping `let`/`let` default (ch01 Q1). Blocks backend alias facts.
6. `FAILURE_*` defaults; float return class (ch02 Q2, Q4). Blocks `fors-abi`.
7. Deliberately absent syntax: char literals, labelled `break`, match
   guards, tuple index fields, type aliases (ch07 Q4). Blocks nothing
   until std needs one.
8. `REDUCE_BLOCK`/`REDUCE_LANES` overridability (ch03 Q2).
9. `@declassify` gate; secret in `@device`; CT denylist (ch05 Q1-3).
10. Tunables: `MONOMORPHIZE_INSTR_THRESHOLD`, comptime budgets (ch03 Q1, ch04 Q1).
11. Security-release signer; `dyn.load` (ch04 Q2-3).
12. Measurement: Tier A additions, Tier B order, canary `N`, FLOP calibration, blocked `matmul` (ch06 Q1-5).
