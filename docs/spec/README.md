# Fors specification (M0.5 draft)

Authority order: `docs/PLAN.md` §4.2/§4.3 > these chapters > `docs/design/*`.

**Citation rule.** Every fact below is defined in exactly one chapter. Any
other document (chapter, design doc, comment, test) MAY only cite it
(`ch03 Rule 11`), never restate or redefine it.

## Chapters

1. `01-ownership.md` — conventions, exclusivity, qualifiers, arenas, scoped return
2. `02-failure.md` — `raises`/`raise`/`?`, failure ABI, traps, contracts, check removal
3. `03-numerics-determinism.md` — integers, floats, D1, `reduce`, generics lowering
4. `04-authority.md` — capabilities, `needs` vs manifest, comptime, build graph
5. `05-ir-contract.md` — IR levels, alias classes, secret/CT, tiles, differential agreement
6. `06-measurement.md` — benchmark tiers and metrics

## Fact -> owning chapter

| Fact | Owner |
|---|---|
| Qualifier set (`iso`, `imm`; `secret` orthogonal), sendability | ch01 R10-14 |
| Failure ABI, trap = whole-process abort | ch02 R4, R6-7 |
| Reduction tree and constant `REDUCE_BLOCK` = 256 | ch03 R11-13 |
| Comptime engine (one: FMIR interpreter) | ch04 R11-15 |
| Capability declaration sites (`needs` ⊆ manifest policy) | ch04 R1-3 |
| IR home of tiles, secrets, alias-class sources | ch05 R5-6b, R12 |
| Secret propagation and CT rejection rules | ch05 R6a-6b, R15 |
| `FAILURE_TAG_REG` (x9), `FAILURE_INLINE_MAX` (24) | ch02 R4 |
| `MONOMORPHIZE_SIZE_MAX` (16), `MONOMORPHIZE_INSTR_THRESHOLD` (unset) | ch03 R16 |
| `COMPTIME_STEP_BUDGET`, `COMPTIME_ALLOC_BUDGET` (unset) | ch04 R14 |
| `@unsafe(invariant:)` form | ch04 R10 |
| Check deletion, contract policy | ch02 R10-12 |

## Open owner questions (most blocking first)

1. **Brand abstraction** (ch01 Q4): how a function signature names an arena or allocator brand; how allocator brands are introduced. Blocks every arena/`Own` API in std.
2. **Privileged-capability sealing** (ch04 Q0): transitive `needs` union gives every std importer `syscall`. Blocks manifest/lockfile schema and std layout.
3. **`reduce` leaf shape vs SIMD** (ch03 Q1): serial leaves forbid vectorized strict float reductions; a later change alters every bit pattern. Blocks the interpreter's `reduce` and C parity.
4. Confirm trap = whole-process abort (ch02 Q1).
5. Structured-`spawn` capture clause in the sendability rule (ch01 Q5).
6. Overlapping `let`/`let` default (ch01 Q1).
7. `FAILURE_*` defaults; float return class (ch02 Q2, Q5).
8. `reduce` on `n = 0`; `REDUCE_BLOCK` overridability (ch03 Q3-4).
9. `@declassify` gate; secret in `@device`; CT denylist (ch05 Q1-3).
10. Syntax: `scoped(p)`, `raise`, `contracts:` placement, no `recover` (ch01 Q2-3, ch02 Q3-4); PLAN §4.3(3).
11. Tunables: `MONOMORPHIZE_INSTR_THRESHOLD`, comptime budgets (ch03 Q2, ch04 Q1).
12. Security-release signer; `dyn.load` (ch04 Q2-3). Measurement: ch06.
