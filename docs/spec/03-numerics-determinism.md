# Chapter 03 — Numerics, Determinism, Reductions and Generics Lowering

## Status

Draft, M0.5, 2026-09-19. Implements PLAN.md R5 (determinism default, reduction-tree shape), R6 (generics lowering default), R12 (`SVec[T]` reserved syntax), and 4.3(1) (strict IEEE-754 default, no FMA contraction by default).

## Scope

Owns: integer width/overflow semantics and `wrap_/sat_/unchecked_`; checked `as`; float strict-IEEE default and `@fastmath`; D1 determinism; `reduce`'s tree shape, tail rules, lowering order; accumulator-loops-never-auto-parallelized; generics lowering (monomorphize vs. witness table), instantiation cache, `@specialize` enforcement; `vector[T,N]`/`mask[N]`; reserved `SVec[T]`.

Not owned: conventions/aliasing (ch01), `raises`/`?`/`raise` and what a trap does (ch02 — this chapter only names trap conditions), `needs` and the `@unsafe` form (ch04), FMIR/OIR structure (ch05).

## Definitions

- **D1**: results bit-identical across thread count, steal pattern, core class, locale count, for a fixed binary and input.
- **Reduction tree**: `reduce`'s fixed shape, a function of `(n, B, L)` only (`B` = `REDUCE_BLOCK`, `L` = `REDUCE_LANES`).
- **Leaf block**: up to `B` consecutive elements reduced into one partial by the lane shape of Rule 11.
- **Lane**: lane `j` (`0 <= j < L`) of a block holds the block's elements at block-relative indices `j, j+L, j+2L, ...`. A lane is *empty* when the block has `<= j` elements.
- **Instantiation shape**: `(size, align, pointerness, qualifier, deinit-ness)` of a generic argument type. Brand arguments are not part of it (ch01 Rule 15e).
- **Witness table**: `{size, align, copy, move, deinit, method_slots}`, layout-identical to a `dyn T` fat pointer.

## Rules

1. Integers are fixed-width (`i8..i64`, `u8..u64`; no 128-bit in v1); any other width MUST be rejected.
2. `+ - * / %` and shifts MUST trap on overflow, div-by-zero, or shift-by-≥-width, in every mode including release.
3. No build flag or mode MAY disable trapping for plain operators; non-trapping paths exist only via Rule 4.
4. Every trapping op MUST have `wrap_<op>`, `sat_<op>`, `unchecked_<op>` counterparts (method form, `x.wrap_add(y)`); `unchecked_<op>` MUST NOT appear outside a declaration carrying `@unsafe(invariant: "...")` (ch04 Rule 10; there is no call-site or block form).
5. No implicit numeric conversion (widening, int↔float, float↔float) is allowed; type `A` MUST NOT stand in for `B` unless identical.
6. `as Type` MUST be checked and trapping (traps if not exactly representable); lossy conversion MUST use `wrap_as`/`sat_as`/`trunc_as`.
7. Floats default to strict IEEE-754: no FMA contraction, no reassociation, in every mode.
8. Rule 7 relaxes only inside lexical `@fastmath(flags) { ... }`, `flags ⊆ {reassoc, contract, nsz, finite, recip}`; no relaxed transform MAY escape the block's lexical extent.
9. `comptime_int`/`comptime_float` are arbitrary-precision, comptime-only; escaping to runtime without an explicit conversion to a fixed-width type MUST be rejected.
10. Default determinism is D1: bit pattern MUST NOT change with thread count, steal pattern, core class mix, or locale count alone.
11. `reduce(op, xs)` is a distinct primitive. For `n >= 1`: partition `xs` (length `n`) into `k = ceil(n/B)` leaf blocks of consecutive elements (the last block holds `n mod B` elements, or `B` if exact). Each block, full or partial, is reduced in two steps. (i) **Lane fold**: for each non-empty lane `j`, `l_j = x_j; l_j = op(l_j, x_{j+L}); l_j = op(l_j, x_{j+2L}); ...` in ascending index order (accumulator is the left operand). (ii) **Lane combine**: the fixed pairwise tree `((l0 ∘ l1) ∘ (l2 ∘ l3)) ∘ ((l4 ∘ l5) ∘ (l6 ∘ l7))`, where `a ∘ b = op(a, b)` with the lower-numbered lane on the left; a node with exactly one empty operand yields its other operand unchanged (no `op` application), and a node with two empty operands is empty. Because non-empty lanes are always the prefix `l0 .. l_{min(m,L)-1}` of a block with `m` elements, this gives exactly one shape per `m`. Then the `k` block partials combine level by level: at each level adjacent partials `(0,1), (2,3), ...` are combined as `op(left, right)` and an unpaired last partial is carried up unchanged, until one remains. The shape is a pure function of `(n, B, L)`; it equals the serial left fold only for `n <= 3`. `B` is the named constant `REDUCE_BLOCK` = **256** and `L` the named constant `REDUCE_LANES` = **8**; both are target-independent literals that MUST NOT depend on hardware lane width, grain, threads, locales, target or build flags, and neither is overridable (Open question 2). A target with fewer than 8 (or no) vector lanes MUST compute the same 8 logical lanes (scalar emulation or several narrower registers); a wider target MUST NOT use more. `op` MUST be pure (no capability use, no `inout` capture); neither associativity nor commutativity is required because the tree and every operand order are fixed.
11a. For `n = 0`: `reduce(op, xs)` MUST trap (kind: empty-reduce, ch02); `reduce(op, xs, identity: e)` MUST return `e`. For `n >= 1` the `identity` argument MUST NOT participate in the fold, so both forms are bit-identical on non-empty input.
12. `reduce` MUST lower to this explicit tree in FMIR **before** parallel lowering, so `--serial-elide` is bit-exact against any parallel execution of the same tree.
13. Tail rules: (a) no identity-padding — a partial block uses the same 8-lane shape over only its present elements; a lane shorter than its neighbours simply stops, and an empty lane contributes nothing: it is skipped in the lane combine (Rule 11(ii)) and MUST NOT be replaced by `identity`, zero or any other value (a vector implementation masks with select, never by feeding a neutral element to `op`); (b) IEEE `-0.0` handling with no inserted normalization; (c) NaN handling is exactly `op`'s applied in the Rule 11 order (for IEEE `+`/`*` any NaN input therefore yields NaN); no transform MAY reorder or drop an operand; (d) the last block's partial enters the combine tree at its own block index, never reordered or merged early.
14. `reduce.serial`/`reduce.fast`/`reduce.exact` are separate named primitives, never selected implicitly by optimization level; only unqualified `reduce` carries D1.
15. A scalar accumulator loop MUST NOT be auto-parallelized or auto-`reduce`d at any level; the compiler MUST emit a diagnostic naming the loop and stating that explicit `reduce` is required.
16. Monomorphize when instantiation shape is scalar, ≤ `MONOMORPHIZE_SIZE_MAX` (16) bytes, or the body's instruction count is below the named constant `MONOMORPHIZE_INSTR_THRESHOLD`; otherwise lower via witness table (layout-identical to `dyn T`).
17. Monomorphized instantiations MUST be deduplicated via a content-addressed cache keyed on `(declaration hash, argument type shape hashes)`.
18. `@specialize` is compiler-enforced inside `simd`/`spmd`/`kernel` regions: an unspecialized witness-table call there MUST be a compile error with its own diagnostic code, never a silent indirect call.
19. `vector[T,N]` (fixed, comptime power-of-two `N`) and `mask[N]` are distinct types; masked-off lanes MUST NOT fault or trap regardless of underlying data.
20. `SVec[T]` is reserved: rejected as a struct/tuple field, heap element type, or generic container argument; legal only as a local/parameter inside `simd`/`spmd` bodies, and only where hardware support is enabled — otherwise a compile error, never a silent scalar fallback.

## Examples

```fors
needs { };

fn accumulate_bytes(let xs: Slice[u8]) -> u32 {
    var total: u32 = 0;
    for b in xs { total = total.wrap_add(b as u32); }  // widening as: exact, never traps
    return total;
}
```

```fors
fn dot(let a: Slice[f64], let b: Slice[f64]) -> f64 raises DimError {
    if a.len != b.len { raise DimError.mismatch; }
    var sum: f64 = 0.0;
    @fastmath(reassoc, contract) {
        for i in 0 ..< a.len { sum = sum + a[i] * b[i]; }  // contracted+reassoc, this block only
    }
    return sum;
}
```

```fors
needs { };

fn sum_deterministic(let xs: Slice[f64]) -> f64 {
    return reduce(+, xs, identity: 0.0);   // tree = f(n, REDUCE_BLOCK, REDUCE_LANES); n = 0 yields 0.0
}

fn sum_naive(let xs: Slice[f64]) -> f64 {
    var acc: f64 = 0.0;
    for x in xs { acc = acc + x; }  // never auto-parallelized
    return acc;
}
```

```fors
fn max_lane[T: Ord](let v: vector[T, 8], let m: mask[8]) -> T {
    var best: T = v[0];  // T=i32: scalar, monomorphized, no witness call in simd
    for i in 1 ..< 8 { if m.lane(i) { best = if v[i] > best { v[i] } else { best }; } }
    return best;
}
```

## Rejected alternatives

- Serial in-leaf fold — forbids vectorizing a strict-IEEE `reduce`; replaced by 8 fixed logical lanes (D3).
- Lane/thread-derived block size for `reduce` — makes bit-identity machine-dependent, defeats D1.
- Release-mode wrapping as overflow default — recreates dev/release semantic divergence.
- `@fastmath` as a global flag — per-region scoping keeps the reference interpreter and review tractable.
- Witness-table-by-default generics — R6 flips this to avoid rewriting std after benchmarking the indirect-call cost.
- Auto-vectorizing/parallelizing accumulator loops — silently changes float order, violates D1.

## Decisions made while drafting

- `@fastmath` flag set fixed to `{reassoc, contract, nsz, finite, recip}`, superseding surface-language.md's `{reassoc, fma, no_nan}` example; PLAN.md left naming open, this is locally decidable.
- `B` default fixed at **256** per PLAN.md R5's literal text, overriding parallel-heterogeneous.md's `B = 4 * native_lanes` (target-dependent, which R5 forbids).
- Owner decision 2026-09-19 (D3): leaves use `REDUCE_LANES` = 8 fixed lanes with a fixed pairwise lane combine (Rule 11), replacing the serial leaf; bit patterns of every float `reduce` change relative to the earlier draft. Verifier additions: operand order is stated for every `op` application (lower lane / accumulator on the left) so non-commutative `op` and NaN payloads are fixed; "skip an empty lane" is defined per combine node; wider hardware may not use more than 8 lanes. Note for implementers: the usual SIMD horizontal reduction adds the low half to the high half (`l0+l4, ...`); Rule 11 requires adjacent pairing (`l0+l1, ...`).
- Tail rules (13) drafted from scratch: PLAN.md requires them but gives no content; chosen rules are the simplest requiring no extra analysis (no padding, standard IEEE zero/NaN behavior, fixed block-index ordering).
- `MONOMORPHIZE_INSTR_THRESHOLD` is named as a single constant here; its numeric value is deferred to whoever first writes std against it (a tuning, not semantics, decision).
- Verifier additions: the combine tree is now spelled out (adjacent pairing, odd partial carried) because "balanced tree" is not unique for non-power-of-two `k`; `n = 0` traps unless an `identity:` is supplied (Rule 11a), which is the only closure that never changes a non-empty result; `B` is named `REDUCE_BLOCK` and the 16-byte bound `MONOMORPHIZE_SIZE_MAX`.
- `reduce.serial`/`.fast`/`.exact` kept from parallel-heterogeneous.md as they don't conflict with R5.

## Open questions for the owner

1. Pin `MONOMORPHIZE_INSTR_THRESHOLD`'s value now, or defer to std authoring per R6's rationale?
2. Are `REDUCE_BLOCK` / `REDUCE_LANES` ever overridable (only conceivable form: a literal at the call site)? Drafted as: no.

## Conformance tests

- `int_overflow_traps_release`: `i32.MAX + 1` in release MUST trap.
- `int_no_implicit_widen`: `u8` into `u32` binding without `as` MUST be a compile error.
- `checked_as_rejects_lossy`: `300u32 as u8` MUST trap.
- `wrap_as_truncates`: `300u32.wrap_as[u8]()` MUST yield `44`, never trap.
- `float_default_no_fma`: `a*b+c` outside `@fastmath` MUST NOT fuse.
- `fastmath_scope_ends`: code after a `@fastmath(contract){}` block MUST NOT be contracted.
- `reduce_bitexact_across_threads`: `reduce(+, xs)` MUST bit-match across `FORS_NUM_THREADS` ∈ {1,2,8}.
- `reduce_tail_no_padding`: with `op` = IEEE `+` and all elements `-0.0`, every `n` in `1..=2B+1` MUST yield `-0.0` (a padded `+0.0` lane would give `+0.0`).
- `reduce_shape_reference`: with a non-associative, non-commutative `op` (string-building `"(" a " " b ")"` in the interpreter; float `-` natively), `n` in `{1, 2, 3, 4, 7, 8, 9, 15, 16, 17, 255, 256, 257, 511, 512, 513, 600, 3B, 5B-1}` MUST bit-match the reference tree of Rule 11; e.g. `n = 7` is `((x0 x1)(x2 x3))((x4 x5) x6)`, `n = 9` is `(((x0 x8) x1)(x2 x3))((x4 x5)(x6 x7))`, `n = 257` is `op(block0, x256)`, `n = 600` is `op(op(block0, block1), block2)` with `block2` over 88 elements (11 per lane).
- `reduce_scalar_vector_agree`: the scalar-emulated and the vectorized lowering of one `reduce(+, xs)` over `f64` MUST bit-match for every `n` in `0..=600`.
- `reduce_empty`: `n = 0` without `identity:` MUST trap; with `identity: e` MUST return `e`; `identity:` MUST NOT alter any `n >= 1` result (checked with `identity: NaN`).
- `reduce_nan_propagates`: for `reduce(+, xs)` any NaN element MUST make the result NaN.
- `reduce_serial_elide_matches_parallel`: `--serial-elide` output MUST bit-match default parallel output.
- `accumulator_loop_not_parallelized`: accumulator loop result MUST NOT vary with `--threads`; diagnostic MUST fire.
- `generics_scalar_monomorphized`: scalar ≤16-byte instantiation MUST NOT contain a witness-table call.
- `generics_specialize_enforced_in_simd`: unspecialized generic call in `simd` MUST be a compile error.
- `instantiation_cache_dedup`: two call sites, same key, MUST share one compiled body.
- `mask_lane_never_faults`: masked-off lane over unmapped memory MUST NOT fault.
- `svec_rejected_in_struct_field`: `SVec[T]` struct field MUST be a compile error.
- `svec_rejected_without_hardware`: `SVec[T]` on unsupported hardware MUST be a compile error, not scalar fallback.
