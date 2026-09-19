# Chapter 01 — Ownership, Conventions, Qualifiers and Arenas

## Status

Draft, M0.5, 2026-09-19. Implements PLAN R1 (sharing qualifiers, secret
taint, sendability), R2 (branded arenas/allocators), R3 (scoped-return).
Normative; PLAN §4.2/§4.3 win over `docs/design/*`.

## Scope

Owns: conventions `let`/`inout`/`sink`/`set` and call-site markers;
destructive moves; the exclusivity conflict check, including the
varying-index rule for `parallel`/`simd`/`kernel`; sharing qualifiers
`iso`/`imm` and the sendability rule; `secret`'s position (not its CT rules
— ch05); branded arenas (`Arena[T]`, `Ref[T, brand]`), brand non-escape,
all-modes generation check; branded allocators (`Own[T, A]`); the
scoped-return rule; interior-mutability policy and `atomic[T]`'s position.
Slice signatures, other escape kinds, the failure ABI, and capability
manifests belong to other chapters.

## Definitions

- **Projection path**: a parameter/local plus field/index projections, e.g.
  `a.b[i].c`.
- **Convention**: a parameter's one access mode: `let`, `inout`, `sink`,
  `set`.
- **Sharing qualifier**: `iso` or `imm`, orthogonal to convention.
- **Secret taint**: the qualifier `secret`, orthogonal to sharing.
- **Brand**: the nominal type introduced by `with arena b: Arena[T] { }`,
  scoped to that block.
- **Scoped value**: a non-owning projection that cannot outlive the call
  that produced it, except under the scoped-return rule.

## Rules

1. Every parameter MUST declare exactly one convention.
2. A call site MUST mark a non-`let` argument: `&x` (inout), `move x`
   (sink), `&out x` (set); `let` carries no marker.
3. A `let` parameter MUST NOT be assigned to or moved from.
4. A `sink` parameter MUST be moved-from or deinitialized on every path,
   unless `Copyable`.
5. A `set` parameter MUST be fully initialized on every return path.
6. Exclusivity is one forward dataflow pass per function over projection
   paths, no fixpoint, no interprocedural analysis; a callee's effect on an
   argument is exactly its declared convention.
7. Two simultaneous overlapping accesses MUST be rejected if either is
   `inout`, `sink`, or `set`. Two overlapping `let` accesses MUST be
   accepted (Decisions §1).
8. At a CFG merge every path MUST agree on each local's liveness;
   disagreement MUST be an error, resolved by explicit `consume x` /
   `discard x` (no drop flags).
9. Inside a region with induction variable `i`, a varying store to an
   `inout` slice at index `e` MUST be accepted iff `e` is `i` or an affine
   `a*i+b` with compile-time-constant, nonzero `a`; any other index MUST be
   rejected unless targeting a disjoint view minted by a stdlib split
   primitive. Every other access (read or write) in the region to a slice
   that has a varying store MUST use the syntactically identical index
   expression `e`; otherwise the region MUST be rejected (`out[i]` written
   with `out[i+1]` or `out[i-1]` also accessed is a cross-iteration race).
10. There are exactly two sharing qualifiers, `iso` and `imm`; `mut`/`ro`
    MUST NOT exist — `inout`/`let` already cover them.
11. Reading a field of an `imm` value MUST yield `imm` (deep immutability).
12. An `iso` binding MUST be extracted only by `move`; the source MUST then
    be dead.
13. Sendability (the one rule). A value MUST cross a channel, isolation
    domain, locale, or any task that can outlive its spawning block only if
    `imm`, or `iso` and captured via `move`. A `spawn` lexically inside a
    structured `parallel { }` / `parallel for` block (implicit sync at the
    block's close) MAY additionally capture a local or scoped value by its
    convention; each such capture is an access under Rules 6-7 whose extent
    is the remainder of the enclosing `parallel` block. Any other capture
    MUST be rejected.
14. `secret` MUST NOT be a sharing qualifier and MUST NOT join with
    `iso`/`imm`; it composes orthogonally (`iso secret T` is legal). CT
    obligations are ch05's.
15. `with arena b: Arena[T] { }` MUST introduce a brand `b`, a name in
    scope only inside that block, that MUST NOT appear in any type
    returned, stored, or captured outside that block. Non-escape is local
    because: (a) every binding's type is fixed at its declaration (no
    deferred inference), so no outer binding can have a type mentioning
    `b`; (b) a type mentioning a brand (including a closure type with a
    branded capture) MUST NOT be converted to any erased form — `dyn`
    trait object, function-pointer type, or witness-table existential;
    (c) the arena binding itself MUST NOT be moved, and a task that can
    outlive the block MUST NOT capture a brand-mentioning value.
16. `Ref[T, b]` MUST be usable only against the `Arena[T]` carrying brand
    `b`; use against any other arena MUST be a compile error.
17. Every arena MUST carry a generation counter bumped on `reset`; every
    `Ref` dereference MUST be generation-checked in every build mode, never
    elided by optimization level.
18. `Own[T, A]` MUST record its producing allocator's brand `A`; `deinit`
    with an allocator whose brand differs from `A` MUST be a compile error.
19. A function MAY return a scoped value iff every scoped derivation in
    that return flows from exactly one designated parameter `p`, named by
    a `scoped(p)` return-type prefix; `p` MUST have convention `let` or
    `inout` (never `sink`/`set`); every `scoped(...)` in one signature MUST
    name the same parameter; combining scoped material from two parameters
    or a local MUST be rejected.
19a. At the call site, the access to the designated argument (with `p`'s
    convention) MUST extend to the end of the lexical scope of the binding
    that receives the scoped result (or to an earlier explicit
    `discard`). A scoped value MUST NOT be stored in a field, container or
    heap object, assigned to a binding of an outer scope, converted to an
    erased type, or captured by anything except a structured `spawn`
    (Rule 13); it MAY be returned only under Rule 19.
19b. Two range/index projections of the same path are treated as
    overlapping by Rule 7 regardless of their bounds; disjoint sub-views
    exist only as results of stdlib split primitives, which are
    `@unsafe(invariant: "...")` declarations (ch04 Rule 10).
20. The safe sequential subset MUST NOT provide interior mutability:
    mutating through a `let` or `imm` path MUST be rejected outside arena
    subscripts.
21. `atomic[T]` MUST appear only as a field of a `Shared`-marked type; on
    any other type it MUST be a compile error.

## Examples

```fors
needs { };

@unsafe(invariant: "the two ranges partition s and never overlap")
fn split_at[T](inout s: Slice[T], let mid: usize)
    -> (scoped(s) Slice[T], scoped(s) Slice[T])
    pre mid <= s.len
{
    return (s[0 ..< mid], s[mid ..< s.len]);   // Rules 19, 19b
}

fn halves(inout buf: Slice[f64]) {
    let (lo, hi) = split_at(&buf, buf.len / 2); // inout access to buf lasts
    parallel {                                  // to the end of this scope
        spawn fill(&lo, 0.0);                   // structured capture, Rule 13
        fill(&hi, 1.0);
    }
}
```

```fors
needs { };

fn build() {
    with arena nodes: Arena[Node] {
        let x: Ref[Node, nodes] = nodes.alloc(Node { next: none, val: 1 });
        let y: Ref[Node, nodes] = nodes.alloc(Node { next: none, val: 2 });
        nodes[x].next = some(y);        // inout subscript, Rule 16/17
    }
}
```

```fors
needs { };

fn scale(inout out: Slice[f64], let k: f64) {
    parallel for i in 0 ..< out.len {
        out[i] = out[i] * k;            // legal: index is i, Rule 9
    }
}

fn scatter_bad(inout out: Slice[f64], let idx: Slice[usize]) {
    parallel for i in 0 ..< idx.len {
        out[idx[i]] = 0.0;              // MUST NOT compile: not affine in i
    }
}
```

```fors
needs { };

fn spawn_work(sink data: iso Buffer[u8], let key: secret u64) raises Error {
    parallel {
        spawn process(move data);       // legal: iso moved, Rule 13
    }
    let h = hash(key)?;                 // secret flows; ct rules in ch05
}
```

## Rejected alternatives

- Four-qualifier lattice (`iso`/`mut`/`imm`/`ro`) + `recover` — redundant
  with `inout`/`let`; PLAN R1.
- Lifetime/region inference for arenas — forbidden; brands chosen (R2).
- Unbranded `Handle[T]` — allows cross-arena confusion.
- General index-disjointness analysis for parallel loops — not locally
  decidable; replaced by the affine rule plus split-minted views.
- `secret` as a third sharing position — breaks composability.
- Debug-only generation counter — contradicts R2's "all modes."
- Fresh brand per `reset` — rejected; kept single brand + generation so an
  arena is loop-reusable.

## Decisions made while drafting

1. Overlapping `let`/`let` access allowed (Rule 7) — design material flags
   this as an aliasing-facts-vs-ergonomics call; drafted permissive as the
   locally decidable default.
2. Generation checks run in all modes per R2's explicit text, overriding
   `safety-security.md`'s "debug-checked" wording.
3. No `recover` keyword: with only two qualifiers there is nothing to
   promote from — `iso` comes only from `move`.
4. `Shared` is a library marker type, not a fourth qualifier.
5. Scoped-return marker: `scoped(p)` prefix on the return type naming the
   designated parameter explicitly (verifier change: the earlier implicit
   "first scoped-eligible parameter" was not a checkable definition). The
   caller-side extent is lexical (Rule 19a) so the single forward pass of
   Rule 6 needs no liveness analysis.
7. Structured `spawn` captures are accesses, not sends (Rule 13): without
   this, Rule 9's `parallel for` stores and `split_at` halves could not be
   used from tasks at all.
8. Brand non-escape forbids type erasure of brand-mentioning types (Rule
   15b); an erased `Ref` re-entering a later dynamic instance of the same
   `with arena` block would otherwise defeat the brand.
6. `Own[T, A]` brand mismatch is a compile error, since brands are always
   statically known at the `deinit` call site.

## Open questions for the owner

1. Confirm/override Rule 7's default (allow vs. forbid overlapping
   `let`/`let`) — your call; affects backend aliasing facts.
2. Confirm dropping `recover`, vs. reserving it for a future qualifier.
3. Confirm `scoped(p)` prefix syntax before ch07 locks slice signatures.
4. **Brand abstraction.** No rule says how a helper function accepts an
   arena plus `Ref`s into it (or an allocator plus `Own[T, A]`): a
   signature cannot name a brand that is scoped to a caller's block.
   Candidates: a brand parameter (`fn link[brand b](inout a: Arena[Node, b],
   let x: Ref[Node, b])`) or parameter-path brands (`Ref[Node, a]` where
   `a` is the arena parameter). Also undecided: how an allocator brand `A`
   is introduced at all. Blocks every arena/allocator-using std API.
5. Confirm Rule 13's structured-capture clause as part of "one sendability
   rule" (R1), or require `iso` partitioning even inside `parallel { }`.

## Conformance tests

- `conv_missing_inout_marker_rejected` — `inout` arg without `&x` rejected.
- `conv_missing_move_rejected` — `sink` arg without `move x` rejected.
- `conv_missing_set_marker_rejected` — `set` arg without `&out x` rejected.
- `excl_inout_inout_overlap_rejected` — two `&x` on one path rejected.
- `excl_let_let_overlap_accepted` — two overlapping `let` reads accepted.
- `excl_no_interprocedural` — caller's check unaffected by callee body.
- `merge_liveness_disagreement_rejected` — unresolved live/dead join
  rejected.
- `varying_induction_store_accepted` — `out[i]=...` in `parallel for`
  accepted.
- `varying_affine_store_accepted` — `out[2*i+1]=...` accepted.
- `varying_nonaffine_store_rejected` — `out[idx[i]]=...` rejected.
- `varying_zero_coefficient_rejected` — `out[0*i+3]=...` rejected.
- `sendability_imm_spawn_accepted` — `imm` capture into `spawn` without
  `move` accepted.
- `sendability_iso_move_accepted` — `iso` captured via `move` accepted.
- `sendability_iso_no_move_rejected` — `iso` captured without `move`
  rejected.
- `secret_iso_composition_accepted` — `iso secret T` type-checks.
- `arena_brand_mismatch_rejected` — foreign `Ref` against an arena
  rejected.
- `arena_brand_nonescape_rejected` — naming a brand outside its block
  rejected.
- `arena_generation_checked_in_release` — stale `Ref` traps in release.
- `allocator_brand_mismatch_rejected` — `deinit` with wrong-brand
  allocator rejected.
- `scoped_return_single_param_accepted` — scoped return from one param
  type-checks.
- `scoped_return_two_params_rejected` — scoped return mixing two params
  rejected.
- `scoped_return_sink_param_rejected` — `scoped(p)` naming a `sink`
  parameter rejected.
- `scoped_result_extends_inout_access` — using `buf` while a
  `split_at(&buf, ..)` result is still in scope rejected.
- `scoped_result_stored_rejected` — scoped value stored in a field or
  outer binding rejected.
- `range_projections_overlap_rejected` — safe `(s[0 ..< m], s[m ..< n])`
  as two live `inout` views rejected outside a split primitive.
- `varying_mixed_index_rejected` — `out[i] = out[i-1]` in `parallel for`
  rejected.
- `structured_spawn_inout_capture_accepted` — `spawn f(&lo)` inside
  `parallel { }` accepted; same capture by a detached task rejected.
- `arena_brand_erasure_rejected` — `Ref[T, b]` (or a closure capturing
  one) converted to `dyn`/fn-pointer type rejected.
- `arena_binding_move_rejected` — `move nodes` rejected.
- `interior_mut_imm_field_rejected` — mutation through `imm` outside an
  arena rejected.
- `atomic_outside_shared_rejected` — `atomic[T]` on non-`Shared` type
  rejected.
- `atomic_inside_shared_accepted` — `atomic[T]` on `Shared` type
  type-checks.
