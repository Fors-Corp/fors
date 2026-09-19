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
— ch05); the `brand` kind and brand parameters (`[A: brand]`); branded
arenas (`Arena[T, A]`, `Ref[T, A]`), brand non-escape, all-modes generation
check; branded allocators (`Own[T, A]`), `with allocator`; the
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
- **Brand**: a phantom type argument of kind `brand`. It has no values, no
  size and no runtime representation. A brand is either a **fresh brand**
  (introduced by one `with arena` / `with allocator` block, Rule 15) or a
  **brand parameter** (`[A: brand]`, Rule 15d).
- **Brand-mentioning type**: a type with a brand anywhere in its type
  arguments (`Ref[Node, A]`, `Vec[Ref[Node, A]]`, a closure capturing one).
- **Scoped value**: a non-owning projection that cannot outlive the call
  that produced it, except under the scoped-return rule.
- **`Shared`**: a marker trait with no methods and no runtime
  representation. `impl Shared for T {}` is accepted only when every field
  of `T` is `atomic[U]`, `imm`, or itself a type implementing `Shared`
  (Rule 21a); it is otherwise an ordinary trait, usable as a generic bound.

## Rules

1. Every parameter MUST declare exactly one convention.
2. A call site MUST mark a non-`let` argument: `&x` (inout), `move x`
   (sink), `&out x` (set); `let` carries no marker. `move` marks a place
   expression (binding or projection path); an rvalue argument (literal,
   call result) to a `sink` parameter carries no marker.
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
15. `with arena x: Arena[T] { ... }` and `with allocator x: Alloc { ... }`
    are statements (they yield no value). Each such block in the source
    introduces exactly one fresh brand; inside the block `x` has type
    `Arena[T, β]` (resp. `Alloc[β]`) where `β` is that fresh brand. In type
    position inside the block, and inside the header's own type `T`
    (needed for self-referential element types, `Arena[Node[x]]`), the
    identifier `x` denotes `β` (`Ref[Node, x]`); `β` has no other spelling and MUST NOT be nameable
    outside the block. `β` equals only itself: it MUST NOT be unified with,
    or inferred for, any brand parameter or type variable of an enclosing
    declaration. Non-escape is therefore local: (a) every binding's type
    is fixed at its declaration (no deferred inference), and every
    signature, field and outer binding is declared where `β` has no
    spelling, so none can have a brand-mentioning type naming `β`; (b) a
    brand-mentioning type MUST NOT be converted to any erased form —
    `dyn` trait object, function-pointer type, or existential; (c) a task
    that can outlive the block MUST NOT capture a brand-mentioning value
    (a structured `spawn` inside the block MAY, Rule 13).
15a. `Arena[T, A]` and every allocator type MUST have no constructor: a
    value of such a type exists only as the binding of a `with` block. It
    MUST NOT be `Copyable`, moved, passed `sink`, assigned or swapped as a
    whole, stored in a field, or captured by a task that can outlive the
    block; it is passed only as `let` or `inout`. Hence at most one live
    arena (allocator) value exists per brand per dynamic block instance.
15b. The omitted brand argument (`Arena[Node]`, `PageAllocator`) is legal
    only in the `with` header; every other use of a branded type MUST
    write its brand argument.
15c. A `with` block re-entered (loop, recursion) reuses the same static
    brand. This is sound because no value of a brand-mentioning type
    survives its block instance (Rule 15) and an inner instance's
    signature cannot name the outer instance's `β`.
15d. A generic parameter MAY have the kind bound `brand`
    (`fn insert[A: brand](...)`, `struct Tree[A: brand] { root: Ref[Node, A] }`).
    A brand parameter MUST appear only as a type argument in a position
    whose declared kind is `brand`; using it as the type of a value, in
    `size_of`/`align_of`, as a trait bound subject, or passing a
    non-brand type for it (or a brand for an ordinary type parameter)
    MUST be rejected. A brand argument at a call site is solved only by
    type equality against the argument types; there is no brand
    subtyping, variance, coercion or join, so one call whose arguments
    carry two different brands for the same parameter MUST be rejected.
    A type that stores a brand-mentioning field MUST itself take that
    brand as a parameter.
15e. Brands are erased after checking: a brand argument MUST NOT be part
    of an instantiation shape or cache key, MUST NOT cause a separate
    monomorphized body, and has no witness table or witness-table slot
    (ch03 Rules 16-17). Two instantiations differing only in brand
    arguments MUST share one compiled body.
16. `Ref[T, A]` MUST be usable only against an `Arena[T, A]` with the
    equal brand `A` (plain type equality, checked per call, no
    interprocedural analysis); any other use MUST be a compile error.
17. Every arena MUST carry a generation counter bumped on `reset`; every
    `Ref` dereference MUST be generation-checked in every build mode, never
    elided by optimization level.
18. `Own[T, A]` MUST record its producing allocator's brand `A`; `deinit`
    with an allocator whose brand differs from `A` MUST be a compile error.
    Allocator brands follow Rules 15-15e unchanged.
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
21. `atomic[T]` MUST appear only as a field of a type implementing
    `Shared` (Rule 21a); on any other type it MUST be a compile error.
21a. `impl Shared for T {}` MUST be checked field-wise: every field of `T`
    MUST be `atomic[U]`, `imm`, or a type that itself implements `Shared`;
    otherwise it MUST be a compile error naming the first non-conforming
    field. The `impl` MUST appear in the module that defines `T`, so every
    private field is visible to the check; an `impl Shared for T {}`
    written in any other module MUST be rejected. "Field" means every
    struct field and every component of every enum variant payload; a
    tuple- or `Array[U, N]`-typed field conforms iff each component type
    does; a `dyn`, function-typed or closure-typed field conforms only if
    `imm`. The implemented type MUST be a struct or enum named by its
    declaration (`impl Shared for Counter`, `impl[P: Shared] Shared for
    Box[P]`), never a type parameter, so a blanket `impl[T] Shared for T
    {}` MUST be rejected. A field whose type mentions a type parameter `P`
    of `T` conforms only if the field is `imm` or the `impl` declares
    `P: Shared`; the check runs once on the declaration, never per
    instantiation, so `Box[NotShared]` simply does not implement `Shared`.
21b. `Shared` MAY be used as a generic trait bound
    (`fn bump[T: Shared](let c: T)`), restricting instantiation to types
    that implement it, exactly like any other trait bound.
21c. The Rule 21a field check MAY be skipped only by
    `@unsafe(invariant: "...") impl Shared for T {}` (ch04 Rule 10's
    attribute form), which MUST appear in the published unsafe inventory
    (ch04 Rule 9's ledger). The defining-module requirement of Rule 21a
    still applies to it.
21d. `atomic[U]`'s operations take the cell by `let` and are the only
    exception to Rules 11 and 20: an `imm` or `let` path to a `Shared`
    value still reaches its atomic cells mutably, and reaches nothing else
    mutably — which is what the Rule 21a field check guarantees. `Shared`
    does not change Rule 13: a `Shared` value crosses a task boundary only
    as `imm`, as `iso` by `move`, or as a structured-`spawn` capture.

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
    with arena nodes: Arena[Node[nodes]] {
        let x: Ref[Node[nodes], nodes] = nodes.alloc(Node { next: none, val: 1 });
        let y: Ref[Node[nodes], nodes] = insert(&nodes, x, Node { next: none, val: 2 });
        nodes[x].next = some(y);        // inout subscript, Rule 16/17
    }
}

struct Node[A: brand] { next: Option[Ref[Node[A], A]], val: i64 }

// Brand-polymorphic helper (Rule 15d): A is solved by type equality from
// `arena` and `parent`; passing a Ref of another arena is a type error.
fn insert[A: brand](inout arena: Arena[Node[A], A], let parent: Ref[Node[A], A],
                    sink value: Node[A]) -> Ref[Node[A], A] {
    let r: Ref[Node[A], A] = arena.alloc(move value);
    arena[parent].next = some(r);
    return r;
}

fn boxed(let n: i64) {
    with allocator heap: PageAllocator {
        var b: Own[i64, heap] = heap.create(n);
        heap.deinit(move b);            // same brand: accepted, Rule 18
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

struct Counter { n: atomic[u64] }
impl Shared for Counter {}          // accepted: field is atomic[u64], Rule 21a

fn bump[T: Shared](let c: T) { }    // Shared as a generic bound, Rule 21b

struct Cell[P] { n: atomic[u64], v: P }
impl[P: Shared] Shared for Cell[P] {}   // generic field needs the bound, Rule 21a

struct Cache { n: atomic[u64], buf: rawptr[u8] }
@unsafe(invariant: "buf is written only before publication, read-only after")
impl Shared for Cache {}            // escape hatch, Rule 21c: buf skips the field check
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
4. `Shared` is a library marker trait, not a fourth qualifier. Owner
   decision 2026-09-19, round 2 (R2-2): the marker is checked, not
   declarative — `impl Shared for T {}` is accepted only field-wise
   (Rule 21a), the `impl` must live beside `T` so private fields stay
   visible to the check, and `@unsafe(invariant: "...")` is the sole
   escape hatch (Rule 21c), listed in the unsafe inventory.
5. Scoped-return marker: `scoped(p)` prefix on the return type naming the
   designated parameter explicitly (verifier change: the earlier implicit
   "first scoped-eligible parameter" was not a checkable definition). The
   caller-side extent is lexical (Rule 19a) so the single forward pass of
   Rule 6 needs no liveness analysis.
7. Structured `spawn` captures are accesses, not sends (Rule 13): without
   this, Rule 9's `parallel for` stores and `split_at` halves could not be
   used from tasks at all.
8. Brand non-escape forbids type erasure of brand-mentioning types (Rule
   15(b)); an erased `Ref` re-entering a later dynamic instance of the same
   `with arena` block would otherwise defeat the brand.
6. `Own[T, A]` brand mismatch is a compile error, since brands are always
   statically known at the `deinit` call site.
9. Owner decision 2026-09-19 (D1): brands are phantom generic parameters
   of kind `brand`, fresh only from `with arena` / `with allocator`,
   erased after checking (Rules 15-15e, 16, 18). Verifier additions that
   close leaks D1 left open: no constructor / no whole-value move or swap
   of an arena or allocator (15a — otherwise a brand-polymorphic callee
   could mint a second arena under the caller's brand and defeat Rule
   16); a fresh brand never unifies with an outer variable (15); `with`
   yields no value (15); brand-kind positions are closed (15d); erasure
   from shapes and witness tables (15e).
10. Owner decision 2026-09-19 (D4): `scoped(p)` prefix (Rule 19) and the
   structured-`spawn` capture clause (Rule 13: an `inout` capture is an
   access lasting to the end of the enclosing `parallel` block) accepted.

## Open questions for the owner

1. Confirm/override Rule 7's default (allow vs. forbid overlapping
   `let`/`let`) — your call; affects backend aliasing facts.
2. Confirm dropping `recover`, vs. reserving it for a future qualifier.
3. Self-referential element types: Rule 15 lets the `with` header name
   its own binding as a brand (`with arena nodes: Arena[Node[nodes]]`),
   because a node that links to siblings must take the brand (Rule 15d).
   Drafted as allowed; confirm, or choose another spelling before std's
   tree/graph containers are written.

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
  rejected; returning, `&out`-storing or outer-assigning a `Ref[T, β]`
  rejected.
- `brand_param_helper_accepted` — `insert[A: brand]` called with an arena
  and a `Ref` of the same block accepted.
- `brand_param_two_arenas_rejected` — one call passing arena `a` and a
  `Ref` from arena `b` for the same `A` rejected.
- `brand_fresh_not_unified_with_param` — inside `fn f[A: brand]`, returning
  a `Ref` of a local `with arena` as `Ref[T, A]` rejected.
- `brand_kind_closed` — `let v: A`, `size_of[A]()`, `Vec[A]`, and an
  ordinary type passed for `A: brand` each rejected.
- `brand_erased_single_body` — instantiations differing only in brand
  share one compiled body; no witness slot for `A`.
- `arena_no_constructor` — constructing, copying, swapping or `sink`-passing
  an `Arena[T, A]` / allocator value rejected.
- `brand_field_requires_param` — `struct S { r: Ref[Node, A] }` without
  `[A: brand]` rejected.
- `brand_detached_capture_rejected` — detached task capturing a
  brand-mentioning value rejected; structured `spawn` accepted.
- `with_block_no_value` — `let r = with arena a: Arena[T] { ... };` rejected.
- `with_allocator_brand` — `Own[T, heap]` deinit by a second allocator's
  brand rejected.
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
- `shared_impl_field_check_rejected` — `impl Shared for T {}` with a
  non-`atomic`/non-`imm`/non-`Shared` field rejected.
- `shared_impl_field_check_accepted` — `impl Shared for T {}` with every
  field `atomic`, `imm` or `Shared` accepted.
- `shared_impl_generic_field_needs_bound` — `impl[P] Shared for Cell[P] {}`
  with a field `v: P` rejected; with `P: Shared` accepted; blanket
  `impl[T] Shared for T {}` rejected.
- `shared_impl_enum_payload_checked` — an enum with a variant payload of a
  non-`Shared`, non-`imm` type fails the field check.
- `shared_impl_foreign_module_rejected` — `impl Shared for T {}` written
  outside `T`'s defining module rejected.
- `shared_bound_generic_accepted` — `fn bump[T: Shared]` accepts a
  `Shared`-implementing argument type, rejects a non-`Shared` one.
- `shared_unsafe_escape_hatch_listed` — `@unsafe(invariant: "...") impl
  Shared for T {}` skips the field check and appears in the unsafe
  inventory.
