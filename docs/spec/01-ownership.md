# Chapter 01 — Ownership, Conventions, Qualifiers and Arenas

## Status

Draft, M0.5, 2026-09-20. Implements PLAN R1 (sharing qualifiers, secret
taint, sendability), R2 (branded arenas/allocators), R3 (scoped-return),
and round 6's owner decisions O1 (linear types, Rules 22-22i) and O2
(`defer`/`errdefer`, Rules 23-23f).
Normative; PLAN §4.2/§4.3 win over `docs/design/*`.

## Scope

Owns: conventions `let`/`inout`/`sink`/`set` and call-site markers;
destructive moves; the exclusivity conflict check, including the
varying-index rule for `parallel`/`simd`/`kernel`; sharing qualifiers
`iso`/`imm` and the sendability rule; `secret`'s position (not its CT rules
— ch05); the `brand` kind and brand parameters (`[A: brand]`); branded
arenas (`Arena[T, A]`, `Ref[T, A]`), brand non-escape, all-modes generation
check; branded allocators (`Own[T, A]`), `with allocator`; the
scoped-return rule, including scope inheritance through a generic
parameter (Rule 19c); LINEARITY — which types carry a cleanup obligation,
what discharges it, and the scope-exit check (Rules 22-22i); the MEANING of
`defer` and `errdefer` — placement, order, what a body may contain and what
it may consume (Rules 23-23f; their syntax is ch07, the error-exit
definition they key on is ch02 Rule 16);
interior-mutability policy and `atomic[T]`'s position.
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
- **Linear type**: a type `T` for which `lin(T)` is true (Rule 22a). A
  live binding of linear type carries a **cleanup obligation**: one of
  Rule 22d's consumptions MUST take the value before its scope is left.
- **`Linear`**: a prelude marker trait with no methods, declared on a
  struct or enum by `impl Linear for T {}` in that type's defining module
  (Rule 22). It is the declared BASE of linearity; propagation through
  fields, payloads and tuple components is inferred (Rule 22a).
- **`Droppable`**: a prelude marker trait with no methods that no `impl`
  may define. `X: Droppable` holds exactly when `lin(X)` is false
  (Rule 22c). It is the bound a generic body writes to say "I drop a value
  of this type".
- **Deferred body**: the `block` — or the `{ expr; }` that the `expr ";"`
  form abbreviates — of a `defer` or `errdefer` statement (ch07
  `defer_stmt`/`errdefer_stmt`; Rules 23-23f).
- **`Shared`**: a marker trait with no methods and no runtime
  representation. `impl Shared for T {}` is accepted only when every field
  of `T` is `atomic[U]`, `imm`, or itself a type implementing `Shared`
  (Rule 21a); it is otherwise an ordinary trait, usable as a generic bound.

## Rules

1. Every parameter MUST declare exactly one convention.
2. A call site MUST mark a non-`let` argument: `&x` (inout), `move x`
   (sink), `&out x` (set); `let` carries no marker. `move` marks a place
   expression (binding or projection path); an rvalue argument (literal,
   call result) to a `sink` parameter carries no marker. Every move of a
   named place is thus written `move`, with exactly ONE exception (owner
   decision 2026-09-19, round 4): the receiver of a method call
   `x.m(args)` never carries a marker, whatever the convention of `self`
   (ch09 Rule 46), so when `m` resolves to a `sink self` method the call
   MOVES the place `x` implicitly. `(move x).m(args)` stays legal and
   means the same. An implicit receiver move is a move for every rule of
   this chapter — Rules 3, 4, 4a, 6-8, 12, 13 and 15a apply exactly as if
   `move x` had been written (use after move, a move inside a loop, a
   partial move out of a field, a move out of a `let` or `inout`
   parameter, a move of a place captured by a closure or structured
   `spawn`, are errors, or not, exactly as with the explicit form). The
   diagnostic a use-after-move MUST carry in that case is ch09 Rule 46's.
   In a qualified call (`T.m(move x)`, ch09 Rule 45) the receiver is an
   ordinary argument and is marked.
3. A `let` parameter MUST NOT be assigned to or moved from.
4. A `sink` parameter MUST be moved-from or deinitialized on every path,
   unless `Copyable`.
4a. Moves and liveness (the rule the implicit receiver move of Rule 2
   leans on; it applies identically to `move p` and to `p.m()` with `m` a
   `sink self` method). A move leaves the place `p` dead until an
   assignment `p = e;` re-initialises it. (a) *Use after move*: any use of
   a dead place, or of a path that has it as a prefix — a read, a second
   move, passing it by any convention, a method call on it — MUST be
   rejected. (b) *Loops*: a move, inside a `for`/`while`/`parallel` body,
   of a place declared outside that body MUST be rejected unless every
   path that reaches the next iteration re-initialises the place first;
   this is Rule 8 at the loop-head merge, stated here so that no reader
   has to derive it. (c) *Partial move*: a move whose place is a field or
   index projection (`move a.b`, `a.b.finish()`) MUST be rejected in v0.1;
   take the value apart with a pattern, or move the whole. (d)
   *Parameters*: a `let` parameter (Rule 3) and an `inout` parameter MUST
   NOT be moved from, even if reassigned afterwards; a `sink` parameter
   and a local MAY. (e) *Captures*: a closure body MUST NOT move a place
   it captures (a closure may be called more than once, so this is (b)
   again). A `spawn` statement's call is not a closure: in `spawn
   x.run();` the receiver move — implicit or written `(move x).run()` —
   IS the `move` capture that Rule 13 requires of an `iso` value, and the
   place is dead afterwards in the spawning task; sendability is judged
   exactly as for `spawn run(move x);`. A `Copyable` place is copied, never
   moved, so none of (a)-(e) applies to it (ch09 Rule 23). A deferred body
   (Rule 23) is NOT a closure and is exempt from (e): it runs at most once
   per exit and exactly one exit is taken, so it MAY move a place of an
   enclosing scope — which is what makes `defer v.deinit(&a);` the idiom
   for discharging a linear obligation (Rules 22d(iii), 23d).
5. A `set` parameter MUST be fully initialized on every return path.
6. Exclusivity is one forward dataflow pass per function over projection
   paths, no fixpoint, no interprocedural analysis; a callee's effect on an
   argument is exactly its declared convention.
7. Two simultaneous overlapping accesses MUST be rejected if either is
   `inout`, `sink`, or `set`. Two overlapping `let` accesses MUST be
   ACCEPTED (Decisions §1; owner decision 2026-09-19, round 5, D4: two
   read-only accesses cannot race, and forbidding them would outlaw
   `f(&x, &x)`-shaped calls that are plainly sound). **Note for the
   backend:** no-alias facts therefore never come from a `let` parameter.
   They come only from `inout`, `sink` and `set` and from the other four
   alias sources of ch05 Rule 5 (affine ownership, arena brand id,
   split-token provenance, SoA field identity — "parameter convention"
   being the first of its five); a `let` parameter MUST NOT be
   annotated `noalias` (or its IR equivalent) on the strength of its
   convention alone.
8. At a CFG merge every path MUST agree on each local's liveness;
   disagreement MUST be an error, resolved by explicit `consume x` /
   `discard x` (no drop flags). **Note (round 6).** This is what keeps
   linearity a property of the forward pass and not of a second analysis:
   because every path must already agree on liveness, a cleanup obligation
   (Rules 22-22i) is never "maybe outstanding", and the merge lattice gains
   no third element. An implementation MUST NOT introduce a "maybe live"
   state, a drop flag or a backward pass to accommodate linear values; for
   a linear local the resolution `discard x` is itself rejected (Rule
   22d), so the disagreement must be resolved by consuming on both paths.
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
19c. **Scope inheritance through a call** (round 6, O3; generalised by
    the round-6 verification). Rules 19-19a say what a scoped value may
    do; this rule says what the CALLER may conclude about a call's RESULT
    when a scoped value went in as an argument or as the receiver. A
    scoped value has a set of SOURCES — the places whose accesses Rule 19a
    extends; a value produced under Rule 19 has one, its designated
    parameter, and a capturing closure has its captures (Rule 19d). At a
    call whose argument `a` is scoped, let `D` be the declared type of the
    parameter `a` goes into (the receiver parameter included):
    (a) if `D` is a BARE type parameter `P` — a parameter of the callee, a
    parameter of its `impl`, or `Self` of a trait method — the call MUST
    be rejected unless BOTH of: no `inout` or `set` parameter of the callee
    has a declared type that mentions `P`, and the callee's `raises` type
    does not mention `P`. The call's result then keeps `a`'s sources iff
    the callee's DECLARED result type mentions `P` syntactically, before
    substitution; otherwise the result is an ordinary unscoped value.
    (a′) if `D` is not a bare type parameter and `a`'s type is `Copyable`
    (the callee may keep a COPY: a `Str`, a `Slice[T]`, a `fn`-typed value,
    a `Copyable` aggregate of these), or `a` is a capturing closure going
    into a `fn`-typed `D` (Rule 19d), the same two conditions apply with
    "mentions `P`" read as "CONTAINS `D`", and the result keeps `a`'s
    sources iff the declared result type contains `D`. *Contains*: `R`
    contains `D` iff `R`, descended through struct fields, enum payloads,
    tuple components and EVERY type argument (`Own`, `rawptr`, `Slice`,
    `Array`, `Option`, `fn` parameter and result types included), with
    arguments substituted and a per-head memo that stops at a cycle, has a
    subterm equal to `D` (ch09 Rule 9). It is the descent of Rule 22a with
    a different leaf test, and costs the same.
    (b) otherwise (`D` concrete or a type application, `a` not `Copyable`)
    the argument MAY be passed `let` or `inout` — Rules 19-19a then govern
    what flows back out, through a `scoped(p)` result and nothing else,
    because a non-`Copyable` value cannot be copied out of a `let` or
    `inout` parameter (Rules 3, 4a(d)) — and MUST NOT be passed `sink`. A
    concrete-typed `sink` parameter is the one place a scoped value could
    be stored away with no trace in the signature, so it is closed here
    rather than by inspecting the callee.
    (c) Rule 19a's extent, "the lexical scope of the binding that receives
    the scoped result", is extended to the two binding-less cases: a scoped
    value consumed within the expression that produced it has THAT
    EXPRESSION as its extent, and one used as the iterable of a `for` has
    THAT `for` STATEMENT.
    (d) A result that keeps sources from SEVERAL arguments keeps them all
    (`v.iter().zip(w.iter())`, `v.iter().map(|sink x| x + k)` keep `v` and
    `w`, or `v` and `k`): each source's access extends under Rule 19a to
    the receiving binding's scope, and the value is an ordinary local.
    Whether it may be RETURNED is Rule 19's question alone — every source
    must be a projection of the one parameter `scoped(p)` names — so a
    value with two parameter sources, or any local source, cannot be
    returned. Rule 19a's ban on storing a scoped value in a field or
    container applies to it as to any scoped value.
    *Why (a) and (a′) are decidable from signatures alone, with no
    interprocedural analysis.* The callee's body is checked once with `P`
    rigid (ch09 Rule 57), and the only things a body may do with a value
    of rigid type are: bind it, pass it by a convention, move it, store it
    in an aggregate, drop it, or hand it to a method of one of `P`'s
    bounds. Stored in an aggregate, it lives in a type that mentions `P`,
    because an aggregate is typed field by field. Passed on to another
    generic callee, this rule applies again, by induction on the call
    graph's depth at the definition. Handed to a bound's method, that
    method's signature mentions `P` only as `Self`, so the same clause
    governs. The remaining escape would be erasure, and ch09 Rule 10(c)
    rejects coercing a value of rigid or neutral-projection type to `dyn
    Tr`. So a value of type `P` reaches the caller only inside the result
    (which mentions `P`), inside an `inout`/`set` argument (banned here)
    or inside the error (banned here). For (a′) the argument is the same
    with "a type containing `D`" for "a type mentioning `P`": a `Copyable`
    value of concrete type `D` can be copied into a field only of a type
    that contains `D`, and a `fn`-typed value has no operation but a call,
    a copy and a store (ch09 Rules 7, 42). The one thing (a′) is not
    needed for is a scoped PROJECTION the callee takes of the parameter
    (`s.bytes()`, `self.items()`): that is scoped to the parameter inside
    the callee by Rule 19 and Rule 19a already forbids storing it there.
    *Cost.* One syntactic "mentions `P`" scan, or one memoised "contains
    `D`" descent, of the callee's declared signature, memoised per
    signature, and a source set on the call's result. No new type, no
    unification, no fixpoint: Rule 6's single forward pass is unchanged.
    *Consequence (round 6, O3).* This is the rule that makes iterator
    method chaining writable: `v.iter().map(f)` passes the scoped
    `SliceIter[i32]` as `sink self` of a trait method whose declared result
    `Mapped[Self, U]` mentions `Self`, so the result is scoped to `v`, and
    the field store inside the generic body is not the caller's concern.
    `v.iter().count()` returns `usize`, which mentions no parameter, so
    nothing stays scoped. `v.iter().map(|sink x| x + k)` keeps `v` and `k`
    ((a′) and Rule 19d: `Mapped[Self, U]` contains the `fn` type `f` went
    in through), so the closure over the local `k` can never leave the
    function inside the adaptor.
19d. **Closure captures** (round-6 verification; closes Open question 5).
    A closure captures each place of an enclosing scope that its body
    mentions by ACCESS — `let`, or `inout` when the body writes it or
    passes it `inout` — and never by move (Rule 4a(e)). A closure value
    that captures at least one place is a SCOPED value whose sources are
    its captured places together with the sources of every captured place
    that is itself scoped; a closure that captures nothing is an ordinary
    unscoped value, like a `fn` item. Each capture is an access under Rules
    6-7 whose extent is the closure value's extent under Rules 19a and
    19c(c): the lexical scope of the binding that holds the closure (or an
    earlier `discard`), the expression or `for` statement that consumes
    it, or, when the closure is an argument, whatever extent the call's
    result inherits by Rule 19c(a′). Consequences: a closure over a local
    can be RETURNED by no function (Rule 19 names parameters only) and
    stored in no field or container by the caller that wrote it (Rule
    19a); a closure over a `let` parameter `p` may be returned only under
    `scoped(p)`; coercing a capturing closure to its `fn` type (ch09 Rule
    10(b)) keeps its sources on the `fn`-typed value, and so does every
    copy of that value (`fn` types are `Copyable`, ch09 Rule 23). Inside a
    callee, a `fn`-typed parameter is an ordinary value — storing it in a
    field is legal there — because Rule 19c(a′) makes the CALLER account
    for what the callee may have kept. A linear place captured by a closure
    is still owed by the enclosing scope (Rule 22g).
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


22. **`Linear`, the declared base** (round 6, O1). `Linear` is a prelude
    marker trait with no methods and no runtime representation (ch09 Rule
    24). `impl Linear for T {}` MUST appear in the module that defines `T`
    (as for `Shared`, Rule 21a), and `T` MUST be a `struct` or `enum` named
    by its declaration, never a type parameter (ch09 Rule 18 already
    forbids a bare-parameter self type). The `impl` MAY have type, const
    and brand parameters and MUST NOT carry a bound on any of them (the
    kind marker `brand` of Rule 15d is a KIND, not a bound, and is written
    wherever the type takes a brand parameter):
    **whether a constructor is linear is a fact of the constructor, never
    of an instantiation** (ch09 Rule 59). `Own[T, A]` is linear by language
    rule, with no written `impl`. `Linear` MAY be used as a generic bound,
    where it restricts instantiation and adds no operation (ch09 Rule 24).
    Which std types declare it is ch10's (Rule 11 and the Definitions'
    list).
22a. **`lin`, the inferred propagation.** For a normalised type (ch09 Rule
    20), `lin(T)` is true iff one of: (a) `T`'s head has an `impl Linear`
    (found by ch09 Rule 12's lookup; by Rule 22 there are no bounds to
    check); (b) `T` is a `struct`, `enum` or tuple and some field, some
    payload component or some tuple component, with `T`'s arguments
    substituted, has `lin` true; (c) `T` is a rigid type parameter or a
    neutral projection that is not `Droppable` (Rule 22c). `lin` is false
    for every primitive, `()`, `never`, `Str`, `Slice[T]`, `Ref[T, A]`,
    `rawptr`, `Range[T]`/`RangeIncl[T]`, `mask`, `atomic[T]`, every `fn`
    and closure type, `dyn Tr`, `Arena[T, A]`, every allocator type and
    every root-capability type, and for `Array[T, N]` / `vector[T, N]` with
    non-linear `T` (Rule 22b). A qualifier (`iso`, `imm`, `secret`) does
    not change `lin`. *Cost and termination.* `lin` is a structural
    descent, memoised per (head, arguments), linear in the number of
    distinct subterms — the shape of ch09 Rule 20 — and it terminates
    because ch09 Rule 14 forbids an infinite type except through the
    indirections `Own`, `Ref`, `Arena`, `Slice`, `rawptr`, `fn` and `dyn`,
    into none of which `lin` descends (`Own` is linear by (a) without
    descending; the others are never linear).
22b. **Arrays and inline buffers.** `lin(Array[T, N])` = `lin(vector[T, N])`
    = `lin(T)`. A CONCRETE `Array[X, N]`, `vector[X, N]` or `atomic[X]`
    with `lin(X)` true MUST be rejected where the type is written or
    instantiated (ch09 Rule 11): an element can leave an array only by a
    partial move, which Rule 4a(c) forbids, so such a value could never be
    consumed and the obligation would be undischargeable by construction.
    In a GENERIC body `Array[T, N]` with a rigid `T` is well-formed and its
    values obey Rule 22c like any other rigid-typed value. The
    consequences for std's containers — `clear` and `deinit` moving to
    `T: Droppable` impl blocks, and `deinit_empty` for the rest — are ch10
    Rules 23-26.
22c. **Rigid types, and `Droppable`** (ch09 Rule 57's amendment).
    `Droppable` is a prelude marker trait that MUST NOT be implemented by
    any `impl`; writing one is an error. `X: Droppable` holds iff `lin(X)`
    is false. A rigid type parameter is `Droppable` iff its declared bounds
    include `Droppable`, `Copyable` (which implies it, Rule 22e) or
    `Iterator` (which implies it, ch09 Rule 21); a neutral projection `P.A`
    iff the bounds its trait declares for `A`, or the constraint entries on
    `P.A` in scope, do. Letting a value of rigid type go out of scope,
    `discard`ing it, matching it with `_`, or evaluating it as an
    expression statement MUST be rejected unless the type is `Droppable`
    (ch09 Rule 57's code); binding it, passing it by a convention, moving
    it, storing it in an aggregate and returning it stay available for
    every rigid type. **This is the conservative assumption**: a generic
    body that drops must SAY SO in its signature, so no error ever depends
    on an instantiation (ch09 Rule 59) and a generic parameter's linearity
    is knowable at the definition.
22d. **The obligation, and exactly what discharges it.** A live binding of
    linear type — a local, a `sink` parameter, a pattern binding; never the
    binding of a `with` block, which Rule 15a governs — carries a cleanup
    obligation. Exactly these discharge it, each of them a move of the
    WHOLE place under Rules 2 and 4a: (i) `move p` to a `sink` parameter,
    the implicit receiver move into a `sink self` method (Rule 2, ch09 Rule
    46), `return p` / `return move p`, the function body's tail value,
    `raise p`, `spawn f(move p);` and the receiver form `spawn p.run();`
    (Rule 4a(e)), the assignment `q = p;` or `q = move p;` (the obligation
    now lives on `q`), and use as a struct-literal field, a variant payload
    or a tuple component (the aggregate is linear by Rule 22a(b) and
    inherits the obligation); (ii) destructuring by a `match` whose arm
    binds EVERY linear component with `let n` — a `_`, an omitted `{ }`
    field (ch09 Rule 50's "omitted fields match anything") or a literal
    pattern facing a linear component is a drop and MUST be rejected;
    (iii) a `defer` or `errdefer` body that moves `p`, on exactly the exits
    that body runs on (Rule 23d(b)). **NOT consumption**, each of which
    MUST be rejected on a linear place: `discard p;` and `consume p;`, a
    `let` or `inout` pass, a copy (impossible, Rule 22e), a capture by a
    closure (Rule 22g), a coercion to `dyn` (Rule 22f), and **a trap** — a
    trap is an abort and runs nothing (ch02 Rule 7), so it never discharges
    an obligation and never has to.
22e. **`Copyable`.** `impl Copyable for T` MUST be rejected when `lin(T)`
    is true, and `X: Copyable` implies `X: Droppable`. ch09 Rule 23's
    built-in `Copyable` list contains no linear type (it already excludes
    `Own`).
22f. **Erasure.** A linear value MUST NOT be coerced to `dyn Tr` (ch09 Rule
    10(c), beside "brand-mentioning or scoped"): the obligation would
    become invisible to every later rule. Neither may a value of rigid or
    neutral-projection type, for the reason Rule 19c(a) gives.
22g. **Containers, enum payloads, closures, `spawn` and `with` blocks.** A
    linear value inside a container, a struct field, an enum payload or a
    tuple makes that aggregate linear (Rule 22a(b)), and the aggregate's
    own consumption discharges the whole; an `Array`/`vector`/`Buffer` of
    linear elements does not exist (Rule 22b), and what a growable
    container does with linear elements is ch10 Rules 23-26. A closure
    captures by ACCESS and MUST NOT move a place it captures (Rule 4a(e)),
    so a closure never holds an obligation, `lin` of a closure type is
    false, and a linear local captured by a closure is still owed by the
    enclosing scope after the closure's last use. A structured `spawn`
    consumes by `move` (Rule 13), and the callee's `sink` parameter carries
    the obligation inside the task, where Rule 4 applies as usual. A
    `with arena` / `with allocator` block is a scope for Rule 22h; its
    binding is live for that block's own deferred bodies (Rule 23d(f)), so
    `defer v.deinit(&a);` INSIDE the block is the idiom, and Rule 15
    already guarantees that no brand-mentioning linear value leaves it.
22h. **The scope-exit check.** At every point where control leaves a scope
    — a block's `}` (a function body, a `with`, a `parallel`, a loop body,
    an arm block, a closure body), `return`, `raise`, the error exit of a
    `?` (ch02 Rule 16), and `break`/`continue`, which leave the loop body's
    scope and every scope nested inside it — and AFTER the pending
    `defer`/`errdefer` bodies of the scopes being left have been accounted
    for (Rule 23d(b)), every binding declared in those scopes that is live
    and of linear type MUST have been consumed; otherwise the diagnostic of
    Rule 22i. The same error is reported for a linear TEMPORARY — an
    expression statement whose value is linear, `let _ = e;`, a `_`
    component of a tuple `binding`, a call result that is not bound — for a
    `var` of linear type ASSIGNED while live ("this overwrites an
    unconsumed value"), and for a `sink` parameter of linear type, whose
    Rule 4 obligation this diagnostic supersedes (Rule 4 stays as it is for
    every other type). The check reads the live set Rule 6 already carries,
    restricted to the scopes being left; it adds no dataflow state (Rule 8's
    note).
22i. **The diagnostic** (normative content, not wording). It MUST carry:
    the value's name, or "the result of `f()` at L:C" for a temporary; its
    type as ch09 Rule 20 displays it; the scope that is being left; the
    exit's kind and location (the `}` of the block opened at L:C, the
    `return` at L:C, the `?` at L:C, the `raise` at L:C, the `break` at
    L:C); and the CONSUMERS. For a type whose head is declared linear the
    consumers are every `sink self` receiver method of that head plus every
    function or method declared in the head's defining module that has a
    `sink` parameter of a type with that head, excluding `@unsafe`
    declarations — for `Vec[i32, heap]` that is `Vec.deinit(&<allocator>)`,
    for `Own[i64, a]` it is `Allocator.deinit`, written `a.deinit(move x)`.
    For an aggregate that is linear by inference the diagnostic MUST name
    the linear field or component and say "destructure it with a pattern
    that binds them, or move the whole". For a rigid type it MUST say "`T`
    may be linear: bound it `Droppable`, or consume it". Illustrative text,
    not normative: "`v` of linear type `Vec[i32, heap]` is not consumed on
    the path leaving `main`'s body at the `?` at 14:5; consume it with
    `Vec.deinit(&<allocator>)`, or attach the cleanup with `defer` or
    `errdefer`".
23. **`defer` and `errdefer`: placement** (round 6, O2; the syntax is ch07
    `defer_stmt`/`errdefer_stmt`). A `defer` or `errdefer` statement is a
    statement of the `block` `B` that DIRECTLY contains it — any block: a
    function body, a loop body, an `if` or `match` arm block, a `with`
    block, a `parallel` block, a closure body, a `comptime` block. Its
    *body* is the statement's `block`, the `expr ";"` form meaning exactly
    `{ expr; }`. The statement itself has type `()` and its body is checked
    against `()` (ch09 Rule 31).
23a. **When a `defer` body runs.** The body runs when control leaves `B` by
    ANY exit — reaching `B`'s `}` by fall-through or a tail value,
    `return`, `raise`, the error exit of a `?`, a `break` or a `continue`
    that leaves `B` — PROVIDED the `defer` statement was executed on that
    path, which, `B` being a statement sequence, means it textually
    precedes the exit point in `B`. All bodies pending in `B` run in
    REVERSE textual order; then the exit continues into the enclosing
    block, whose pending bodies run next, and so on outward. On `return
    e;`, `raise e;` and a tail value, `e` is evaluated, and moved into the
    result, BEFORE any body runs; a body can neither read nor change the
    result. There is NO runtime registration and no runtime stack: the set
    of bodies at each exit is static, and the lowering is the inlining of
    the pending bodies at that exit (an implementation MAY emit one copy
    and jump to it; the behaviour is the same).
23b. **When an `errdefer` body runs.** An `errdefer` body runs on the ERROR
    exits of `B` (ch02 Rule 16) that follow its statement, and NEVER on a
    normal exit. `defer` and `errdefer` bodies pending in `B` run
    interleaved, in one reverse textual order. An `errdefer` statement
    after which `B` has NO error exit — the function does not `raises`,
    or every `?` and `raise` of `B` precedes the statement — MUST be
    rejected ("`errdefer` at L:C can never run: no error exit follows
    it"); the set of error exits is syntactic (ch02 Rule 16), so this
    costs nothing, and it is the diagnostic for the common mistake of
    writing the `errdefer` AFTER the fallible call it was meant to cover
    (Rule 22h then also reports the linear value leaked at that `?`).
23c. **What a body may contain.** A body MUST NOT contain `return`,
    `raise`, `?`, or a `break`/`continue` whose target loop lies outside
    the body (a loop written INSIDE the body may use them freely). A call
    to a `raises` function inside a body MUST carry an `else |e| { }`
    handler that neither `raise`s nor `return`s (ch02 Rule 5): it yields
    the success value or traps. The reasons: on a normal exit there is
    nothing to attach an error to; on an error exit a second error would
    have to replace the first or be lost; and a `return` from a body would
    silently turn an error exit into a success. Bodies MAY NEST: a `defer`
    written inside a body is a statement of that body's block and runs when
    that block exits.
23d. **Captures, ownership and consumption.** A body mentions places of the
    enclosing scopes. It is typed once, and its ownership effects are
    summarised once, as a map from place to strongest access (`let` <
    `inout` < move); the summary is applied at each exit where the body
    runs. (a) Every place a body mentions MUST be live at every exit at
    which that body runs — for `defer`, every exit of `B` after the
    statement; for `errdefer`, every error exit after it — and a move of
    such a place between the statement and such an exit is Rule 4a(a)'s
    use-after-move, reported as "`p` is moved at L:C but the `defer` at
    L':C' still needs it". (b) A body that MOVES a place `p` — a `sink`
    argument, an implicit receiver move, `move p` — is a *deferred
    consumption*: `p` stays live in `B` after the statement and may be read
    and passed `inout` as usual, and at each exit where the body runs `p`
    is moved by it, which discharges `p`'s obligation (Rule 22d(iii)) on
    exactly those exits. So `defer p.deinit(&a);` consumes on every exit,
    while `errdefer p.deinit(&a);` consumes on the error exits only and the
    normal exits must consume `p` some other way — typically `return move
    p;`, which is legal precisely because the `errdefer` does not run
    there. (c) A body's `let`/`inout` accesses are NOT accesses during `B`:
    they are accesses AT THE EXIT POINT. Without this, `defer
    v.deinit(&a); v.push(&a, x)?;` would be a Rule 7 conflict, which is the
    opposite of the intent. (d) A body in a loop's block that moves a place
    declared OUTSIDE the loop is Rule 4a(b)'s move inside a loop and is
    rejected unless every path to the next iteration re-initialises the
    place; this falls out of (b) and needs no separate rule. (e) A body may
    capture nothing a closure could not, but it is NOT a closure: it runs
    at most once per exit and exactly one exit is taken, so unlike a
    closure it MAY move (Rule 4a(e)'s exemption). (f) The binding of a
    `with` block, and every `let`/`inout`/`sink` parameter of the enclosing
    function, is live for the bodies of its own block's exits; an arena or
    allocator value dies only after its block's bodies have run.
23e. **Loops, `main`, and `comptime`.** The body block of `for`, `while`,
    `parallel for` and `simd for` is exited at the end of every iteration
    and on `break`/`continue`, so a `defer` written inside it runs once per
    iteration; a `defer` written outside the loop is unaffected by
    iterations. `main`'s bodies run as part of `main`'s exit, before the
    runtime does anything of ch02 Rule 17. Inside a `comptime` block the
    semantics are identical under the FMIR interpreter (ch04 Rule 11);
    there is no special case.
23f. **Traps.** A trap runs NO deferred body, and a trap is not an exit:
    ch02 Rule 7 states it and states the consequence. Nothing in a program
    or in std MAY depend on a deferred body running on the abnormal path.

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


```fors
needs { };

// A linear `Vec` must be consumed on EVERY path (Rules 22, 22d, 22h).
// `defer` attaches the consumption once, and it runs on the `?`'s error
// exit as well as on the normal one (Rules 23a, 23d(b)).
fn sum_all[A: brand, L: Allocator[A]](inout a: L, let xs: Slice[i32])
    -> i32 raises AllocError
{
    var v: Vec[i32, A] = Vec.new();
    defer v.deinit(&a);                 // deferred consumption, Rule 22d(iii)
    for x in xs {
        v.push(&a, x)?;                 // legal: the defer's accesses are at the exit
    }
    var acc: i32 = 0;
    for y in v.iter() {
        acc = acc + y;
    }
    return acc;
}

// `errdefer` runs only on the error exits (ch02 Rule 16), so the normal
// exit may still hand the value to the caller (Rules 22d(i), 23b).
fn build[A: brand, L: Allocator[A]](inout a: L) -> Vec[i32, A] raises AllocError {
    var v: Vec[i32, A] = Vec.new();
    errdefer v.deinit(&a);
    v.push(&a, 1)?;
    v.push(&a, 2)?;
    return move v;
}
```

```fors
needs { };

fn double(sink x: i32) -> i32 { return x * 2; }
fn small(let x: i32) -> bool { return x < 10; }

// `v.iter()` is scoped to `v`; every adaptor's declared result type
// mentions `Self`, so the whole chain stays scoped to `v` (Rule 19c(a)),
// and `count`'s `usize` mentions nothing, so the extent ends here.
fn count_small[A: brand](let v: Vec[i32, A]) -> usize {
    return v.iter().map(double).filter(small).take(3).count();
}

// A borrowed source is chained through `by_ref`: the adaptors take
// `sink self`, and an `inout` parameter MUST NOT be moved from (Rule 4a(d)).
fn take_two[I: Iterator](inout it: I) -> usize {
    return it.by_ref().take(2).count();
}
```

```fors
needs { };

fn note(let tag: Str) { }

// A `defer` inside a loop body runs at the end of every iteration and on
// `continue`/`break` (Rule 23e); the bodies pending in one block run in
// reverse textual order (Rule 23a), so "later" precedes "end".
fn ticks(let n: usize) {
    for i in 0 ..< n {
        defer note("end");
        defer note("later");
        if i == 0 { continue; }
        note("body");
    }
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
- **Linearity as a keyword or qualifier** (`linear struct S { }`) — a new
  reserved word for what a marker trait already expresses; the owner asked
  for none if one suffices, and `Shared` (Rules 21-21d) is the precedent.
- **An attribute naming the consumer** (`@linear(by: X.deinit)`) — it makes
  the resolver resolve a deferred method path, or carry an unchecked
  string; Rule 22i derives the consumer list from signatures instead.
- **Declared propagation on the `Shared` model** (`impl[T: Linear] Linear
  for Option[T] {}` required on every generic aggregate) — forgetting it is
  a silent leak, and it is boilerplate on every `struct Pair[T]`. `Shared`
  is opt-in safety and linearity is opt-out-impossible safety, so the
  polarities differ: the base is declared (Rule 22) and the propagation
  inferred (Rule 22a).
- **Inferring the base from a naming convention** ("has a `sink self`
  method called `deinit` or `close`") — a convention is not a rule.
- **Rigid types non-linear by default with a positive `T: Linear` bound
  meaning "the callee promises to consume"** — it inverts what a bound is
  (an upper bound on what may be passed) and needs a per-instantiation
  check, which ch09 Rule 59 forbids.
- **A runtime trap on a rigid drop** (ch10 Rule 11c's earlier answer) — the
  owner's decision is "the compiler MUST reject"; Rule 22c makes the
  generic case static.
- **Consumption by `discard`** — it would make explicit allocators
  decorative; the ban of ch10 Rule 11 is kept (Rule 22d).
- **Go-style function-scoped `defer` with a runtime stack** — it needs a
  runtime list and makes a `defer` in a loop accumulate; block scope (Rule
  23) needs no runtime state at all.
- **`errdefer |e| { }` binding the error** — nothing in v0.1 inspects the
  error during cleanup; liftable later without breaking accepted code.
- **Allowing `?` inside a deferred body with "first error wins"** — it
  hides errors; Rule 23c requires a handler instead.
- **A "maybe live" merge element / drop flags** for linear values — Rule 8's
  note; it would break the one-pass property and the no-flags promise.

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
11. Owner decision 2026-09-19, round 4: `x.finish()` on a `sink self`
   method moves `x` implicitly (Rule 2's single exception; typing and the
   required diagnostic are ch09 Rule 46, whose conformance list carries
   the tests). Alternative `(move x).finish()` as the only spelling was
   rejected by the owner; it remains legal.
12. Round-4 verification: Rule 4a added. The chapter owned "destructive
   moves" but no rule said that a use after a move, a move in a loop, a
   partial move, a move out of an `inout` parameter or a move of a
   captured place is an error; an implicit move (decision 11) cannot lean
   on unwritten rules. Conservative v0.1 choices, each liftable without
   breaking accepted code: no partial moves (4a(c)); no move out of an
   `inout` parameter even with a refill (4a(d)); no moving closure
   captures (4a(e)). `spawn x.run();` counts as the `move` capture of
   Rule 13, because the owner made the receiver move mean exactly `(move
   x).run()`. Tests: ch09's Rule 46 list (tests/conformance/09-types).

13. Round 6 (2026-09-20), O1. `Linear` is a DECLARED base and `lin` an
   INFERRED propagation (Rules 22, 22a): the alternative polarities are in
   Rejected alternatives. `Droppable` is a structural marker with no impls
   (Rule 22c) rather than a positive `Linear` bound, so that a generic body
   states what it drops and no error depends on an instantiation (ch09 Rule
   59). Arrays, `vector`s and `atomic`s of linear elements are ill-formed
   (Rule 22b) rather than merely awkward, because Rule 4a(c) forbids the
   partial move that would be the only way to consume an element. A trap
   discharges nothing (Rule 22d), which is the honest reading of ch02
   Rule 7 and the reason std promises no cleanup on the abnormal path.
14. Round 6, O2. `defer`/`errdefer` are BLOCK-scoped and statically
   inlined at exits, with each body typed and summarised once (Rules 23,
   23a, 23d): no runtime registration, no allocation, no list. The one
   subtle rule is 23d(c) — a body's accesses happen AT THE EXIT, not at the
   `defer` statement; the natural implementation (open the access at the
   statement) would make `defer v.deinit(&a); v.push(&a, x)?;` a Rule 7
   exclusivity conflict, which is exactly the program the feature exists
   for. A body is exempt from Rule 4a(e) (Rule 23d(e)) because, unlike a
   closure, it runs at most once and exactly one exit is taken.
15. Round 6, O3. Rule 19c is an OWNERSHIP rule, not a typing one: ch09's
   method lookup already finds a provided method of `Iterator` for a
   concrete, rigid or adaptor receiver, and ch09 Rules 38-41 already bind
   `Self` before any argument is visited. What was missing was what the
   CALLER may conclude when a scoped value goes into a bare type parameter
   — so ch10's free-function adaptors were a workaround for a gap in this
   chapter, not for a gap in ch09. No blanket impl is introduced anywhere.

16. Round 6, implementation stage. The corpus directory `01-ownership`
   gained a resolver-view gate of its own
   (`ch01_ownership_corpus_resolver_view` in
   `crates/fors-resolve/tests/conformance.rs`), matching ch09's and ch10's:
   until a type checker exists, every `check-ok` and `check-error` test
   here MUST be resolver-CLEAN, because this chapter's codes are the
   checker's. Four tests written in rounds 1-3 whose shape is a NAME error
   as well as an ownership one (`arena_brand_nonescape_rejected`,
   `brand_field_requires_param`, `shared_blanket_impl_rejected`,
   `shared_impl_outside_defining_module_rejected`) are listed in that test
   rather than asserted; they are ch08's to move or retire, not round 6's.

17. Round-6 verification. (a) Rule 19c's "two scoped sources → reject
   the call" was replaced by a SOURCE SET (Rule 19c(d)): the adaptor
   idiom `v.iter().map(|sink x| x + k)` has two sources (`v` and the
   capture `k`) and must be a legal local, and Rule 19 already decides
   what may be returned. (b) Open question 5 was not optional: with
   `Mapped` storing its callable, `return v.iter().map(|sink x| x + k)`
   under `scoped(v)` would have carried a closure over the dead local `k`
   out of the function. Rule 19d makes a capturing closure a scoped value
   with its captures as sources, and Rule 19c(a′) makes the caller account
   for a `fn`-typed (or any `Copyable`) argument the callee may keep,
   through a "contains `D`" descent of the declared result; the same
   clause closes Open question 6 (a `Copyable` scoped value through a
   concrete `let` parameter). The alternative — treating a `let`
   parameter as scoped inside the callee — was rejected because it would
   have rejected `Mapped { src: self, f: f }` in the very body O3 needs.
   (c) An `errdefer` with no error exit after it is an error (Rule 23b).
   (d) The migration "hold `Option[X]`" for an array of linear elements
   was wrong: `Array[Option[X], N]` is linear by Rule 22a(b) and ill-formed
   by Rule 22b; the entry now says what to do instead.

## Closed by owner decision 2026-09-20, round 6

- **O1 — linear types.** The compiler MUST reject any path on which a
  value carrying an outstanding cleanup obligation leaves its scope
  unconsumed. Mechanism: the prelude marker `Linear` for the declared base
  (Rule 22), the structural function `lin` for field-, payload- and
  tuple-wise propagation (Rule 22a), the structural marker `Droppable` for
  the drop side and for rigid types (Rule 22c), and the existing forward
  pass of Rules 6 and 8 for the check (Rule 22h). No new keyword: the
  owner asked for none if one sufficed, and `Shared` was the precedent.
  Linearity is decided from SIGNATURES only and never per instantiation
  (Rules 22, 22c). A trap consumes nothing (Rule 22d). What this forbids
  that was legal is listed under "What round 6 forbids" below.
- **O2 — `defer` and `errdefer`.** Both words, block-scoped, reverse
  order, `errdefer` on error exits only (Rules 23-23f; grammar in ch07,
  error exits in ch02 Rule 16). A deferred body MAY be a value's last use
  and MAY consume it (Rule 23d(b)), which is how cleanup is written once
  instead of on every `?` path.
- **O3 — iterator method chaining.** `it.map(f).take(3)` works with the
  single addition of Rule 19c (plus ch09 Rule 10(c)'s amendment); the
  std surface it enables is ch10 Rules 32-35. Method lookup, provided
  methods, generic-argument determination and projections are UNCHANGED,
  and blanket impls are still not in the language.

### What round 6 forbids that was legal before it

Each entry names the migration; the corpus and std stages work from this
list and from ch09's and ch10's copies of it.

1. Every path on which a value of a linear type — `Vec`, `Map`, `String`,
   `Own`, `Block`, `fs.File`, `fs.Entries`, `net.Conn`, `net.Listener`,
   `proc.Child` — goes out of scope unconsumed; in particular EVERY `?`
   written after one is created, since the error exit is a scope exit
   (Rule 22h). *Migration*: add `defer x.deinit(&a);` (consume on every
   exit) or `errdefer x.deinit(&a);` with `return move x;` (hand it to the
   caller on the normal exit).
2. `Array[X, N]`, `vector[X, N]`, `atomic[X]` and `Buffer[X, N]` with a
   linear `X` (Rule 22b) — and, since `lin(Option[X])` is `lin(X)` (Rule
   22a(b)), `Array[Option[X], N]` is just as ill-formed. *Migration*: a
   fixed number of linear values is a struct with one field each (the
   aggregate is linear and is consumed by destructuring, Rule 22d(ii)); a
   variable number lives in a `Vec[X, A]` or `Map[K, X, A]`, emptied by
   `pop`/`remove` and released by `deinit_empty` (ch10 Rule 11c).
3. Dropping a value of rigid type in a generic body with no `Droppable`,
   `Copyable` or `Iterator` bound (Rule 22c). *Migration*: add the bound,
   or return/move the value instead of dropping it.
4. `discard p;` and `consume p;` on a linear place, and `_`, an omitted
   `{ }` field or a literal pattern facing a linear component (Rule 22d).
   *Migration*: bind every linear component with `let n` and consume it.
5. `impl Copyable for T` with `lin(T)` (Rule 22e); coercing a linear, a
   rigid or a neutral-projection value to `dyn Tr` (Rule 22f, ch09 Rule
   10(c)). *Migration*: take `dyn Tr` as a parameter instead.
6. Passing a non-`Copyable` scoped value to a `sink` parameter of
   CONCRETE type (Rule 19c(b)); passing a `Copyable` scoped value, or a
   capturing closure, to a callee whose `inout`/`set` or `raises` type
   contains the parameter's type (Rule 19c(a′)); RETURNING a value that
   keeps two sources — `v.iter().zip(w.iter())`, `v.iter().map(|sink x|
   x + k)` — or a closure over a local (Rules 19, 19c(d), 19d). Such
   values are legal as locals. *Migration*: consume the value where it
   is, or own one of the two sources.
7. The free-function adaptor and consumer calls of ch10's old Rules 34-35
   (`mem.map(&it, f)`, `mem.count(move k)`), which are deleted.
   *Migration*: the method chain, `it.map(f).count()`.
8. The identifiers `defer` and `errdefer` (ch07). No occurrence exists in
   the spec, `std/` or `tests/conformance`, so nothing migrates.

## Closed by owner decision 2026-09-19, round 5

- **D4 — overlapping `let`/`let` accesses are accepted.** Open question 1
  closed as drafted (Rule 7): two read-only accesses cannot race, and
  forbidding them would outlaw `f(&x, &x)`. The cost is stated where the
  backend will look for it: a `let` parameter yields no no-alias fact
  (Rule 7's note; ch05 Rule 5's other four sources are unaffected).
- **D4 — the self-referential arena header is kept.** Open question 3
  closed as drafted: `with arena nodes: Arena[Node[nodes]]` stays legal
  (Rule 15, 15d), so a node type that links to its siblings can take the
  brand of the arena being introduced. No alternative spelling is
  reserved; std's tree/graph containers may rely on this form.
- **D5 — allocation is explicit and is not authority** (recorded for the
  next milestone; std is NOT designed here). Every heap-allocating std
  type MUST take an EXPLICIT allocator VALUE, Zig-style and branded per
  PLAN R2 (`Own[T, A]`, `with allocator`, Rules 15-18): there is no
  default global allocator and no ambient allocation anywhere in the
  language or std, and the root heap arrives as a `main` parameter (ch04
  Rule 21's list, which the std surface chapter will extend with its
  type). Allocation is not authority: no `needs` entry exists or will
  exist for it (ch04).

## Open questions for the owner

1. ~~Confirm/override Rule 7's default (allow vs. forbid overlapping
   `let`/`let`) — your call; affects backend aliasing facts.~~ Closed by
   owner decision 2026-09-19, round 5 (D4): overlapping `let`/`let` is
   ACCEPTED; see Rule 7 and the closed-decision section above.
2. Confirm dropping `recover`, vs. reserving it for a future qualifier.
3. ~~Self-referential element types: Rule 15 lets the `with` header name
   its own binding as a brand (`with arena nodes: Arena[Node[nodes]]`),
   because a node that links to siblings must take the brand (Rule 15d).
   Drafted as allowed; confirm, or choose another spelling before std's
   tree/graph containers are written.~~ Closed by owner decision
   2026-09-19, round 5 (D4): kept exactly as drafted.
4. Rule 4a's three conservative bans (partial moves, moves out of an
   `inout` parameter with a refill, moving closure captures). Recommended:
   keep for v0.1; each needs per-field liveness or a call-once closure
   kind, neither of which v0.1 has.
5. ~~**Closure capture extent** (round 6).~~ Closed by the round-6
   verification: Rule 19d (drafting decision 17). Original text: Rule 19c(a)'s soundness argument
   assumes a closure cannot carry a value of rigid type out of the scope
   it captured it from; this holds if a capture is an ACCESS whose extent
   is the lexical scope of the closure value, which is what Rule 4a(e)
   implies but no rule states. Recommended: state it — "a closure's
   captures are accesses under Rules 6-7 whose extent is the lexical scope
   of the closure value" — as an editorial clarification. The conformance
   test `closure-returned-with-local-capture-rejected` settles whether the
   chapter as written already rejects the escape; if it does not, this
   clarification is a prerequisite for Rule 19c, not an optional tidy.
6. ~~**A `Copyable` scoped value through a CONCRETE `let` parameter**~~
   Closed by the round-6 verification: Rule 19c(a′) (drafting decision
   17); `scoped-copy-into-field-via-let-param-rejected` is now the rule's
   test. Original text: `fn keep(let s: Str) -> Holder { return Holder
   { s: s }; }` called with a scoped `Str` yields an UNSCOPED `Holder`;
   Rule 19c(b) does not close it, because the parameter is `let`, not
   `sink`, and Rule 19a's ban on storing a scoped value in a field is
   written from the caller's side. Independent of round 6 and older than
   it. Recommended: treat a `let` parameter's value as scoped to that
   parameter inside the body, so the field store is rejected where it is
   written; the test is `scoped-copy-into-field-via-let-param-rejected`.
7. **`errdefer |e| { }`** binding the raised error in the cleanup body
   (Rule 23b). Recommended: not in v0.1 — nothing needs it, and it is
   addable without breaking accepted code.

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

Round 6 (Rules 19c, 22-22i, 23-23f). All in `tests/conformance/01-ownership/`
unless a chapter is named; every `-rejected` name expects a `check-error`
whose `detail` starts with the code of the rule named beside it, and every
one of them is a test on which `fors check` (the resolver) MUST stay
silent, since no type checker exists yet.

*Linearity, the obligation (R22h, R22i)*:
`linear-local-dropped-at-block-end-rejected`,
`linear-local-dropped-at-return-rejected`,
`linear-local-dropped-at-question-rejected` (the `detail` names the `?`),
`linear-local-dropped-at-break-rejected`,
`linear-temporary-expression-statement-rejected`,
`linear-let-underscore-rejected`, `linear-var-overwritten-rejected`,
`linear-sink-parameter-unconsumed-rejected`,
`user-linear-type-diagnostic-names-consumer-rejected` (the `detail`
carries value, type, exit and `Res.close`).

*Linearity, what consumes (R22d)*: `linear-consumed-by-sink-call-accepted`,
`linear-consumed-by-return-accepted`,
`linear-consumed-by-implicit-receiver-move-accepted`,
`linear-consumed-by-struct-literal-then-aggregate-rejected` (the aggregate
inherits the obligation), `linear-aggregate-destructured-accepted`,
`linear-match-underscore-rejected`, `linear-match-omitted-field-rejected`,
`linear-option-matched-accepted`, `linear-consume-rejected`,
`linear-discard-rejected`, `linear-in-loop-reinit-accepted`,
`linear-in-loop-consumed-once-rejected` (R4a(b)),
`linear-field-partial-move-rejected` (R4a(c)),
`linear-captured-by-closure-still-owed-rejected` (R22g),
`linear-spawn-move-accepted`, `linear-with-block-exit-rejected`,
`linear-with-block-defer-accepted`, `linear-trap-does-not-consume-rejected`.

*Linearity, declarations and types*: `linear-impl-with-bound-rejected`
(R22), `linear-impl-outside-defining-module-rejected` (08-names, N0021),
`linear-array-element-rejected` (09-types, R22b),
`linear-vector-element-rejected` (09-types, R22b),
`linear-buffer-element-rejected` (10-std, R22b),
`linear-copyable-impl-rejected` (09-types, R22e),
`linear-to-dyn-rejected` (09-types, R22f),
`droppable-impl-rejected` (09-types, R22c),
`rigid-drop-without-droppable-rejected` (09-types, T0057),
`rigid-drop-with-droppable-accepted`, `rigid-drop-with-copyable-accepted`,
`rigid-iterator-drop-accepted` (ch09 R21's implication).

*Scope inheritance (R19c)*:
`scoped-through-generic-sink-result-scoped-rejected` (the result outlives
its source), `scoped-through-generic-sink-consumed-accepted`,
`scoped-into-concrete-sink-rejected` (R19c(b)),
`scoped-through-generic-inout-param-rejected` (R19c(a)'s `inout` clause),
`scoped-through-generic-raises-rejected`,
`scoped-through-generic-sink-returned-under-scoped-accepted` (R19),
`zip-two-scoped-sources-rejected` (R19c(d), R19: two sources, returned),
`zip-two-scoped-sources-local-accepted` (R19c(d)),
`zip-scoped-and-owned-accepted`,
`scoped-rvalue-extent-is-the-statement-accepted` (R19c(c)),
`scoped-rvalue-extent-is-the-for-accepted`,
`adaptor-chain-for-mutates-source-rejected` (R19c(c), R7),
`scoped-copy-into-field-via-let-param-rejected` (R19c(a′)),
`closure-returned-with-local-capture-rejected` (R19d, R19),
`closure-capture-keeps-local-in-chain-accepted` (R19d, R19c(d)),
`closure-capture-in-chain-returned-rejected` (R19d, R19: the closure over
the local `k` would leave inside the adaptor).

*`defer`/`errdefer` flow (R23-23f)*:
`defer-consumes-linear-on-all-exits-accepted`,
`errdefer-consumes-on-error-exit-accepted` (`return move v;` on the normal
exit), `errdefer-normal-exit-unconsumed-rejected`,
`defer-place-moved-before-exit-rejected` (R23d(a)'s diagnostic),
`defer-inout-use-after-defer-accepted` (R23d(c)),
`defer-in-loop-moves-outer-rejected` (R4a(b)),
`defer-in-loop-per-iteration-accepted`, `defer-return-inside-rejected`,
`defer-raise-inside-rejected`, `defer-question-inside-rejected`,
`defer-break-outer-loop-rejected`, `defer-inner-loop-break-accepted`,
`defer-handler-inside-accepted` (R23c, ch02 R5),
`defer-with-block-allocator-live-accepted` (R23d(f)),
`defer-in-closure-body-accepted`, `defer-nested-body-accepted`,
`errdefer-and-defer-interleaved-reverse-order-accepted` (R23b),
`errdefer-without-error-exit-rejected` (R23b: no error exit follows),
`errdefer-after-fallible-call-rejected` (R23b, R22h: the `?` before it
leaks and the statement can never run),
`linear-enum-payload-one-arm-unconsumed-rejected` (R22h at the arm's
`}`).

*`defer`/`errdefer` behaviour* (`run-ok`, stdout compared;
`02-failure` holds the `run-error` ones): `defer-reverse-order-run-ok`
(prints `3 2 1`), `defer-runs-on-return-run-ok`,
`errdefer-skipped-on-return-run-ok`, `defer-per-iteration-run-ok`,
`defer-result-evaluated-first-run-ok`, `defer-nested-scope-order-run-ok`
(inner block's bodies, then the outer's), `defer-not-run-on-trap`
(10-std; `trap` kind; the marker goes to `Stderr`, since ch10 Rule 40(b)
may lose buffered `Stdout` bytes).
