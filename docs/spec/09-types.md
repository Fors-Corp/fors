# Chapter 9: Types, traits, generics and the typing judgements

## Status

Draft, M1, 2026-09-19. Type checking is a phase of its own: it runs after name
resolution (ch08) on one declaration at a time and consumes only that
declaration's CST, the resolver's bindings, and the *signatures* of the
declarations it mentions. Implements PLAN "Surface": generics in `[...]`,
exactly two judgements, no solver, no overloading, no implicit conversions, a
closed operator-trait set. Diagnostic codes `T00nn` equal the rule numbers;
tests cite `09.Rk`.

Round 4 (owner decisions 2026-09-19, applied here): unsuffixed integer
literals default to `i32`; operator traits are homogeneous; traits have full
associated types (Rules 16-20, 61-62), which REPLACE the draft's
"self-determined traits" (old Rule 20) and "bound propagation" (old Rule 38
paragraph); a `sink self` receiver moves its place implicitly (Rule 46).
Numbering: no rule was renumbered. Rule 20 was replaced in place (it is now
the normalisation rule) and two rules were added at the end as section J
(Rules 61-62), so every older citation `09.Rk` still points at the same
subject. The round-3 forms (`let n` in patterns, `use a.b as c;`, a local may
shadow a prelude name) are in ch07/ch08 and are used below. Every example is
derived from ch07's productions.

## Scope

Owns exclusively: the type universe and primitive sizes; type equality; the
closed coercion list; well-formedness; generic-parameter kinds; trait and
`impl` rules including overlap; associated types, projections, their
normalisation, and constraint entries; the closed operator-trait table; `Copyable`;
`synth` and `check` for every expression, statement and pattern form;
generic-argument determination; member lookup (the deferred segments of ch08
Rules 16, 22); exhaustiveness; what a generic body may do with a parameter; the
signature as the only inter-declaration interface. Not owned: see the table
"Not owned by this chapter".

## Definitions

- **synth(e) = T**: `e` is typed with no expected type and yields `T`.
- **check(e, T)**: `e` is typed against a complete expected type `T`. Which
  syntactic positions are CHECK positions is ch03 Rule 25.
- **Projection**: the type `P.A`, the associated type `A` (of one trait among
  `P`'s bounds) at `P` (Rule 61). **Neutral projection**: a projection whose
  head is rigid; it is an opaque type (Rule 20).
- **Complete type**: a type that, after substituting what the call being typed
  has bound so far and normalising (Rule 20), mentions no undetermined generic
  parameter of that call. A generic parameter of the *enclosing* declaration
  is a rigid, opaque type and is complete, and so is a neutral projection.
- **Head**: the outermost constructor of a type after stripping qualifiers: a
  nominal item, a primitive, `tuple/n`, `fn`, `dyn Tr`, a rigid parameter, or
  a neutral projection.
- **One-way match** `match(P, A)`: `P` may mention unbound parameters of one
  call, `A` is complete. Walk both in lockstep; an unbound parameter in `P` is
  bound to the facing subterm of `A`; a bound parameter, or any constructor,
  MUST equal the facing subterm (Rule 9). Matching does not look through
  projections: a subterm of `P` that is a projection on a still-unbound
  parameter faces anything, binds nothing and is not compared (Rule 38(e)
  compares it later). Nothing in `A` is ever bound. Cost is linear in the size
  of `P`.
- **Signature**: exactly the parts listed by ch08 Rule 12, plus parameter
  conventions and names, the `scoped(p)` prefix and contract clauses; for a
  `trait`, also its associated-type declarations with their bounds; for an
  `impl`, its header, its associated-type definitions (`type A = T;`) and the
  signature of each method.

## Rules

### A. Discipline

1. **T0001** — The checker MUST type a function body in one left-to-right pass
   in which each CST node is visited once, in one mode. No rule MAY require
   backtracking, a worklist, a constraint store, a two-way unification
   variable, or any variable that outlives the one call, struct literal or
   operator expression that created it. Cost: each node does O(1) table lookups
   plus type comparisons and one-way matches linear in the size of the types
   involved; impl lookups (Rule 12) and projection normalisations (Rule 20) are
   memoised functions of their arguments, not constraints: a projection is
   either rewritten at once or is a neutral, rigid type, never a variable
   awaiting a later answer. The following are therefore
   not features, and a program that needs one MUST be rejected with this code
   where no more specific code applies: inferring a binding's type from a later
   use (`let x;` with neither annotation nor initialiser; an un-annotated
   closure parameter with no expected `fn` type); numeric-literal defaulting
   that looks beyond the literal's own operator or call; return-type or
   `raises`-type inference for `fn` items; inference of a generic argument from
   a later statement; ranking of candidates of any kind.
2. **T0002** — Signatures are the only interface between declarations. Typing a
   body MUST consult only the signatures of the items, impls and traits it
   mentions, never another body; nothing in a signature is inferred. An
   impl's associated-type definitions are part of its signature, not of any
   body (Definitions), because other declarations' types normalise through
   them (Rule 20): a change to `type A = T;` is a signature-level change and
   MUST change the impl's fingerprint. A change
   confined to a body, a closure, a `const` initialiser's value (unless used as
   a const argument, Rule 13) or a private member never named outside MUST NOT
   change the result of checking any other declaration, so a fingerprint of the
   resolved signature is a sufficient dependency key in the compiler's query
   DAG.

### B. The type universe

3. **T0003** — Primitive types and sizes in bytes: `i8 u8 bool` 1; `i16 u16` 2;
   `i32 u32 f32` 4; `i64 u64 f64` 8; `isize usize rawptr` the target pointer
   width. `bool` has exactly the values `true` and `false`. `Str` is a
   primitive text type; its representation is std's. No other scalar exists (no
   `f16`, `char`, 128-bit; ch03 Rule 1). Layout of every non-primitive type is
   ch05's.
4. **T0004** — `()` is the unit type (one value, size 0). `never` is the
   uninhabited type (size 0); it is the type of `return`, `raise`, `break`,
   `continue`, of a call to a function declared `-> never` (`never` is a
   prelude name, ch08 Rule 17), and of a block that ends in one of these (Rule 33).
   A tuple type `(T1, ..., Tn)`, `n >= 1`, is structural; `(T)` is `T` and
   `(T,)` is the 1-tuple (ch07). Tuples have no index fields; components are
   reached by a tuple `binding` or pattern.
5. **T0005** — Built-in generic types: `Array[T, N]` (`N: usize`; the type of
   `[x; n]` and array literals, ch03 Rules 21-24a; there is no `[T; n]` type
   syntax), `Slice[T]` (ch03 Rule 24), `vector[T, N]` and `mask[N]` (ch03 Rule
   19; `SVec[T]` stays reserved, ch03 Rule 20), `Option[T]` (an ordinary enum
   with variants `some(T)` and `none`, which the prelude also binds as values),
   `atomic[T]`, `Own[T, A]`, `Ref[T, A]`, `Arena[T, A]` (ch01), and the range
   types `Range[T]` / `RangeIncl[T]` produced by `..<` / `..=` (Rule 30).
6. **T0006** — `struct`, `soa struct` and `enum` declarations introduce nominal
   types: two declarations are never equal whatever their fields. `soa` changes
   layout only (ch05) and no typing rule. An enum is closed: its variant set is
   exactly its declaration's, in every module, `pub` or not; adding a variant
   is a source-breaking change (Rule 53).
7. **T0007** — Function types are written as ch07's `fn_type` and are equal iff
   conventions, parameter types, result type and `raises` type are pairwise
   equal (a missing result is `()`; a missing `raises` is distinct from every
   `raises E`). A non-generic `fn` item used as a value has the matching `fn`
   type; a generic one MUST be written with all its arguments (`id[i32]`). Each
   closure expression has its own anonymous closure type, which cannot be
   written. `dyn Tr` is the object type of a dyn-capable trait (Rule 25). A
   value of `fn`, closure or callable-parameter type (Rule 41) is called with
   `( )`; its parameter types are complete, so every argument is checked.
8. **T0008** — There is no type-alias declaration (ch07). `Self` is the only
   alias-like name: inside `impl ... for S` / `impl S` it MUST be replaced by
   `S` before any comparison, overlap test or fingerprint (`Self.A` there:
   Rule 61(c)); inside a `trait` it is a rigid parameter whose one bound is
   the trait itself, with the trait's own parameters as arguments. If aliases are ever added they MUST be transparent in
   the same way.
9. **T0009** — Type equality. Two types are equal iff they have the same
   qualifier set and the same head and their arguments are pairwise equal: type
   arguments by this rule; brand arguments by identity (the same fresh brand or
   the same brand parameter, ch01 Rules 15, 15d); const arguments by value when
   closed, by identity when a bare const parameter (Rule 13). Equality is
   syntactic on resolved, `Self`-expanded, *normalised* types (Rule 20, the
   only normalisation there is): two neutral projections are equal iff their
   heads are equal and they name the same trait (arguments included) and the
   same associated type. There is no subtyping and no variance.
10. **T0010** — There is no subtyping. `check(e, T)` with `synth(e) = S`, `S !=
    T`, succeeds only through this closed list, applied once, at the outermost
    type only, never searched or chained: (a) `never` to any `T`; (b) a closure
    type or `fn` item to an equal `fn` type; (c) a type `S` to `dyn Tr` when
    `S` implements `Tr` (Rule 12). (c) MUST be rejected for a
    brand-mentioning or scoped value (ch01 Rules 15(b), 19a); (b) MUST be
    rejected for a brand-mentioning value and for a closure capturing one
    (ch01 Rule 15(b)), while a closure's other captures SURVIVE the
    coercion as the `fn`-typed value's sources (ch01 Rule 19d; round-6
    verification — without this, `it.map(|sink x| x + k)` would be
    unwritable), and (c) MUST
    also be rejected when `S` is LINEAR (ch01 Rule 22f: the cleanup
    obligation would become invisible) or when `S` is a rigid type
    parameter or a neutral projection (round 6; a generic body that wants
    an object takes `dyn Tr` as a parameter — this is the clause that
    closes the last escape in ch01 Rule 19c(a)'s soundness argument). Any conversion
    between qualified and unqualified forms (`iso`, `imm`, `secret`) is ch01's
    and ch05's; this chapter adds none. There is no numeric, array-to-slice
    (ch03 Rule 24) or `T`-to-`Option[T]` coercion. Anything else: type
    mismatch, Rule 26.

```fors
fn f(let c: bool) -> i64 {
    let a: i64 = if c { 1 } else { return 0; };   // never -> i64, Rule 10(a)
    let b: i32 = 2;
    return a + b;          // rejected T0026: expected i64, found i32
}
```

### C. Well-formedness

11. **T0011** — A `type_app` MUST supply exactly as many arguments as its item
    declares parameters, each of the declared kind: a type for a type
    parameter, a constant for a const parameter, a brand for a `brand`
    parameter (kind misuse is ch01 Rule 15d's diagnostic). The single exception
    is the omitted brand in a `with` header (ch01 Rule 15b). A generic item
    named with no arguments is legal only where Rule 34 or 38 determines them.
    A bare `targ` path (ch07 Disambiguation 11) is classified by the kind of
    the parameter it fills. The head of a type path MUST be what ch08 resolved
    to a type-level entity: a struct, enum, trait (after `dyn`, in a bound or
    an `impl` header), prelude type, type parameter or `Self`, possibly
    reached through modules. A head that ch08 resolved to a value — in
    particular a local or parameter that shadows a prelude type (ch08 Rule
    18: `fn f(let Option: i32)` then `Option[i32]` in the body), or a local
    named `io` written as the head of `io.Stdout` in a module that does not
    import `std.io` (round 5, D3: `io` is then an ordinary binding, not a
    module) — MUST be rejected with this code, naming the binding. A type path with deferred segments (ch08
    Rule 16) is a projection and is Rule 61's. **Linear element types**
    (round 6, ch01 Rule 22b): a CONCRETE `Array[X, N]`, `vector[X, N]` or
    `atomic[X]` whose element type `X` is linear MUST be rejected with this
    code where the type is written or instantiated, naming `X` and its
    linear head. An element can leave such a value only by a partial move,
    which ch01 Rule 4a(c) forbids, so the obligation could never be
    discharged. With a RIGID element type the same written type is
    well-formed and its values obey Rule 57's drop clause instead.
12. **T0012** — Bounds MUST hold at every use: for each argument `X` given to a
    parameter `P: Tr1 + ... + Trk`, `X` MUST implement every `Tri`. "`X`
    implements `Tr[As]`" is decided structurally: if `X` is a rigid parameter,
    by its declared bounds only; otherwise find the impls of `Tr` whose
    self-type head equals `X`'s head, one-way match each impl's `(trait
    arguments, self type)` against `(As, X)` — at most one matches, by Rule 19
    — and then require the matched impl's own bounds on the subterms it bound.
    If `X` is a neutral projection `P.A`, by the bounds the trait declares for
    `A` (Rule 16) and the constraint entries in scope (Rule 62) only. A
    constraint entry `P.A: Tr` of the callee is a bound like any other: after
    Rule 38 it is checked on the normalised `P.A`. Every recursive goal is about a strict subterm of `X`: Rule 18 forbids a
    bare-parameter self type, REQUIRES every bounded impl parameter to occur
    in the impl's self type (a parameter bound only by the trait arguments
    `As` would make the next goal's subject a subterm of `As`, which a bound
    such as `U: Tr[Wrap[U]]` lets grow without limit), and an impl's bounds
    attach only to its parameters because Rule 62 forbids constraint entries
    on an `impl`. The trait arguments of a recursive goal may be larger than
    `As`; its subject never is. So the
    procedure terminates in time linear in the size of `X` times the number of
    impls of that trait for that head; results are memoised. An
    `@unsafe(invariant:)` impl (ch01 Rule 21c) satisfies a bound like any other
    impl; its soundness is the unsafe ledger's (ch04 Rule 9).
13. **T0013** — A generic parameter whose bound is a type (Rule 15) is a const
    parameter; that type MUST be an integer type or `bool`. A const argument
    MUST be either a closed constant expression, evaluated by comptime (ch04
    Rules 11-14) and required to fit the parameter's type, or a bare const
    parameter of the enclosing declaration. Arithmetic on a const parameter in
    type position (`Array[T, N + 1]`) MUST be rejected: its range error could
    surface only after instantiation, which Rule 59 forbids.
14. **T0014** — A type of infinite size MUST be rejected. Build the graph whose
    nodes are struct and enum declarations, with an edge `D -> E` when a field
    or payload type of `D` mentions `E` outside the arguments of `Own`, `Ref`,
    `Arena`, `Slice`, `rawptr`, a `fn` type or `dyn`; any cycle is the error,
    reported on one field of the cycle. A projection stores whatever it
    normalises to, so the graph also has one node per associated type
    `Tr.A`, with an edge `D -> Tr.A` when a field or payload type of `D`
    mentions a projection of `Tr`'s `A` outside those same indirections, and
    an edge `Tr.A -> E` for every struct or enum `E` that the right-hand side
    of any impl's `type A = RHS;` mentions outside them (without this,
    `struct S[I: Iterator] { x: I.Item }` with `impl Iterator for Foo { type
    Item = S[Foo]; ... }` would give `S[Foo]` infinite size although no
    declaration mentions itself); a cycle through such an edge is reported
    on that `type A = RHS;`. The test is on declarations (one SCC
    pass), never per instantiation, and is conservative: a generic argument
    counts as stored by value. What `Own`/`Ref` mean is ch01's.
15. **T0015** — A `gparam` is classified from its bound alone: `brand` (ch01
    Rule 15d); no bound — an unbounded type parameter; otherwise every
    `+`-joined bound is resolved, and they MUST be either all traits (a bounded
    type parameter), or exactly one non-trait type (Rule 13), or exactly one
    `fn_type` (a callable parameter, Rule 41). `+` is the only way to state
    several bounds; there is no `where` clause, so a bound's subject is always
    a parameter or, in a constraint entry (ch07 `gconstraint`, Rule 62), a
    projection on a parameter. A constraint entry is not a `gparam`: it
    introduces no name and has no kind.

```fors
struct List { head: Option[List] }                 // rejected T0014
struct Tree[A: brand] { root: Option[Ref[Tree[A], A]] }   // accepted: Ref
fn first[T: Copyable, N: usize](let a: Array[T, N]) -> T { return a[0]; }
fn grow[T, N: usize](let a: Array[T, N]) -> Array[T, N + 1] { return a; } // rejected T0013
```

### D. Traits and impls

16. **T0016** — A `trait` declares methods and associated types (ch07
    `trait_item`). A method with `;` is required; one with a block is
    provided, and its body is checked once, with `Self` rigid and only the
    trait's own methods, the declared bounds of its associated types and the
    bounds of its generic parameters available. `type A;` or `type A: Tr1 +
    ... + Trk;` declares the associated type `A`: every `Tri` MUST be a trait
    (not `brand`, not a `fn` type, not a const-kind type; Rule 15's other
    kinds do not exist for associated types), and inside the trait `Self.A`
    is a neutral projection (Rule 61(b)) usable in every method signature,
    bound and provided body, including the bounds of another associated type.
    Names: ch08 Rule 27. v0.1 restrictions, each liftable without breaking
    accepted code: no generic associated types, no defaults (`type A = T;` in
    a trait is ch07's parse error), no associated consts, no equality bounds,
    no supertraits: a constant is a parameterless method (`fn zero() ->
    Self;`), and a function needing two traits writes `T: Eq + Ord`. A method
    whose first parameter is named `self` MUST give it the type `Self` (in an
    impl: the self type), optionally qualified, or OMIT the annotation
    entirely — ch07's receiver shorthand `convention "self"` (Disambiguation
    21, owner decision 2026-09-19, round 5, D1), which means exactly
    `self: Self` and is the same signature for every rule of this chapter;
    it is a *receiver method*.
    Other functions of a trait or impl are *associated functions*.
17. **T0017** — `impl Tr[As] for S` MUST define every required method of `Tr`,
    MAY redefine provided ones, MUST define every associated type of `Tr`
    exactly once (`type A = T;`; a second definition in the same impl is ch08
    Rule 27's error), and MUST NOT define anything else; an inherent impl
    MUST NOT contain a `type` item. Each right-hand side `T` MUST be
    well-formed (Rules 11-14, 61(d)) and MUST implement every bound the trait
    declares for `A`, after substituting `Self := S`, the trait parameters by
    `As` and `Self.B` by this impl's definition of `B`; the check is made
    once, at the impl, with the impl's parameters rigid (Rule 12), and is
    never repeated at a use. Each method's signature MUST equal the trait's
    after the same substitution and normalisation: same generic parameters,
    bounds and constraint entries, conventions, parameter names and types,
    result type (`scoped` included) and `raises` type. Contract clauses on an
    impl method are ch02's.
18. **T0018** — In an `impl_decl` with `for`, the first type MUST be a trait
    and the second MUST NOT be one; without `for` the type MUST be a struct or
    enum. Every type, const and brand parameter of the impl MUST occur in the
    impl head — its self type or trait arguments — otherwise "unconstrained
    impl parameter" (no match could determine it; an occurrence only in a
    bound, in `type A = ...;` or in a method does not count). A parameter
    that carries a bound MUST moreover occur in the impl's SELF type: an
    occurrence in the trait arguments alone is "bounded impl parameter not
    in the self type" (Rules 12 and 20 recurse on the self type only; given
    `impl[U: Tr[Wrap[U]]] Tr[U] for Foo` and `impl[V: Tr[Wrap[V]], W] Tr[V]
    for Wrap[W]`, the goal `Foo: Tr[Wrap[Foo]]` would otherwise ask for
    `Wrap[Foo]: Tr[Wrap[Wrap[Foo]]]`, then `Wrap[Wrap[Foo]]: ...`, for
    ever). The impl head
    MUST NOT contain a projection, at any depth. The self type MUST NOT be a
    bare type parameter: blanket impls do not exist. Where an impl may be
    written is ch08 Rule 21.
19. **T0019** — Overlap. Two impls of the same trait MUST NOT unify: rename
    their generic parameters apart, treat them as variables, and unify the
    pairs `(trait arguments, self type)` first-order, ignoring all bounds;
    success is an error at the later impl naming the earlier. Ignoring bounds
    means there is no specialisation and no negative reasoning. Associated
    types play no part: the test never reads a `type A = T;`, and two impls
    that differ only there overlap. The test is decidable and cheap: impl
    heads are finite first-order terms (no aliases; no projections, by Rule
    18; const arguments are constants or variables), so unification with
    occurs check is near-linear, and only impls with the same trait and the
    same self-type head are compared. Two inherent impls of one type MAY
    coexist; their method names MUST be distinct (Rule 48).
20. **T0020** — Normalisation. Types are compared (Rule 9), matched (Rule 38)
    and displayed after normalisation, a function computed bottom-up:
    arguments first, then each projection `H.A` of trait `Tr[As]` whose head
    `H` is now normal. (a) If `H` is rigid — a type parameter, `Self` in a
    trait, or itself a neutral projection — `H.A` is *neutral*: a normal,
    opaque type, equal only to the same (head, trait with arguments, name)
    (Rule 9), whose only operations are those of Rule 57. (b) Otherwise find
    the impl of `Tr[As]` for `H` by Rule 12's lookup (none: T0012, reported
    where the projection arose; at most one, by Rule 19), take its `type A =
    RHS;`, apply the match substitution to `RHS` and normalise the result. An
    undetermined parameter of the call being typed is neither: a projection on
    it is left alone until it is bound (Rule 38). *Termination and cost.* By
    Rule 61(d) a projection inside `RHS` is headed only by one of the impl's
    own parameters; to head a projection that parameter must carry the bound
    that declares the associated type (Rule 61(c)), and by Rule 18 a bounded
    impl parameter occurs in the impl's SELF type, so the match bound it to
    a STRICT SUBTERM of `H`, already normal. Every
    expansion step therefore projects on a strict subterm of the type being
    normalised: normalisation is structural descent on `H`. It terminates; no
    cycle can be written (`type A = Self.A;` and a projection headed by a
    concrete type are Rule 61 errors, and `Wrap[T].A` is not a ch07 `type` at
    all); with results memoised per (type, trait, name) its cost is linear in
    the number of distinct subterms of the type. Implementations SHOULD
    intern types so a repeated right-hand side (`type A = Pair[T.A, T.A];`)
    is shared rather than copied. Normalisation happens at substitution time
    — instantiating a signature at a call, a field type at an access, an impl
    at a lookup — so no later rule ever sees a projection with a non-rigid,
    determined head.
21. **T0021** — The operator-trait set is closed; no other operator is
    overloadable and no other trait is consulted by an operator.

    | Operator | Trait | Method (receiver `let self`) |
    |---|---|---|
    | `+` `-` `*` `/` `%` | `Add` `Sub` `Mul` `Div` `Rem` | `add sub mul div rem (let rhs: Self) -> Self` |
    | unary `-` | `Neg` | `neg() -> Self` |
    | `&` `\|` `^` `<<` `>>` | `BitAnd` `BitOr` `BitXor` `Shl` `Shr` | `bitand bitor bitxor shl shr (let rhs: Self) -> Self` |
    | `==` `!=` | `Eq` | `eq(let rhs: Self) -> bool`; `a != b` is `not a.eq(b)` |
    | `<` `<=` `>` `>=` | `Ord` | `lt`, `le` `(let rhs: Self) -> bool`; `a > b` is `b.lt(a)`, `a >= b` is `b.le(a)` |
    | `a[i]` read | `Index[I]`, `type Output;` | `at(let i: I) -> scoped(self) Self.Output` |
    | `a[i]` written or passed `&` | `IndexMut[I]` | `at_mut(inout self, let i: I) -> scoped(self) Self.Output` |
    | `for x in e` | `Iterator`, `type Item;` | `next(inout self) -> Option[Self.Item]` |
    | `a op= b` | the trait of `op` | `a = a op b` with the place `a` evaluated once |

    Every binary operator trait is homogeneous (`Self x Self -> Self`; owner
    decision round 4): `Add` and its siblings have NO `Output`, so resolution
    is one lookup keyed on the left operand's type (Rule 29); operands are
    evaluated left to right whatever the desugaring. Whether a `scoped` result
    is a place is ch01 Rules 19-19a. The language-known declarations are
    (receivers abbreviated in the table are written in full here):

    ```fors
    trait Iterator { type Item: Droppable; fn next(inout self: Self) -> Option[Self.Item]; }
    trait Index[I] { type Output; fn at(let self: Self, let i: I) -> scoped(self) Self.Output; }
    trait IndexMut[I] { fn at_mut(inout self: Self, let i: I) -> scoped(self) Self.Output; }
    ```

    `Iterator` is language-known in its REQUIRED part only: the associated
    type, its bound and `next`. Std declares the same trait and adds
    PROVIDED methods to it (the adaptors and consumers of ch10 Rules
    32-35); a provided method is a lookup candidate exactly like a required
    one (Rules 16, 43), so nothing here changes for it. `Iterator` is the
    SECOND trait with a language-known prerequisite, after `IndexMut`
    (round 6, O1): `impl Iterator for S` MUST be rejected unless `S` is
    `Droppable`, and a bound `P: Iterator` implies `P: Droppable`. With
    `type Item: Droppable` this means v0.1 has no linear iterator and no
    linear item, which is what lets `for x in it` (Rule 31) own and drop
    the iterator and drop each item, in a generic body as well as a
    concrete one. An iterator over a linear source takes that source
    `inout` and is `scoped` to it; a container of linear elements is
    emptied by `pop`/`remove`, never iterated by value (ch10 Rule 33).

    A type MAY implement `Index[I]` for several `I`. `IndexMut[I]` declares no
    associated type of its own: it is the one trait with a language-known
    prerequisite — `impl IndexMut[As] for S` MUST be rejected unless `S`
    implements `Index[As]` (Rule 12, impl parameters rigid), a bound `P:
    IndexMut[I]` implies `P: Index[I]`, and inside `IndexMut` `Self.Output`
    denotes `Index[I]`'s. Reads and writes of `a[i]` therefore have one and
    the same element type. This is not a supertrait feature: no other trait
    has or can declare a prerequisite.
22. **T0022** — Not overloadable, and typed only by this chapter's fixed rules:
    `and`, `or`, `not` (operands `bool`); `=`; `?` and the `else` handler
    (ch02); `move`, `&`, `&out` (ch01 Rule 2); `as` (numeric primitives only,
    ch03 Rule 6); `..<` and `..=`; range-indexing `a[lo ..< hi]` (built-in on
    `Array` and `Slice` only, ch03 Rule 24, selected syntactically by a range
    expression directly inside the brackets); `.name`; call `( )`. Built-in
    impls: every integer type has all of Rule 21's arithmetic, bitwise, `Eq`
    and `Ord` traits (`Neg` signed only); floats have `Add Sub Mul Div Rem Neg
    Eq Ord`; `bool` has `Eq`; `mask[N]` has `BitAnd BitOr BitXor Eq`; `Array`,
    `Slice`, `vector` index by `usize` with `Output = T` (indexing stays
    `usize`-only: write `1usize ..< 8` for a loop that indexes), `Arena[T, A]`
    by `Ref[T, A]` (ch01 Rule 16). Their semantics (traps, IEEE, lanes) are ch03's;
    `wrap_`/`sat_`/`unchecked_` forms are ordinary methods (ch03 Rule 4).
23. **T0023** — `Copyable` is a checked marker trait with no methods. Using a
    place of `Copyable` type as a value copies it; any other place is moved
    (the consequences are ch01's). `impl Copyable for T {}` MUST appear in
    `T`'s defining module and is accepted only if every field and payload
    component of `T` is `Copyable`, a field mentioning a parameter `P` needing
    the impl to declare `P: Copyable`; the check runs once on the declaration.
    Built in: numeric types, `bool`, `()`, `never`, `rawptr`, `Str`, `Ref[T,
    A]` , `fn` item types, and tuples, `Array`, `vector`, `mask`, `Option` of
    `Copyable` components. Never `Copyable`: `Own`, `Arena`, allocator and
    root-capability types (ch01 Rule 15a, ch04 Rule 7), any `iso` type, a
    closure type, `dyn Tr`. This is the `Copyable` that ch01 Rule 4 and ch03
    Rule 24a name. `impl Copyable for T` MUST also be rejected when `T` is
    LINEAR (ch01 Rule 22e), and `X: Copyable` implies `X: Droppable`.
24. **T0024** — A marker trait (`Shared`, `Copyable`, and from round 6
    `Linear` and `Droppable`) has no methods and
    contributes no operation to a generic body; as a bound it only restricts
    instantiation (ch01 Rule 21b). `Shared`'s field check is ch01 Rules 21-21d.
    A marker trait MUST NOT be used as `dyn`. The two round-6 markers differ
    from the other two in how they are established. `Linear` is DECLARED:
    `impl Linear for T {}` in `T`'s defining module, with no bound on any
    parameter of the impl, so linearity is a fact of the constructor and
    never of an instantiation (ch01 Rule 22); linearity then propagates
    structurally, with no impl to write (ch01 Rule 22a). `Droppable` is
    purely STRUCTURAL: `impl Droppable for T` MUST be rejected for every
    `T` — there are no impls at all — and `X: Droppable` holds exactly when
    `X` is not linear (ch01 Rule 22c). As a BOUND, `Droppable` is how a
    generic body says that it drops a value of that parameter's type
    (Rule 57); `Copyable` and `Iterator` each imply it.
25. **T0025** — `dyn Tr` is well-formed iff `Tr` is dyn-capable: it declares
    no associated type (so `dyn Iterator` does not exist in v0.1; there is no
    `dyn Tr[Item = T]` form), it has no generic methods, every method is a receiver method with convention `let` or
    `inout`, and `Self` occurs in no signature other than as the receiver's
    type. Method calls on `dyn Tr` are typed from the trait's signatures.
    Representation is ch03 Rule 16's witness table.

```fors
trait Shape {
    fn area(let self) -> f64;                                  // required (round 5, D1)
    fn twice(let self) -> f64 { return self.area() * 2.0; }    // provided
}
struct Circle { r: f64 }
struct Pair[T] { a: T, b: T }
impl Shape for Circle { fn area(let self: Circle) -> f64 { return self.r * self.r; } }
impl[T] Shape for Pair[T] { fn area(let self: Pair[T]) -> f64 { return 0.0; } }
impl Shape for Pair[i32] {                                           // rejected T0019
    fn area(let self: Pair[i32]) -> f64 { return 1.0; }
}
impl[T] Shape for T { fn area(let self: T) -> f64 { return 0.0; } }  // rejected T0018

struct Counter2 { n: i64, end: i64 }
impl Iterator for Counter2 {
    type Item = i64;
    fn next(inout self: Counter2) -> Option[i64] {      // Self.Item normalised: Rule 17
        if self.n >= self.end { return none; }
        self.n = self.n + 1;
        return some(self.n);
    }
}
struct Skip[I] { inner: I, n: usize }
impl[I: Iterator] Iterator for Skip[I] {
    type Item = I.Item;                                  // headed by an impl parameter: Rule 61(d)
    fn next(inout self: Skip[I]) -> Option[I.Item] { return self.inner.next(); }
}
// Skip[Skip[Counter2]].Item  ->  Skip[Counter2].Item  ->  Counter2.Item  ->  i64   (Rule 20)
trait Keyed { type Key: Eq + Ord; fn key(let self) -> Self.Key; }
impl Keyed for Circle { type Key = f64; fn key(let self: Circle) -> f64 { return self.r; } }
impl Keyed for Counter2 {                                // rejected T0017: Circle is not Eq
    type Key = Circle;
    fn key(let self: Counter2) -> Circle { return Circle { r: 0.0 }; }
}
struct Two[T] { a: T }
impl[T, U] Keyed for Two[T] {                            // rejected T0018: U unconstrained
    type Key = i64;
    fn key(let self: Two[T]) -> i64 { return 0; }
}
struct Three[T] { a: T }
impl[I: Iterator] Keyed for Three[I.Item] {              // rejected T0018: projection in head
    type Key = i64;
    fn key(let self: Three[I.Item]) -> i64 { return 0; }
}
```

### E. The two judgements

26. **T0026** — Every expression is typed by exactly one of `synth(e)` and
    `check(e, T)`; the position decides which (ch03 Rule 25). Unless the table
    below gives a form its own CHECK rule, `check(e, T)` is *subsumption*:
    compute `S = synth(e)`, then require `S = T` (Rule 9) or a Rule 10
    coercion; failure is T0026 "expected `T`, found `S`". A form marked "CHECK
    only" MUST be rejected in SYNTH mode with the code of its rule.

    | Form | synth | check against `T` | Rule |
    |---|---|---|---|
    | suffixed number; string; `true`/`false` | the suffix type; `Str`; `bool` | subsumption | 27 |
    | unsuffixed integer / float | `i32` / `f64` | `T` if an integer (resp. float) type | 27 |
    | `dot_lit` `.v`, `.v(args)` | CHECK only | variant `v` of enum `T` | 34 |
    | `path` (local, param, `const`, `fn` item, variant, `none`) | declared type | subsumption; generic value: Rule 38 | 28 |
    | `a op b`, `-a` | operator method's result | subsumption; `-lit`: check `lit` | 29 |
    | `a op= b`, `a = b` | statement; `b` checked against `synth(a)` | — | 29, 31 |
    | `not a`, `a and b`, `a or b` | `bool`; operands synth to `bool` | subsumption | 30 |
    | `a ..< b`, `a ..= b` | `Range[I]`, `RangeIncl[I]` | subsumption | 30 |
    | `e as U`; `move e` | `U`; type of `e` | subsumption; `move`: check `e` | 30 |
    | block | tail's type, `()` or `never` | tail checked against `T` | 31 |
    | `if` / `match` | first non-`never` branch, rest checked | every branch checked | 32 |
    | `return` `raise` `break` `continue` | `never` | always succeeds | 33 |
    | tuple `(a, b)` | componentwise | componentwise if `T` is an n-tuple | 34 |
    | array literal, `[x; n]` | ch03 Rules 22, 24a | ch03 Rules 21, 24a | — |
    | struct literal, variant construction | as a call (Rule 38) | as a call with expected `T` | 34 |
    | closure | all params annotated | params and result from `fn` type `T` | 35 |
    | call, method call | result type (Rule 38) | Rule 38 with expected `T` | 38-46 |
    | `e?`, call `else \|x\| { }` | the call's success type | the call checked; handler block checked | 36 |
    | `e.f`; `a[i]` | field type; Rule 21 / 47 | subsumption | 42, 47 |
    | `comptime { }` | as its block | as its block | 37 |
    | `asm_expr` | CHECK only (ch04 Rule 27) | ch04 Rule 27 | — |
27. **T0027** — Literals. A suffixed number has its suffix type. An unsuffixed
    integer literal checks against any integer type and an unsuffixed float
    literal against `f32`/`f64` (range: ch03; negated literal: ch07
    Disambiguation 8); an integer literal MUST NOT check against a float type,
    nor any literal against a rigid parameter. In SYNTH mode they are `i32` and
    `f64`. The default never looks outward: `let n = 0;` is `i32` whatever
    later uses need.
28. **T0028** — A `path` resolved by ch08 to a binding synthesises its declared
    type; to a `const`, its annotation; to a non-generic `fn`, Rule 7; to a
    unit variant, its enum with arguments by Rule 38. A generic `fn` or generic
    unit variant (`none`) in SYNTH mode with no explicit arguments MUST be
    rejected (T0039). A path ending on a type, trait or module is not a value
    (ch08 Rule 16).
29. **T0029** — Operators. `a op b` is typed as the method call of Rule 21: `S
    = synth(a)`; `S` MUST implement the trait (Rule 12), else T0029 naming operator, trait
    and `S`; when `S` is rigid (a type parameter or a neutral projection) the
    trait MUST be among its bounds, else T0057 (Rule 57: the fix is a bound,
    not an impl); then `b` is a call
    argument whose parameter type `S` is complete, so it is checked against `S`
    (ch03 Rule 25). One syntactic exception keeps `0 ..< n` and `1 + x` usable:
    when `a` is an unsuffixed numeric literal (optionally negated) and `b` is
    not, `b` is synthesised first and `a` checked against it. When both are
    literals Rule 27's default applies. There is no other operand promotion.
    `a[i]`: `S = synth(a)`; collect the `Index` impls whose head matches `S`
    (if `S` is rigid: its `Index[...]` bounds, Rule 12). None: T0029. Exactly
    one, `Index[I]`: `i` is checked against `I` (so `v[0]` indexes by
    `usize`). Several: `i` is synthesised and `S` MUST implement
    `Index[synth(i)]`, one Rule 12 lookup; an unsuffixed literal index MUST
    then be rejected (T0029, "suffix the index"), so adding a second `Index`
    impl can break `a[0]` but can never silently change which impl it means.
    The result type is the normalised `S.Output` of the chosen impl; a write
    or `&` use selects `IndexMut` with the same `I` (Rule 21). Nothing is
    ranked.
30. **T0030** — `not`/`and`/`or` operands and `if`/`while` conditions and
    contract clauses are synthesised and MUST be `bool`. Both operands of
    `..<`/`..=` MUST be the same integer type `I` (Rule 29's literal exception
    applies); the result is `Range[I]`/`RangeIncl[I]`. `e as U` synthesises
    `e`; both types MUST be numeric primitives. `move e` has the type and mode
    of `e`. A `grain` expression is checked against `usize`.
31. **T0031** — Statements. `let p: T = e;` checks `e` against `T`; `let p =
    e;` binds `synth(e)`, which MUST NOT be `never`; `let p: T;` declares an
    uninitialised binding (definite initialisation is ch01's); a tuple
    `binding` needs a tuple type of the same arity. `var` is identical. `a =
    e;` synthesises the place `a` and checks `e` against it. An expression
    statement is synthesised and its value dropped (whether the drop is legal
    is ch01's); a statement-form `if`/`match` that is not the block's tail is
    checked against `()`. `for p in e`: `synth(e)` MUST be
    `Range[I]`/`RangeIncl[I]` (element `I`), `Array[T, N]` or `Slice[T]`
    (element `T`), or a type `S` that implements `Iterator` (Rule 12; a rigid
    `S` needs the bound), in which case the element type is the normalised
    `S.Item` (Rule 20; neutral when `S` is rigid) and the binding is typed
    against it. The iterable is a value use: a place of non-`Copyable`
    type is moved into the loop, which owns and drops the iterator (Rule
    23; so `for x in it` with `sink it: I` consumes the parameter, and a
    `let` parameter cannot be iterated directly, ch01 Rule 3). The body is
    checked against `()`, as are the bodies of `while`, `parallel`, `with` and
    attribute blocks. A `defer` or `errdefer` statement (ch07) has type
    `()`; its `block` body is checked against `()`, and its `expr ";"` form
    is checked as the expression statement it abbreviates. Everything else
    about a deferred body — where it may appear, when it runs, what it may
    contain, what it may capture and consume — is ch01 Rules 23-23f. A function body is checked against the declared result
    type (`()` if absent); `return e;` checks `e` against it and `return;`
    requires `()`. A block with no tail expression has type `()`, or `never`
    when its last statement has type `never`.
32. **T0032** — `if` and `match`. In CHECK mode every branch block or arm body
    is checked against the expected type. In SYNTH mode branches are
    synthesised in source order until one has a type `R` other than `never`;
    every later branch is checked against `R`; if all are `never` the result is
    `never`. Earlier `never` branches need no second visit (Rule 10(a)), so
    this is one pass. An `if` with no `else` has type `()` and its block is
    checked against `()`. There is no join or common-supertype computation.
33. **T0033** — `never`. A binding MUST NOT be given type `never` by synthesis
    (`let x = die();` with `fn die() -> never` is rejected — `return` itself
    is a statement in ch07, not an expression; with an annotation the
    initialiser coerces by Rule 10(a)). `never` MUST NOT be bound to a generic parameter by Rule
    38's matching: an argument that synthesises `never` binds nothing (it
    coerces to whatever the parameter becomes), and a parameter left
    undetermined is T0039. `break`/`continue` outside a loop MUST be rejected.
    Inside a `defer`/`errdefer` body (ch01 Rule 23c) a `return`, a `raise`,
    a `?`, and a `break`/`continue` whose target loop is outside the body
    MUST be rejected with this code, naming the enclosing `defer` or
    `errdefer` statement.
34. **T0034** — Aggregates. A struct literal MUST name each field of the struct
    exactly once and nothing else, each visible (ch08 Rule 11), and is typed as
    a call whose parameters are the fields in written order (Rule 38); explicit
    arguments are the `bracket` of ch07's `struct_lit`. A tuple variant is
    constructed by calling its path (`Shape.circle(1.0)`, `some(y)`), a
    struct-form variant by a struct literal on its path, a unit variant by its
    path. A `dot_lit` is legal only in CHECK mode against an enum type, where
    `.v` names that enum's variant `v`.
35. **T0035** — Closures. Checked against a `fn` type: the `cparam` count and
    any written convention or type MUST agree with it, un-annotated parameters
    take theirs from it, and the body is checked against its result type; `?`
    and `raise` in the body use its `raises` type. In SYNTH mode every `cparam`
    MUST carry a type (convention defaults to `let`), the body is synthesised,
    the closure does not raise, and `return` inside it MUST be rejected (its
    type is not yet known). A closure parameter's type is never inferred from
    the body. What a closure may capture is ch01's.
36. **T0036** — `e?` and `call else |x| { ... }` require `e` to be a call of a
    `raises E` function (ch02 Rules 1-5). Their type is the call's success type
    and an expected type is passed to the call. `x` has type `E`; the handler
    block is checked against the success type. The `ErrorFrom[E]` impl ch02
    Rule 3 needs is found by Rule 12 on the enclosing function's `raises` type.
    `raise e;` checks `e` against the enclosing `raises` type.
37. **T0037** — `comptime { }` has the type and mode of its block (evaluation:
    ch04). `spawn e;` requires `e` to be a call; `consume`/`discard` take any
    place (ch01). A `bare_op` argument is legal only in CHECK mode against a
    `fn(let X, let X) -> X` (or `-> bool` for comparison operators) with `X`
    complete, and denotes Rule 21's method for `X`. A named argument's label
    MUST equal the name of the parameter in that position; arguments are never
    reordered and no parameter has a default.

### F. Generic calls

38. **T0038** — The generic arguments of a call, struct literal or variant
    construction are determined by this procedure and no other. Let the
    *parameters to determine* be those of the impl or trait reached (with
    `Self`), then those of the function, enum or struct. (a) Explicit `[...]`
    arguments, if written, MUST be all of the function's (or type's) own
    parameters, in order (constraint entries are not parameters and take no
    argument). (b) A method receiver is synthesised and matched one-way
    against the receiver parameter type. (c) In a CHECK position the declared
    result type is matched one-way against the expected type; a structural
    mismatch here binds nothing and is not yet an error. (d) Arguments are
    then visited left to right: the parameter type is substituted with
    everything bound so far and normalised (Rule 20); if it is now complete,
    the argument is checked against it; otherwise the argument is synthesised
    and the parameter type is matched one-way against the result. A parameter
    type that is, or contains, a projection on a still-undetermined parameter
    never BINDS through that projection (Definitions, one-way match): the
    projection subterm is skipped. (e) Finally every parameter type whose
    argument was synthesised in (d) is substituted in full, normalised, and
    the type that argument synthesised MUST equal it or coerce to it by Rule
    10 (T0026 at that argument);
    this is the only place a skipped projection is compared, and it is a
    comparison of two complete types, not a unification. The bounds and
    constraint entries of the callee are then checked (Rule 12). (f) The
    result type, fully substituted and normalised, is the call's type
    (subsumption applies in CHECK mode). A binding is never revised; a later
    disagreement is T0026 at that argument. No variable survives the call:
    each nested call runs the procedure to completion before the outer one
    continues. Associated types need no inference step of their own: once `I`
    is bound, `I.Item` is a function of it (Rule 20), so an argument whose
    parameter type mentions only projections on already-bound parameters is
    complete and is CHECKed — this is what lets a closure follow its iterator
    (Rule 41, and the `map_sum` example below). An argument that precedes the
    binding of its projection's head is merely synthesised (`fn f[I:
    Iterator](let x: I.Item, sink it: I)` types `x` alone, then compares in
    (e)); declare the head-binding parameter first.
39. **T0039** — If a parameter is still undetermined after Rule 38(d) — a
    parameter that occurs only under projections (`fn g[I: Iterator](let x:
    I.Item)`) always is, unless given explicitly — the call
    MUST be rejected: "cannot infer `T`; write `f[T](...)`". Wrong
    explicit-argument count, wrong argument count, and a convention marker that
    disagrees with the parameter (ch01 Rule 2) are also reported at the call.
40. **T0040** — Const parameters follow Rule 38 unchanged (bound by value or by
    the bare parameter). A brand parameter is bound by identity, and only from
    a receiver or argument type, steps (b) and (d): step (c) skips brand
    positions and the final subsumption compares them (ch01 Rule 15d; two
    brands for one parameter is T0026). A fresh brand may be bound to a
    *callee's* parameter only; since every binding's type is fixed at its
    declaration (Rules 1, 31), a type mentioning a fresh brand can never reach
    a binding, field or signature outside its `with` block (ch01 Rule 15).
41. **T0041** — A callable parameter `F: fn(...) -> R raises E` (Rule 15)
    accepts a closure type, `fn` item or `fn` value of that signature, and a
    value of type `F` may be called with it. When the argument for a parameter
    of type `F` (or of a `fn` type) is syntactically a closure and every
    *parameter* type of the signature is complete (after substitution and
    normalisation, Rule 38(d)), the closure is checked by
    Rule 35; if the signature's result type is not yet complete the body is
    synthesised instead and the result type matched one-way against it.
    Otherwise Rule 38(d) applies. This is the only place a result type flows
    out of a closure.

```fors
fn apply[T, U, F: fn(let T) -> U](let x: T, let f: F) -> U { return f(x); }
fn demo() {
    let a = apply(2, |let n| n * 2);   // T := i32 from `2`; closure checked; U := i32
    let b: Option[u8] = some(1);       // Rule 38(c): T := u8, then `1` is checked
    let c = none;                      // rejected T0039: write Option[u8].none
    let d = apply(|let n| n * 2, 2);   // rejected T0035: T unbound, closure is SYNTH
}

fn map_sum[I: Iterator, U: Add + Copyable, F: fn(sink I.Item) -> U](sink it: I, let f: F, let zero: U) -> U {
    var acc: U = zero;                      // a copy: U is Copyable (Rule 23)
    for x in it { acc = acc + f(move x); }  // x: I.Item (Rule 31); `+` from U: Add
    return acc;
}
fn demo2(sink xs: Counter2) {          // given: impl Iterator for Counter2 { type Item = i64; ... }
    let s = map_sum(move xs, |sink x| x * 2, 0);   // an argument, so marked (ch01 Rule 2)
    // I := Counter2 from `move xs`; fn(sink I.Item) -> U normalises to
    // fn(sink i64) -> U, whose parameter types are complete, so the closure
    // is CHECKed (x: i64) and its body synthesises U := i64; `0` is then
    // checked as i64. Nothing was propagated: I.Item is a function of I.
}
```

### G. Members

42. **T0042** — `e.name` not followed by a call or by instantiating brackets is
    a field access: `synth(e)` MUST have a struct head with a visible field
    `name` (ch08 Rule 11); the result is the field's type with the struct's
    arguments substituted, qualified per ch01 Rule 11 and ch05 Rule 6a. Naming
    a method without calling it MUST be rejected; there are no method values. A
    rigid parameter, tuple, enum or primitive has no fields (`len` on
    `Slice`/`Array` is built in).
43. **T0043** — `e.name(args)`: `S = synth(e)`, qualifiers stripped for lookup.
    Candidates are searched in two tiers, stopping at the first non-empty one:
    (1) receiver methods named `name` in the inherent impls of `S`'s head whose
    self type matches `S`; (2) receiver methods named `name` of each *candidate
    trait* that `S` implements. If `S` is a rigid parameter the candidate
    traits are exactly its bounds; if `S` is a neutral projection `P.A`,
    exactly the bounds its trait declares for `A` plus the constraint entries
    on `P.A` in scope (Rule 62); if `S` is `dyn Tr`, exactly `Tr`; otherwise
    they are the prelude traits and the traits with an impl for `S`'s head
    located in the module defining that head, in the current module, or in a
    module the current module has a direct edge to (ch08 Rule 7).  This uses
    the module graph, not a scope (ch08 Rule 22), so a module the caller does
    not import cannot alter the outcome. No candidate: T0043. Whether a
    trait method is REQUIRED or PROVIDED (Rule 16) makes no difference
    here: a provided method is a candidate exactly like a required one, and
    is the mechanism by which std puts `map`, `filter`, `take` and the
    consumers on `Iterator` without a blanket impl (ch10 Rules 32-35). A
    std type that implements `Iterator` therefore MUST NOT declare an
    INHERENT method whose name is that of one of `Iterator`'s provided
    methods, since tier (1) would silently re-route the call (Rule 44's
    inherent-before-trait precedence; ch10 Rule 34).
44. **T0044** — More than one candidate in the tier that answered MUST be an
    error listing them; the call is rewritten in a qualified form (Rule 45).
    Candidates are never ranked by specificity, import order or argument types.
    Inherent-before-trait is the only precedence, so that adding a trait impl
    never changes an existing inherent call.
45. **T0045** — Qualified forms (deferred segments, ch08 Rule 16). `Type.name`
    / `Type[args].name`: an inherent associated function or method of that
    head, else one from a candidate trait (Rules 43-44). `P.name` with `P` a
    rigid parameter: from `P`'s bounds; when `name` is an associated type the
    path is a projection (Rule 61), and `P.A.name` takes `name` from the
    bounds of the neutral projection `P.A` (Rule 43's candidate traits). `Tr.name` / `Tr[args].name`: that
    trait's function, with `Self` determined like any parameter by Rule 38. In
    every qualified form a receiver is an ordinary first argument and carries
    its ch01 Rule 2 marker.
46. **T0046** — Receivers. In method-call form `e.m(args)` the receiver
    carries no convention marker, for ANY convention; the convention comes
    from the method Rules 43-44 resolved: `let self` reads `e`; `inout self`
    requires a mutable place; `sink self` takes an rvalue as it is and, when
    `e` is a place (ch07 `place`: a binding or a projection path), MOVES that
    place implicitly (owner decision round 4). This is the single exception
    to ch01 Rule 2, which cross-references this rule. `(move x).m(args)` is
    legal and means exactly the same. The implicit move is a move in every
    respect: all of ch01's rules apply unchanged (ch01 Rule 4a, clause by
    clause: (a) use after move; (b) a move inside a loop; (c) a partial
    move, so `a.b.finish()` on a field place is rejected; (d) a move out of
    a `let` or `inout` parameter; (e) a move of a place captured by a
    closure, and `spawn x.run();` as the `move` capture of ch01 Rule 13;
    further an `iso` or `imm` qualified place, ch01 Rules 12-13, and ch05's
    rules for a `secret` one) and
    accept or reject the call exactly as they would `(move x).m(args)`; if
    the receiver's type is `Copyable` it is copied, not moved (Rule 23). This
    chapter adds no ownership rule of its own. **Diagnostic requirement
    (normative).** When a use-after-move (or any other ch01 move error) is
    reported for a place whose move was an implicit receiver move, the
    diagnostic MUST name the consuming call (its method name and location)
    and the `sink self` declaration it resolved to (the method's owner type
    or trait and its location), e.g. "`x` was moved by the call `x.finish()`
    at 12:5, because `Builder.finish` takes `sink self` (declared at
    3:8)". The code stays ch01's. There is no auto-dereference,
    auto-reference or receiver adjustment of any kind: the receiver's type
    MUST match the method's self type up to the qualifier access ch01
    permits.
47. **T0047** — A `bracket` after an expression instantiates iff its operand is
    a `path` the resolver bound to a generic `fn`, struct, enum, trait or
    prelude type, or is a `.name` that Rule 43/45 resolves to a method or
    associated function; its arguments are then reinterpreted as types,
    constants and brands (ch07 Disambiguation 11). Otherwise it is an index
    (Rules 21-22). The reading never depends on the arguments.
48. **T0048** — Member clashes (left open by ch08 Rule 27) are errors at the
    later declaration: two inherent methods or associated functions of one head
    with the same name, in the same or different `impl` blocks; an inherent
    member named like a field of the struct; an inherent associated function
    named like a variant of the enum (closes ch08 open question 5: the clash
    is an error, so ch08 Rule 16's "the variant wins" never decides a
    program). Names inside one trait or one impl are ch08 Rule 27's.
49. **T0049** — The checker enforces ch08 Rule 11 for every member it resolves,
    with ch08's diagnostic, and performs no scope lookup (ch08 Rule 22).

```fors
struct Counter { n: i64 }               // Shape, Circle: section D's example
impl Counter { fn bump(inout self: Counter) { self.n = self.n + 1; } }
fn total(let c: Circle, inout k: Counter) -> f64 {
    k.bump();                          // inout receiver, no marker: Rule 46
    return c.area() + Shape.twice(c);  // method form; qualified form: Rule 45
}

struct Builder { parts: i64 }          // not Copyable
impl Builder {
    fn finish(sink self: Builder) -> i64 { let p = self.parts; discard self; return p; }
}
fn build(sink b: Builder, sink c: Builder, let d: Builder) -> i64 {
    let n = b.finish();                // moves `b` implicitly: Rule 46
    let m = (move c).finish();         // same meaning, explicit
    let k = b.finish();                // rejected (ch01): `b` was moved by the call
                                       // `b.finish()`; `Builder.finish` takes `sink self`
    let j = d.finish();                // rejected (ch01 Rule 3): move out of a `let` parameter
    return n + m;
}
```

### H. Patterns

50. **T0050** — A pattern is checked against the scrutinee's type `S` (`synth`
    of the `match` head). `_`: any `S`. `let n`: any `S`, binds `n: S`. Integer
    literal (optionally `-`): `S` an integer type, value in range. String: `S =
    Str`. `true`/`false`: `S = bool`. Float literals MUST be rejected. Tuple:
    `S` a tuple of the same arity, componentwise. A `path` with no payload MUST
    resolve to a unit variant of enum `S` or to a `const` of type `S` whose
    type is an integer type, `bool` or `Str`; ch08 Rule 25 lets any
    module-scope entity through, so a bare pattern name that resolves to
    anything else — a `fn`, a struct, a trait, a prelude type, a variant
    that has a payload — MUST be rejected here, with the hint `to bind,
    write "let n"`. A `path` or `dot_lit` with a
    payload MUST name a variant of `S` (a `dot_lit` always means `S`'s variant)
    or, for a `{ }` payload, the struct `S` itself; a `( )` payload needs one
    sub-pattern per component, a `{ }` payload names visible fields at most
    once each, and omitted fields match anything. **Linear components**
    (round 6, ch01 Rule 22d(ii)): when the component a sub-pattern faces is
    of LINEAR type, `_`, an omitted `{ }` field and a literal pattern each
    DROP that component and MUST be rejected; the arm binds it with `let
    n`, or the whole value is moved instead of destructured. This is the
    one place a pattern's legality depends on ownership, and the code and
    diagnostic are ch01's.
51. **T0051** — A `let n` binding has the type of the component it faces, with
    the enum's or struct's arguments substituted. Whether it moves, copies or
    projects that component is ch01's; the type is the same in each case. The
    meaning of the `fpat` shorthand under the round-3 forms is ch08's.
52. **T0052** — Refutable patterns occur only in `match` arms. ch07's `binding`
    (in `let`, `var`, `for`) admits only names, `_` and tuples, all
    irrefutable, so no irrefutability check exists. Within a `match`, `_` and
    `let n` are irrefutable; a `const` pattern is refutable, like the literal
    of its value.
53. **T0053** — A `match` MUST be exhaustive. The checker runs the standard
    usefulness algorithm on the arm matrix: the match is exhaustive iff the
    all-wildcard row is not useful after the last arm. Constructors: an enum's
    variants (closed, Rule 6, so a non-local enum needs no wildcard arm and
    gaining a variant breaks its matches); `true`/`false`; the single
    constructor of a tuple or struct; integer and string literals, whose
    domains count as infinite, so such a column is exhaustive only through `_`
    or `let n`. `let n` is a wildcard for this algorithm: it covers every
    value of its column. A `const` pattern is the literal constructor of the
    constant's comptime value (ch04) and covers exactly that one value: two
    constants of equal value, or a constant and an equal literal, are the same
    constructor (the second arm is Rule 54's), and an arm list of `bool`
    constants `T` and `F` is exhaustive iff their values are `true` and
    `false`. The diagnostic names one uncovered value.
54. **T0054** — An arm that is not useful with respect to the arms before it
    MUST be rejected as unreachable.
55. **T0055** — Why this is cheap, and the guard. The grammar has no
    or-patterns, guards or range patterns, so specialising the matrix by a
    constructor never duplicates or splits a row and a column is only ever
    partitioned by the constructors that occur in it plus one default. The
    problem stays co-NP-hard in theory (wildcards over tuples of enums), so the
    computation is charged one step per row visited and MUST stop with T0055,
    asking for the match to be nested, after `MATCH_STEP_FACTOR` (256) times
    the match's pattern-node count: acceptance never depends on machine
    speed. The count is that of the PLAIN algorithm, so that it is the same
    in every implementation: for each usefulness query (one per arm, then
    the all-wildcard row), specialise the first column by each constructor
    that occurs in it, plus the default matrix when those constructors are
    not a complete signature, and charge one step per row of every matrix
    so formed, with no memoisation and no early exit other than an empty
    matrix or an exhausted column list. An implementation MAY compute the
    answer faster but MUST report T0055 exactly when the plain count of
    the whole match exceeds the budget.
56. **T0056** — Range patterns, or-patterns and guards are absent from ch07 and
    MUST NOT be accepted. Should or-patterns be added, every alternative MUST
    bind the same names with equal types.

```fors
enum Shape2 { circle(f64), rect { w: f64, h: f64 }, empty }
fn area(let s: Shape2) -> f64 {
    match s {
        Shape2.circle(let r) => r * r * 3.0,
        .rect { w: let w, h: let h } => w * h,
        .empty => 0.0,
        _ => 1.0,                         // rejected T0054: unreachable
    }
}
fn sign(let n: i32) -> i32 { match n { 0 => 0, -1 => -1 } }   // rejected T0053: e.g. 1
```

### I. Generic bodies and signatures

57. **T0057** — A generic declaration is checked once, at its definition, with
    each type parameter rigid. The only operations on a value of rigid type `T`
    are: binding it, passing it by a convention, moving it, storing it in an
    aggregate, dropping it IF `T` IS `Droppable`, `size_of` / `align_of`,
    and the methods and
    operators of `T`'s declared bounds (an operator needs its Rule 21 trait
    among the bounds; copying needs `Copyable`). **The drop clause**
    (round 6, ch01 Rule 22c): letting a value of rigid type go out of
    scope, `discard`ing it, matching it with `_`, or evaluating it as an
    expression statement MUST be rejected with this code unless `T`'s
    declared bounds include `Droppable`, `Copyable` or `Iterator` (each of
    the last two implies the first; for a neutral projection `P.A` the
    bounds are the trait's declaration for `A` plus the constraint entries
    in scope). Binding, passing, moving, storing and returning stay
    available for every rigid type. A generic body must therefore SAY in
    its signature that it drops, which keeps Rule 59 intact: the error is
    at the definition, against the bounds, never at an instantiation. A neutral projection `P.A`
    is a rigid type under this rule; its "declared bounds" are exactly the
    bounds the trait declares for `A` (Rule 16) plus the constraint entries
    on `P.A` in scope (Rule 62), and nothing is learnt from any impl. Fields, literals, `as`,
    patterns other than `_` and `let n`, and methods not provided by a bound
    MUST be rejected. Codes: an operator whose trait is not among the bounds
    is T0057; a method no bound provides is T0043; a field T0042; a literal
    T0027; `as` T0030; a pattern T0050. Without a `Copyable` bound a value
    use of a rigid-typed place is a move (Rule 23), never a copy, and
    whether that move is legal is ch01's, with ch01's code.
58. **T0058** — A brand parameter has no operations at all and occurs only as a
    brand argument (ch01 Rule 15d). A const parameter is a constant of its type
    in the body. `Shared` and `Copyable` bounds add no methods (Rule 24).
59. **T0059** — No error may depend on an instantiation. Every diagnostic is
    raised either at the definition, against the declared bounds, or at a use
    site, from the callee's signature and the signatures of the impls that
    normalisation reads (arity, kinds, bounds, constraint entries, inference,
    const-argument fit; an impl's `type A = T;` is signature, Rule 2); an instantiated body is never re-checked, no rule
    inspects which type a parameter received, and there is no specialisation.
    Hence both lowerings of ch03 Rule 16 are valid for every accepted program:
    each operation of Rule 57 is a witness-table entry (`size`, `align`,
    `copy`, `move`, `deinit`, a bound's method slot) or, monomorphised, its
    direct counterpart; a value of neutral type `P.A` uses the witness of `A`
    that `P`'s trait witness carries (how that witness is laid out is ch03
    Rule 16's to state).
60. **T0060** — The `raises` type of a signature is a type like any other (ch02
    Rule 1): it MAY be a type parameter (`fn try_apply[T, U, E, F: fn(let T) ->
    U raises E](let x: T, let f: F) -> U raises E`), determined by Rule 38.
    Nothing abstracts over *whether* a function raises: a non-raising function
    type never equals a raising one, and `never` is not inferred for `E` (Rule
    33). A combinator that must accept both is written twice.

### J. Projections and constraint entries

61. **T0061** — Projections. A projection is written as the dotted type path
    `P.A` and in no other way; ch08 Rules 16 and 22 hand the second segment
    to this rule. It is well-formed iff all of: (a) the path has exactly two
    segments (`I.Item.Item` MUST be rejected; a nested projection can arise
    only by substitution into a signature, where it is an ordinary neutral
    type, Rule 20(a)); (b) `P` is a *type* parameter in scope or `Self` — a
    brand or const parameter has no bounds and MUST be rejected, and so MUST
    a head that is a struct, enum, prelude type or trait ("write the type
    itself": a projection headed by a concrete type is not writable in v0.1;
    `Wrap[T].A` is not even a ch07 `type`); (c) exactly one trait among
    `P`'s bounds declares an associated type named `A` — none is "no
    associated type `A`", two or more (including two instantiations of one
    trait, `P: Index[usize] + Index[Key]`) is "ambiguous projection", and
    there is no qualified form in v0.1. For `Self` inside `trait Tr[Ps]` the
    bounds are `Tr[Ps]` alone (plus `Index[I]` inside `IndexMut[I]`, Rule
    21). For `Self` inside `impl Tr[As] for S`, `A` MUST be an associated
    type of `Tr` (of `Index` too, in an `IndexMut` impl) and `Self.A` is
    replaced at once by that impl's own definition (no lookup); inside an
    inherent impl `Self.A` MUST be rejected. (d) Inside the right-hand side
    of `type A = RHS;` a projection MUST be headed by one of the impl's own
    type parameters: `Self.B` there MUST be rejected (it would let `type A =
    Self.A;` or a two-step cycle be written). This is the premise of Rule
    20's termination argument. A projection MUST NOT occur in an impl head
    (Rule 18); it MAY occur anywhere else a type may: parameter, result and
    `raises` types, fields, payloads, the arguments of bounds, `fn` types,
    annotations of locals and explicit generic arguments.
62. **T0062** — Constraint entries. A `gconstraint` `P.A: Tr1 + ... + Trk`
    (ch07) adds bounds to the projection `P.A` and introduces no name. `P`
    MUST be a type parameter declared EARLIER in the same list, a type
    parameter of the enclosing `impl` or `trait`, or `Self` (scope and the
    earlier-than test: ch08 Rule 26); `P.A` MUST be a well-formed projection
    (Rule 61); every `Tri` MUST be a trait (no `brand`, no `fn` type, no
    const-kind type). A constraint entry is legal only in the `generics` of a
    `fn` — a `fn` item, a trait method, an impl method; in the list of a
    `struct`, `enum`, `trait` or `impl` it MUST be rejected. (On an `impl` it
    would make impl lookup recurse on a normalised projection, which is not a
    subterm of the goal, and Rule 12 would lose its termination argument;
    the other three would force every impl over the type to restate it. A
    method constrains a parameter of its impl instead: `impl[I: Iterator]
    Sum[I] { fn total[I.Item: Add + Copyable](...) }`.) Inside the function
    the entry's traits are bounds of the neutral type `P.A` (Rules 12, 43,
    57); at each use of the function they are checked, after Rule 38, on the
    normalised `P.A` (T0012). The traits of a constraint entry MAY themselves
    declare associated types (`I.Item: Iterator`): values of type `I.Item`
    then have methods whose signatures mention the neutral `I.Item.Item`,
    which is a legal type although Rule 61(a) gives it no spelling.

```fors
fn sum_all[I: Iterator, I.Item: Add + Copyable](sink it: I, let zero: I.Item) -> I.Item {
    var acc: I.Item = zero;                 // copy: the constraint entry gives Copyable
    for x in it { acc = acc + x; }          // `+`: the constraint entry gives Add
    return acc;
}
fn no_add[I: Iterator](sink it: I, let zero: I.Item) {
    for x in it { let y = zero + x; }       // rejected T0057: I.Item has no Add bound (Rule 29)
}
fn bad1[I.Item: Eq, I: Iterator]() { }      // rejected (ch08 Rule 26): head not declared earlier
fn bad2[I: Iterator, J: Iterator](sink a: I.Item) -> J.Item {
    return a;                               // rejected T0026: I.Item and J.Item are
}                                           // different neutral types
fn bad3[A: brand, T: Index[usize] + Index[i32]](let x: A.Item, let y: T.Output) { }
                                            // rejected T0061 twice: brand head; ambiguous
fn bad4(let x: Counter2.Item) { }           // rejected T0061: concrete head, write i64
```

## Not owned by this chapter

| Fact | Owner |
|---|---|
| Conventions, call-site markers, move/copy consequences, definite initialisation, exclusivity, `scoped` | ch01 R1-9, R19-19b |
| Qualifiers `iso`/`imm`, their conversions, sendability; `secret` propagation | ch01 R10-14; ch05 R6a-6b |
| Brands, `with arena`/`with allocator`, non-escape, `Own`/`Ref`/`Arena` | ch01 R15-18 |
| `Shared` field check and `atomic` | ch01 R21-21d |
| `raises`, `?`, handler legality, `ErrorFrom` hop count, traps, contracts | ch02 R1-5, R9-12, R15 |
| Integer/float semantics, `as` semantics, literal range, `wrap_`/`sat_`/`unchecked_` | ch03 R1-9 |
| Array/vector/mask literal typing, `.splat`, `Slice` by range-index | ch03 R21-24a |
| Which positions are CHECK positions | ch03 R25 |
| Monomorphise vs witness table, instantiation cache, `@specialize` | ch03 R16-18 |
| Comptime evaluation of const arguments and `const` initialisers | ch04 R11-15 |
| Root-capability types and their opacity; `asm_expr` typing | ch04 R7-8, R21, R27 |
| Layout, alias classes, `soa` representation | ch05 |
| Scope lookup, path heads, visibility definitions, orphan rule, prelude list | ch08 R10-18, R21-27 |
| Deferral of a projection's second segment; scope and earlier-than test of a constraint entry's head; duplicate member names in one trait or impl (associated types included) | ch08 R16, R22, R26, R27 |
| Syntax of `type A;`, `type A = T;`, `gconstraint`; `type` reserved; the `.`-versus-`:` lookahead | ch07 Grammar, Disambiguation 19-20 |
| Whether an implicit receiver move is legal (use after move, loops, partial moves, `let`/`inout` parameters, captures, `spawn`, qualifiers) | ch01 R2-4a, R8, R12-13 |

## Drafting decisions

- **Expected type before arguments** (Rule 38(c)). Alternative: bind from
  arguments first and use the expected type last. Rejected because `let b:
  Option[u8] = some(1);`, `Buffer.fixed(4096)` and `none` in a field
  initialiser (all attested in ch01/ch04) would mistype or fail; both orders
  are solver-free.
- **Associated types instead of bound propagation** (owner decision round 4;
  Rules 16-20, 38, 61-62). The draft's self-determined traits (old Rule 20)
  and the "Bound propagation" paragraph of Rule 38, with its example and five
  tests, are deleted: `I.Item` is a function of `I`, so nothing propagates.
  What keeps this inside Rule 1 and the near-linear gate: impl heads carry no
  projections, so overlap stays first-order and blind to associated types
  (Rules 18-19); right-hand sides project only on impl parameters, so
  normalisation is structural descent (Rules 20, 61(d)); a neutral projection
  is a rigid type, never a variable; one-way matching skips projections and
  one final equality check compares them (Rule 38(e)).
- **Constraint entries only on `fn` generics** (Rule 62). The owner's design
  allows them in "the generics list"; this draft restricts *where*: not on
  `impl` (an impl bound on `T.A` makes Rule 12 recurse on a normalised
  projection, which can be larger than the goal — `impl[T: Tr, T.A: Tr] Tr for
  Wrap[T] { type A = Wrap[T.A]; }` with `Base.A = Wrap[Wrap[Base]]` never
  terminates), and not on `struct`/`enum`/`trait` (every impl over such a type
  would need the entry the previous clause forbids). ch07 parses them
  everywhere; the rejection is T0062. Liftable later (Open question 4).
- **`IndexMut[I]` has a language-known prerequisite `Index[I]`** and no
  `Output` of its own (Rule 21). Alternative: both declare `Output`. Rejected:
  `P: Index[usize] + IndexMut[usize]` would make `P.Output` ambiguous (Rule
  61(c)) and a read and a write of `a[i]` would have two unrelated neutral
  types in generic code. It is one closed special case, not supertraits.
- **Index with several impls synthesises the index** and rejects an
  unsuffixed literal there (Rule 29), so a new `Index` impl can break, never
  re-route, an existing `a[0]`.
- **`Self.A` inside an impl** is that impl's own definition, by table lookup,
  in method signatures and bodies, but is rejected inside `type A = RHS;`
  (Rule 61(c)-(d)).
- **Nested neutral projections exist but cannot be written** (Rules 61(a),
  62): a constraint entry or a trait-declared bound may name a trait that has
  associated types; the resulting `I.Item.Item` appears only by substitution.
  Decided "allowed" because forbidding it would forbid `type Iter: Iterator;`.
- **The `map_sum` example declares `U: Add + Copyable`** and the call writes
  `map_sum(move xs, ...)`: the owner's sketch had `U: Add` and an unmarked
  `xs`, but its body must copy `zero` out of a `let` parameter (ch01 Rule 3)
  and `xs` is an argument, not a receiver, so ch01 Rule 2 marks it. The
  inference shown is unchanged.
- **Implicit receiver move** (owner decision round 4; Rule 46). The draft's
  `(move x).m()`-only rule is gone; the visibility ch01 Rule 2 loses is bought
  back by the mandatory diagnostic detail.
- Round-3 checker obligations now stated: a bare pattern name resolving to a
  `fn`, struct, trait or prelude type is T0050 (Rule 50); a value binding
  used as a type-path head is T0011 (Rule 11); `let n` is a wildcard and a
  `const` pattern a one-value constructor for exhaustiveness (Rules 52-53).
- Drafting defaults taken by the orchestrator, round 4: the prelude gains this
  chapter's language-known names (ch08 Rule 17); variant versus associated
  function is an error (Rule 48); `MATCH_STEP_FACTOR` = 256 until measured.
- **Bound-by-earlier-argument means CHECK.** ch03 Rule 25 lists a generic call
  argument as SYNTH "while the parameter type still mentions a generic
  parameter"; Rule 38(d) reads "still" as "still undetermined", which is ch03's
  own definition of a complete expected type. ch03's wording should say so.
- **Operator right operands are call arguments**, hence CHECK under ch03 Rule
  25, plus one syntactic literal-on-the-left exception (Rule 29). Alternative:
  literal-typed values that adopt a type later; rejected by Rule 1. Positions
  checked here that ch03 Rule 25's list omits and should cite: index operand,
  `raise` operand, handler block, `grain` expression, function-body tail.
- **Homogeneous operator traits** (confirmed by the owner, round 4).
  Alternative `Mul[R]` with `type Output` (design doc). Not taken for v0.1
  although associated types now exist: a parameterised `Mul` needs overload
  resolution on the right operand. Scalar-times-vector is a method or `.splat`.
- **No associated consts, supertraits, generic associated types, defaults or
  equality bounds** (Rule 16): none is needed by the language-known traits,
  and each can be added without breaking accepted code.
- **No blanket impls** (Rule 18). Alternative: allow them and detect cycles
  during impl lookup. Rejected: lookup would stop being structural recursion,
  and a blanket impl overlaps every other impl anyway.
- **`Copyable` is the name** (ch01 Rule 4, ch03 Rule 24a and ch04 Rule 7
  already use it), modelled on `Shared`: checked marker, defining module.
- **Method candidates by module-graph edge, not by scope** (Rule 43).
  Alternative: "trait in scope" as in Rust; rejected because ch08 Rule 22
  forbids checker scope lookup and `use` binds modules, not traits.
- **Inherent before trait; otherwise ambiguity is an error** (Rule 44).
- **No const arithmetic on parameters** (Rule 13), although ch07 parses
  `Array[T, N + 1]`: it is the one feature that would need post-instantiation
  errors.
- Smaller calls: the infinite-size test is per declaration and conservative
  (Rule 14); literal defaults `i32`/`f64` match ch03's `[1, 2, 3]` example; an
  unreachable arm is an error, not a lint; the exhaustiveness budget is a
  function of the match's size, never of time.
- Self-review 2026-09-19, holes closed: overlap via `Self` (Rule 8; ch08
  keeps `Self` out of an impl header, so the corpus probes renaming apart
  instead); overlap
  undecidable through projections (none exist); unbounded operations and copies
  in generic bodies (Rule 57); brand escaping a `with` block by inference (Rule
  40); `Shared` bound met by an `@unsafe` impl (Rule 12); foreign enum growth
  (Rules 6, 53); `never` in bindings and inferred arguments (Rule 33);
  impl-lookup non-termination (Rules 12, 18); `1 + x` under left-keyed
  operators (Rule 29); closure result flowing outward (Rule 41: the closure is
  identified syntactically before it is typed).
- Self-review round 4, probes and the rule that answers each. Overlap through
  associated types: impossible, heads have no projections and Rule 19 never
  reads a definition (Rules 18-19). Normalisation cycle: `type A =
  Wrap[T].A;` is not a ch07 `type` (`.A` cannot follow `]`), `type A =
  Wrap.A;` / `S.A` is a concrete head (Rule 61(b)), `type A = Self.A;` is
  Rule 61(d). Projection on a brand or const parameter: Rule 61(b).
  Projection whose bound comes only from a constraint entry on another
  projection: not writable (Rule 61(a)), legal as a substituted neutral type
  (Rule 62). `Self.Item` inside the trait: neutral, Rule 61(c) with Rule 8.
  Impl-lookup non-termination through an impl-level constraint entry: Rule
  62 forbids the entry. A parameter occurring only under a projection: never
  bound, T0039 (Rule 39). Literal argument typed before its projection's head
  is bound: synthesised as `i32`, compared in Rule 38(e), never revised.
  Implicit receiver move of a place captured by a closure or `spawn`, of a
  `secret` value, or on an `iso`/`imm` place: Rule 46 adds no ownership rule
  and defers to ch01/ch05 on exactly the terms of `(move x).m()`, so no
  contradiction can be introduced. Single pass (Rule 1): normalisation and
  impl lookup are memoised functions of closed inputs called at substitution
  time; the only deferred work is Rule 38(e), which is inside the one call.

- Verification round 4 (adversarial review of the draft above), holes
  closed with the rule that now closes each. (1) Impl lookup and
  normalisation could diverge through a bounded impl parameter that occurs
  only in the trait arguments (`impl[U: Tr[Wrap[U]]] Tr[U] for Foo` plus
  `impl[V: Tr[Wrap[V]], W] Tr[V] for Wrap[W]`): Rule 18 now requires every
  bounded impl parameter to occur in the self type, so both recursions
  descend on the self type (Rules 12, 20). (2) The infinite-size test
  missed `struct S[I: Iterator] { x: I.Item }` with `type Item = S[Foo];`:
  Rule 14 adds one graph node per associated type; conservative (an
  iterator yielding a struct that holds a by-value projection field of the
  same trait is a false positive), see open question 8. (3) `let x =
  return;` is not ch07 syntax: Rule 33 now uses a `-> never` call. (4) The
  match budget (Rule 55) depended on whether an implementation exits early
  on an all-wildcard row; the plain count is now normative. (5) An
  operator on a rigid type without the bound was T0029 in Rule 29 and
  T0057 in Rule 57: Rule 29 now says T0057 for rigid operands, and Rule
  57 lists every code it delegates to. (6) `copy-without-copyable`: a value
  use of a non-`Copyable` rigid place is a move (Rule 23), so the error is
  ch01's, never T0057. (7) `for x in it` moves its iterable (Rule 31), so
  the `sink it: I` examples satisfy ch01 Rule 4. (8) ch01 had no rule for
  use after move, moves in loops, partial moves, moves out of `inout` or
  captured places — the implicit receiver move leaned on nothing: ch01
  Rule 4a now states each clause, and Rule 46 cites them one by one. (9)
  ch08 keeps `Self` out of impl headers, so "overlap via Self" cannot be
  written; the corpus probes parameters renamed apart. Every probe the
  task listed is a corpus test: mutually recursive impls across two traits
  (`normalise-mutually-recursive-impls-accepted`), a right-hand side
  projecting on a parameter that occurs only under another projection
  (`projection-in-impl-head-rejected`, `impl-param-only-in-assoc-type-
  rejected`), overlap through associated types (`overlap-ignores-assoc-
  types-rejected`, `overlap-ignores-bounds-rejected`), impls that would
  unify only after normalisation (`neutral-projection-does-not-match-
  concrete-impl-rejected`), an ambiguous projection reached through a
  constraint entry (`constraint-entry-ambiguous-projection-rejected`),
  `I.Item.Item` (ch07 `generics-constraint-three-segments-reject`, ch09
  `projection-three-segments-rejected`, `constraint-entry-with-assoc-trait-
  accepted`), `Self.Item` in a provided body (`assoc-type-in-provided-body-
  accepted`), a projection field (`projection-in-struct-field-accepted`,
  `recursive-through-assoc-type-rejected`), the closure before its
  iterator (`closure-before-its-iterator-rejected`), and the five receiver-
  move shapes (`implicit-receiver-move-*-rejected`).


## Closed by owner decision 2026-09-20, round 6

**O3 — iterator method chaining works under this chapter AS WRITTEN.** The
mechanism is PROVIDED methods on `Iterator` (Rule 16) returning CONCRETE
adaptor structs, each carrying an ordinary struct-headed `impl Iterator`.
No blanket impl is involved (Rule 18 is untouched), and Rules 16, 18, 19,
20, 38-41, 43-46, 57 and 61 needed no change. The derivation, for
`v.iter().map(double).take(3).count()`:

- Rule 43 tier (2) finds `Iterator.map` for a concrete receiver
  (`Iterator` is a prelude trait and the `impl` for `SliceIter`'s head is
  in the module defining that head), for a rigid receiver (`I: Iterator`:
  "the candidate traits are exactly its bounds") and for an adaptor
  receiver (`Mapped`'s own `impl Iterator`, found by Rule 12). A provided
  method is a candidate like a required one, and there is no Rule 44
  ambiguity.
- Rule 38(b) binds `Self` from the receiver BEFORE any argument is visited
  in (d), so the parameter type `fn (sink Self.Item) -> U` is always
  normalised through the impl (Rule 20(b)) for a concrete `Self`, or
  neutral (Rule 20(a)) for a rigid one, when the callable argument is
  checked. A closure argument is then handled by Rule 41, which binds `U`
  from the closure's body; a `fn` item binds `U` by the one-way match of
  Rule 38(d).
- The provided body is checked once with `Self` rigid (Rule 16): the
  struct literal `Mapped { src: self, f: f }` is typed as a call (Rule 34)
  whose parameters are determined from the CHECK position (Rule 38(c)),
  `Mapped[Self, U]` is well-formed because `Self`'s one bound inside the
  trait is `Iterator` (Rule 8), and the field types agree by Rule 9's
  equality on neutral projections.
- `dyn` capability is already lost for `Iterator` (Rule 25: it declares an
  associated type), so nothing is given up by the generic provided methods.

Two consequences are normative and recorded above: Rule 43's sentence that
a provided method is a lookup candidate and that no std iterator type may
declare an inherent method of the same name; and Rule 21's statement that
`Iterator` now has a language-known prerequisite (`Self: Droppable`,
`type Item: Droppable`).

**Two declaration choices that this chapter forces**, recorded so the std
stage does not "simplify" them back:
- A CALLABLE PARAMETER MUST BE A `fn` TYPE, never a callable type
  parameter. With `fn map[U, F: fn (sink Self.Item) -> U](sink self, let
  f: F)`, a `fn`-item argument binds `F` only; `U` occurs in no parameter
  type, and Rule 38 never binds anything through a BOUND, so
  `it.map(double)` is T0039. With a `fn` type the item's type is matched
  componentwise (Rule 7) and binds `U`, and a closure argument is handled
  by Rule 41. The second benefit is that the adaptor types stay WRITABLE
  (`Taken[Mapped[SliceIter[i32], i32]]`), since no closure type appears in
  a signature and a closure type "cannot be written" (Rule 7).
- AN ADAPTOR CARRIES EVERY PARAMETER IT NEEDS IN ITS OWN HEAD
  (`Mapped[I, U]`, not `Mapped[I]`), because `impl[I: Iterator, U]
  Iterator for Mapped[I]` would leave `U` unconstrained (Rule 18: "an
  occurrence only in a bound, in `type A = ...;` or in a method does not
  count").

A callable FIELD is called as `(self.f)(move x)`. `self.f(x)` is
method-call form (Rule 43) and is T0043: there are no method values (Rule
42), and a value of `fn` type is called with `( )` (Rule 7).

**Round-6 verification, two corrections.** (1) `Mapped[I, U]`'s impl MUST
bound `U: Droppable`: the trait declares `type Item: Droppable` (Rule 21)
and Rule 17 checks `type Item = U;` against that bound at the impl with
`U` rigid, so `impl[I: Iterator, U] Iterator for Mapped[I, U]` is T0021 as
written; `map[U: Droppable]` carries the same bound so that a closure
returning a LINEAR value fails at `map` with T0012 ("`Vec[..]` is not
`Droppable`") instead of at the next stage with "no method `take`". An
iterator of linear items does not exist in v0.1, by Rule 21. (2) A closure
argument that captures is a scoped value (ch01 Rule 19d), and the caller
accounts for the callable the adaptor stores through ch01 Rule 19c(a′):
`Mapped[Self, U]` CONTAINS the `fn` type `f` went in through, so
`v.iter().map(|sink x| x + k)` keeps `v` and `k`; typing is unchanged.
A generic `fn` item passed where a `fn` type is expected but not yet
complete is SYNTHESISED and is T0039 by Rule 28 (`it.map(same)` needs
`it.map(same[I.Item])`); a non-generic item binds `U` by the one-way match.
(3) The verification re-derived the three-adaptor chain
`v.iter().map(double).filter(small).take(3).count()` rule by rule:
Rule 43 tier (2) at each stage (`Iterator` is a prelude trait; the impl
for `SliceIter`, `Mapped`, `Filtered` is in its head's defining module, so
NO import is needed); Rule 38(b) binds `Self` from the receiver, (d)
normalises `fn (sink Self.Item) -> U` to `fn (sink i32) -> U` and the
one-way match against `double`'s type binds `U := i32`; Rule 12 then
checks `U: Droppable`; each stage's result is `Mapped[SliceIter[i32],
i32]`, `Filtered[Mapped[..]]`, `Taken[Filtered[..]]`, and `count` is
`usize`. In a CHECK position (`var t: Taken[Mapped[SliceIter[i32], i32]]
= ...`) Rule 38(b) still binds `Self` from the receiver first and (c)
merely agrees; a disagreeing annotation is T0026 at the call. Through a
bound (`fn f[I: Iterator](sink it: I)`) tier (2) is exactly the bound and
`Self.Item` stays neutral, so the closure is CHECKed against `fn (sink
I.Item) -> U` and its body synthesises `U`. With a second trait in the
bounds that also declares `take`, tier (2) has two candidates and the
call is T0044; the qualified form `Iterator.take(move it, 3)` resolves it.

**O1 — linearity's obligations on the checker** are ch01 Rules 22-22i;
this chapter carries the five clauses those rules delegate to it: Rule
10(c) (no `dyn` of a linear, rigid or neutral-projection value), Rule 11
(no concrete `Array`/`vector`/`atomic` of a linear element), Rule 21
(`Iterator`'s prerequisites), Rules 23-24 (`Copyable` excludes linear;
`Linear` and `Droppable` as markers, `Droppable` with no impls), Rule 50
(`_`, an omitted field or a literal over a linear component) and Rule 57
(the drop clause for rigid types). **O2 — `defer`/`errdefer`** cost this
chapter two sentences: Rule 31 (the statement and its body have type
`()`) and Rule 33 (no `return`, `raise`, `?` or outward `break`/`continue`
inside a body).

```fors
needs { };

// The shape of every adaptor: a provided method returning a concrete
// struct that carries its own struct-headed impl. No blanket impl.
pub trait Iterator {
    type Item: Droppable;
    fn next(inout self) -> Option[Self.Item];
    fn take(sink self, let n: usize) -> Taken[Self] {
        return Taken { src: self, left: n };        // Rules 34, 38(c)
    }
}

pub struct Taken[I: Iterator] { src: I, left: usize }

impl[I: Iterator] Iterator for Taken[I] {
    type Item = I.Item;                             // Rule 61(d)
    fn next(inout self) -> Option[I.Item] {
        if self.left == 0 { return none; }
        self.left = self.left - 1;
        return self.src.next();
    }
}
```

## Open owner questions

Closed in round 4 and removed from this list: the integer-literal default
(`i32`), homogeneous operators, associated types, the `sink self` receiver
(owner); prelude additions, variant versus associated function,
`MATCH_STEP_FACTOR` (drafting defaults, see Drafting decisions).

1. **Remaining v0.1 restrictions**, each addable later without breaking
   accepted code: no blanket impls or supertraits (Rules 16, 18 — round 6
   confirmed that iterator method chaining needs NEITHER, so nothing in
   std or the corpus is now waiting on them; `Iterator` joins `IndexMut`
   as the second trait with a language-known prerequisite, which is still
   not a supertrait feature); no generic
   associated types, defaults, associated consts or equality bounds (Rule 16);
   no arithmetic on const parameters (Rule 13, although ch07 parses `N + 1`);
   no effect polymorphism, so std writes `map`/`try_map` pairs (Rule 60).
   Recommended: accept all.
2. **Qualified projection form.** `P: Index[usize] + Index[Key]` makes
   `P.Output` ambiguous and nothing can name either (Rule 61(c)).
   Recommended: add `(P as Tr).A` later, when std first needs it; it needs a
   ch07 production, so decide before the grammar freeze whether to reserve the
   shape.
3. **Projection headed by a concrete type** (`Counter2.Item`, `Vec[T].Item`)
   is not writable (Rule 61(b)). Recommended: keep for v0.1 (the type itself
   can always be written); lifting it needs `type_app "." ident` in ch07 and a
   termination re-argument for right-hand sides, and is compatible.
4. **Constraint entries only on `fn` lists** (Rule 62, a drafting
   restriction, not the owner's). Recommended: keep for v0.1; lifting it on
   `impl` needs a termination measure (or a step budget like Rule 55) for
   impl lookup.
5. **Associated consts** (`const N: usize;` in a trait). Recommended: not in
   v0.1; a parameterless method covers values, and a const usable in type
   position would reopen Rule 13's post-instantiation-error problem.
6. **`IndexMut`'s language-known prerequisite** (Rule 21). Recommended:
   confirm; the alternative is general supertraits.
7. **Nested projection spelling** (`I.Item.Item`, Rule 61(a)). Recommended:
   not in v0.1; add together with question 2.
8. **Bounded impl parameters must occur in the self type** (Rule 18) and
   **the associated-type node of the infinite-size test** (Rule 14) are
   the verification round's containments; the first rejects `impl[E:
   Display] From[E] for MyErr`-style impls, the second gives a false
   positive for an iterator that yields a struct holding a by-value
   projection field of the same trait. Recommended: keep both for v0.1
   (each is liftable without breaking accepted code; lifting the first
   needs a termination measure over trait arguments, the second a
   per-instantiation size check that Rule 59 currently forbids).

## Conformance tests

All in `tests/conformance/09-types/` (186 tests, one per name below; the
list is generated from the corpus directives and MUST stay equal to it);
`-accepted` expects `check-ok`, `-rejected` expects `check-error` with the
code shown, which is also the first token of the test's `detail`. A ch01
code means the receiver move (or a value use of a non-`Copyable` place) is
decided by that ch01 rule; `implicit-receiver-move-then-use-rejected`'s
`detail` MUST name the consuming call and the `sink self` declaration
(Rule 46). Until a type checker exists, `fors check` is CLEAN on every
T- and ch01-coded test and reports exactly the named ch08 code on the
others (crates/fors-resolve/tests/conformance.rs, `ch09_types_corpus_
resolver_view`).

R1 `let-without-type-or-init-rejected` T0001,
`literal-default-ignores-later-use-rejected` T0026; R7
`fn-item-as-value-accepted`, `generic-fn-value-without-args-rejected` T0039;
R9 `brand-identity-mismatch-rejected` T0026,
`nominal-structs-distinct-rejected` T0026; R10 `array-to-slice-rejected`
T0026, `concrete-to-dyn-accepted`, `never-coerces-accepted`; R11
`local-shadowing-prelude-type-as-type-head-rejected` T0011 (renamed and
re-aimed at a prelude TYPE by round 5's D3, the prelude having no modules
left to shadow),
`type-arity-rejected` T0011; R12 `bound-unsatisfied-rejected` T0012,
`bound-via-generic-impl-accepted`; R13
`const-arg-arithmetic-on-param-rejected` T0013, `const-param-float-rejected`
T0013; R14 `projection-field-behind-own-accepted`, `recursive-struct-rejected`
T0014, `recursive-through-assoc-type-rejected` T0014,
`recursive-via-ref-accepted`; R15 `mixed-trait-and-type-bound-rejected` T0015;
R16 `assoc-type-bound-mentions-other-assoc-type-accepted`,
`assoc-type-bound-not-a-trait-rejected` T0016,
`assoc-type-bounded-declared-accepted`, `assoc-type-declared-accepted`,
`assoc-type-in-provided-body-accepted`, `provided-method-accepted`,
`provided-method-uses-foreign-op-rejected` T0057,
`self-receiver-wrong-type-rejected` T0016; R17
`assoc-type-bound-met-by-projection-accepted`,
`assoc-type-bound-violated-at-impl-rejected` T0017,
`assoc-type-defined-accepted`, `assoc-type-duplicate-in-impl-rejected` (ch08
code N0027), `assoc-type-extra-in-impl-rejected` T0017,
`assoc-type-in-inherent-impl-rejected` T0017,
`assoc-type-missing-in-impl-rejected` T0017,
`impl-method-signature-normalised-accepted`,
`impl-method-signature-projection-mismatch-rejected` T0017,
`impl-missing-method-rejected` T0017; R18 `blanket-impl-rejected` T0018,
`bounded-impl-param-only-in-trait-args-rejected` T0018,
`impl-param-only-in-assoc-type-rejected` T0018,
`projection-in-impl-head-rejected` T0018,
`unbounded-impl-param-in-trait-args-accepted`,
`unconstrained-impl-brand-param-rejected` T0018,
`unconstrained-impl-param-rejected` T0018; R19
`overlap-generic-vs-concrete-rejected` T0019,
`overlap-ignores-assoc-types-rejected` T0019,
`overlap-ignores-bounds-rejected` T0019, `overlap-renamed-params-rejected`
T0019; R20 `neutral-projection-does-not-match-concrete-impl-rejected` T0043,
`neutral-projection-equals-itself-accepted`,
`neutral-projection-matches-generic-impl-accepted`,
`neutral-projections-distinct-params-rejected` T0026,
`normalise-mutually-recursive-impls-accepted`,
`normalise-nested-adaptors-accepted`, `projection-head-without-impl-rejected`
T0012, `projection-normalises-after-substitution-accepted`; R21
`compound-assign-via-add-accepted`, `index-two-index-types-accepted`,
`indexmut-output-is-index-output-accepted`, `indexmut-without-index-rejected`
T0021, `operator-trait-has-no-output-rejected` T0017,
`operator-via-impl-accepted`; R22 `and-on-non-bool-rejected` T0030; R23
`copyable-fieldwise-accepted`, `copyable-with-own-field-rejected` T0023; R24
`dyn-marker-rejected` T0024; R25 `dyn-generic-method-rejected` T0025,
`dyn-trait-with-assoc-type-rejected` T0025; R27
`int-literal-to-float-rejected` T0027,
`literal-against-neutral-projection-rejected` T0027,
`literal-against-param-rejected` T0027, `literal-checks-to-u8-accepted`; R28
`none-in-synth-rejected` T0039; R29 `index-literal-with-two-impls-rejected`
T0029, `index-suffixed-with-two-impls-accepted`,
`literal-left-operand-accepted`, `mixed-width-operands-rejected` T0026,
`operator-missing-impl-rejected` T0029; R30 `if-condition-non-bool-rejected`
T0030; R31 `for-element-type-from-item-accepted`,
`for-element-type-mismatch-rejected` T0026, `for-over-non-iterable-rejected`
T0031, `for-over-rigid-iterator-accepted`,
`for-over-rigid-non-iterator-rejected` T0031, `return-value-mismatch-rejected`
T0026; R32 `if-branch-mismatch-rejected` T0026,
`if-branches-first-fixes-accepted`, `if-first-branch-never-accepted`; R33
`let-never-rejected` T0033, `never-not-inferred-rejected` T0039; R34
`dot-lit-in-synth-rejected` T0034,
`struct-literal-args-from-expected-accepted`,
`struct-literal-missing-field-rejected` T0034; R35
`closure-checked-against-fn-type-accepted`,
`closure-synth-unannotated-rejected` T0035; R36 `handler-block-type-rejected`
T0026; R37 `named-arg-wrong-label-rejected` T0037; R38
`binding-never-revised-rejected` T0026, `infer-from-expected-type-accepted`,
`infer-from-first-argument-accepted`, `map-sum-closure-checked-accepted`,
`projection-arg-before-head-accepted`,
`projection-arg-before-head-final-check-rejected` T0026,
`projection-result-against-expected-accepted`; R39 `cannot-infer-rejected`
T0039, `param-only-under-projection-explicit-accepted`,
`param-only-under-projection-rejected` T0039; R40
`brand-inferred-for-callee-accepted`, `two-brands-one-param-rejected` T0026;
R41 `callable-bound-closure-accepted`, `closure-before-its-iterator-rejected`
T0035, `closure-before-its-type-source-rejected` T0035; R42
`field-on-type-param-rejected` T0042; R43 `inherent-before-trait-accepted`,
`method-on-bound-accepted`, `method-on-projection-via-trait-bound-accepted`,
`trait-method-without-edge-rejected` T0043; R44
`two-traits-same-method-rejected` T0044; R45 `qualified-trait-call-accepted`;
R46 `explicit-move-receiver-accepted`, `implicit-receiver-move-accepted`,
`implicit-receiver-move-in-closure-rejected` (ch01 Rule 4a(e)),
`implicit-receiver-move-in-loop-rejected` (ch01 Rule 4a(b)),
`implicit-receiver-move-of-field-rejected` (ch01 Rule 4a(c)),
`implicit-receiver-move-of-inout-param-rejected` (ch01 Rule 4a(d)),
`implicit-receiver-move-of-let-param-rejected` (ch01 Rule 3),
`implicit-receiver-move-then-use-rejected` (ch01 Rule 4a(a)),
`inout-receiver-unmarked-accepted`, `let-receiver-unmarked-accepted`,
`no-auto-deref-own-rejected` T0043,
`qualified-call-sink-receiver-needs-move-rejected` (ch01 Rule 2),
`sink-receiver-copyable-not-moved-accepted`, `sink-receiver-rvalue-accepted`;
R47 `bracket-instantiates-method-accepted`; R48
`duplicate-method-across-impls-rejected` T0048,
`method-named-as-field-rejected` T0048,
`variant-and-assoc-fn-same-name-rejected` T0048; R50
`pattern-bare-fn-name-rejected` T0050, `pattern-bare-prelude-type-rejected`
T0050, `pattern-bare-struct-name-rejected` T0050,
`pattern-float-literal-rejected` T0050; R51 `let-binding-in-pattern-accepted`;
R53 `match-bool-consts-exhaustive-accepted`,
`match-const-pattern-needs-wildcard-rejected` T0053,
`match-foreign-enum-no-wildcard-accepted`, `match-int-needs-wildcard-rejected`
T0053, `match-let-pattern-covers-all-accepted`,
`match-non-exhaustive-enum-rejected` T0053; R54
`arm-after-let-pattern-unreachable-rejected` T0054,
`const-pattern-equal-to-literal-unreachable-rejected` T0054,
`unreachable-arm-rejected` T0054; R55 `match-budget-exceeded-rejected` T0055,
`match-budget-within-accepted`; R57 `copy-with-copyable-accepted`,
`copy-without-copyable-rejected` (ch01 Rule 3),
`projection-op-via-trait-declared-bound-accepted`,
`projection-op-without-constraint-rejected` T0057,
`unbounded-op-on-param-rejected` T0057; R58
`brand-param-as-value-type-rejected` (ch01 Rule 15d); R59
`generic-checked-at-definition-rejected` T0057; R60
`generic-raises-type-accepted`, `raising-closure-to-plain-fn-type-rejected`
T0026; R61 `assoc-type-rhs-self-projection-rejected` T0061,
`assoc-type-rhs-two-step-self-cycle-rejected` T0061,
`projection-ambiguous-rejected` T0061, `projection-in-struct-field-accepted`,
`projection-on-brand-param-rejected` T0061,
`projection-on-concrete-head-rejected` T0061, `projection-on-param-accepted`,
`projection-on-self-in-trait-accepted`, `projection-self-in-impl-accepted`,
`projection-three-segments-rejected` T0061,
`projection-unknown-assoc-type-rejected` T0061,
`self-projection-in-inherent-impl-rejected` T0061; R62
`constraint-entry-accepted`, `constraint-entry-ambiguous-projection-rejected`
T0061, `constraint-entry-brand-head-rejected` T0061,
`constraint-entry-head-not-earlier-rejected` (ch08 code N0026),
`constraint-entry-in-impl-generics-rejected` T0062,
`constraint-entry-in-struct-generics-rejected` T0062,
`constraint-entry-non-trait-bound-rejected` T0062,
`constraint-entry-on-impl-param-in-method-accepted`,
`constraint-entry-satisfied-at-call-accepted`,
`constraint-entry-unsatisfied-at-call-rejected` T0012,
`constraint-entry-with-assoc-trait-accepted`.

Removed in round 4: R20 `two-iterator-impls-rejected`; R38's five
bound-propagation tests (`generic-arg-from-iterator-bound-accepted`,
`closure-param-from-iterator-bound-accepted`,
`rigid-param-iterator-bound-propagates-accepted`,
`non-self-determined-bound-does-not-bind-rejected`,
`iterator-bound-no-impl-rejected`); R46 `sink-receiver-needs-move-rejected`;
R19 `overlap-via-self-rejected` (not writable: ch08 keeps `Self` out of an
impl header; replaced by `overlap-renamed-params-rejected`). Rules 2, 49
and 52 have no corpus test: 2 is an incremental-build property (tested in
the query engine: `assoc_type_def_is_signature_level_and_method_bodies_
are_not` in crates/fors-index), 49 re-uses ch08's tests, 52 is a fact
about the grammar. Rule 56 has none: it forbids syntax ch07 does not have.

Added in round 6 (2026-09-20), all in `tests/conformance/09-types/` unless
another chapter is named; each `-rejected` expects a `check-error` with the
code shown, and `fors check` (the resolver) stays CLEAN on every one of
them, as for every other T- and ch01-coded test.

R10(c) `rigid-to-dyn-rejected` T0010, `neutral-projection-to-dyn-rejected`
T0010, `linear-to-dyn-rejected` T0010, `dyn-param-in-generic-body-accepted`.
R11 `linear-array-element-rejected` T0011,
`linear-vector-element-rejected` T0011,
`linear-atomic-element-rejected` T0011,
`rigid-array-element-in-generic-body-accepted`.
R21 `iterator-impl-linear-self-rejected` T0021,
`iterator-impl-linear-item-rejected` T0021,
`iterator-bound-implies-droppable-accepted`,
`iterator-item-dropped-in-generic-body-accepted`.
R23 `linear-copyable-impl-rejected` T0023,
`copyable-implies-droppable-accepted`.
R24 `droppable-impl-rejected` T0024,
`linear-impl-with-bound-rejected` T0024 (ch01 R22),
`linear-bound-adds-no-operation-rejected` T0057.
R31 `defer-body-checks-against-unit-accepted`,
`defer-body-with-value-rejected` T0026.
R33 `defer-return-inside-rejected` T0033,
`defer-raise-inside-rejected` T0033,
`defer-question-inside-rejected` T0033,
`defer-break-outer-loop-rejected` T0033,
`defer-inner-loop-break-accepted`.
R12 `adaptor-map-closure-returns-linear-rejected` T0012 (`U: Droppable`).
R17/R21 `adaptor-impl-unbounded-item-rejected` T0021 (`type Item = U;`
with `U` unbounded).
R26 `adaptor-annotated-binding-mismatch-rejected` T0026 (CHECK position
disagreeing with the receiver-bound `Self`).
R28 `adaptor-generic-fn-item-uninstantiated-rejected` T0039.
R43 (O3) `adaptor-chain-method-accepted` (three adaptors, `fn` items),
`adaptor-chain-closure-accepted` (`U` from a closure body, un-annotated
binding), `adaptor-chain-rigid-receiver-accepted` (`I: Iterator`, result
`Mapped[I, I.Item]`), `adaptor-chain-on-adaptor-receiver-accepted`,
`adaptor-provided-method-shadowed-by-inherent-rejected` (ch10 R34),
`adaptor-name-clash-two-traits-rejected` T0044,
`adaptor-name-clash-qualified-accepted` (`Iterator.take(move it, 3)`),
`adaptor-on-inout-receiver-rejected` (ch01 R4a(d); the `detail` names
`Iterator.map`'s `sink self`, Rule 46),
`adaptor-on-field-receiver-rejected` (ch01 R4a(c)),
`adaptor-by-ref-on-inout-accepted`, `adaptor-by-ref-on-field-accepted`,
`adaptor-stored-then-chained-accepted`,
`adaptor-annotated-binding-accepted`
(`mem.Taken[mem.Mapped[mem.SliceIter[i32], i32]]`),
`adaptor-chain-across-question-accepted`,
`adaptor-chain-as-for-iterable-accepted`,
`adaptor-by-ref-for-then-reuse-accepted`,
`callable-field-method-form-rejected` T0043 (`self.f(x)`),
`callable-field-paren-call-accepted` (`(self.f)(x)`),
`callable-bound-cannot-bind-result-rejected` T0039 (the `F: fn(...) -> U`
shape the std surface must not use), `try-fold-method-accepted`,
`consumer-count-drops-items-accepted` (a non-`Copyable`, non-linear
`Item`).
R50 `linear-match-underscore-rejected`, `linear-match-omitted-field-rejected`,
`linear-match-literal-component-rejected`, `linear-option-matched-accepted`.
R57 `rigid-drop-without-droppable-rejected` T0057,
`rigid-drop-with-droppable-accepted`, `rigid-drop-with-copyable-accepted`,
`rigid-iterator-drop-accepted`,
`rigid-discard-without-droppable-rejected` T0057,
`rigid-expression-statement-without-droppable-rejected` T0057,
`neutral-projection-drop-without-bound-rejected` T0057.
