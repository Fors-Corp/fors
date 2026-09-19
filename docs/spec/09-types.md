# Chapter 9: Types, traits, generics and the typing judgements

## Status

Draft, M1, 2026-09-19. Type checking is a phase of its own: it runs after name
resolution (ch08) on one declaration at a time and consumes only that
declaration's CST, the resolver's bindings, and the *signatures* of the
declarations it mentions. Implements PLAN "Surface": generics in `[...]`,
exactly two judgements, no solver, no overloading, no implicit conversions, a
closed operator-trait set. Diagnostic codes `T00nn` equal the rule numbers;
tests cite `09.Rk`.

Note (round-3 owner decisions, 2026-09-19, not yet applied to ch07/ch08 text):
a binding inside a pattern is written `let n`, and a bare name in a pattern is
always a reference; `use a.b as c;` exists; a local may shadow a prelude name
and nothing else. Examples below use these forms. Everything else is derived
from ch07's frozen productions.

## Scope

Owns exclusively: the type universe and primitive sizes; type equality; the
closed coercion list; well-formedness; generic-parameter kinds; trait and
`impl` rules including overlap; the closed operator-trait table; `Copyable`;
`synth` and `check` for every expression, statement and pattern form;
generic-argument determination; member lookup (the deferred segments of ch08
Rules 16, 22); exhaustiveness; what a generic body may do with a parameter; the
signature as the only inter-declaration interface. Not owned: see the table
"Not owned by this chapter".

## Definitions

- **synth(e) = T**: `e` is typed with no expected type and yields `T`.
- **check(e, T)**: `e` is typed against a complete expected type `T`. Which
  syntactic positions are CHECK positions is ch03 Rule 25.
- **Complete type**: a type with no undetermined generic parameter of the call
  being typed. A generic parameter of the *enclosing* declaration is a rigid,
  opaque type and is complete.
- **Head**: the outermost constructor of a type after stripping qualifiers: a
  nominal item, a primitive, `tuple/n`, `fn`, `dyn Tr`, or a rigid parameter.
- **One-way match** `match(P, A)`: `P` may mention unbound parameters of one
  call, `A` is complete. Walk both in lockstep; an unbound parameter in `P` is
  bound to the facing subterm of `A`; a bound parameter, or any constructor,
  MUST equal the facing subterm (Rule 9). Nothing in `A` is ever bound. Cost is
  linear in the size of `P`.
- **Signature**: exactly the parts listed by ch08 Rule 12, plus parameter
  conventions and names, the `scoped(p)` prefix and contract clauses; for an
  `impl`, its header and the signature of each method.

## Rules

### A. Discipline

1. **T0001** — The checker MUST type a function body in one left-to-right pass
   in which each CST node is visited once, in one mode. No rule MAY require
   backtracking, a worklist, a constraint store, a two-way unification
   variable, or any variable that outlives the one call, struct literal or
   operator expression that created it. Cost: each node does O(1) table lookups
   plus type comparisons and one-way matches linear in the size of the types
   involved; impl lookups are memoised (Rule 12). The following are therefore
   not features, and a program that needs one MUST be rejected with this code
   where no more specific code applies: inferring a binding's type from a later
   use (`let x;` with neither annotation nor initialiser; an un-annotated
   closure parameter with no expected `fn` type); numeric-literal defaulting
   that looks beyond the literal's own operator or call; return-type or
   `raises`-type inference for `fn` items; inference of a generic argument from
   a later statement; ranking of candidates of any kind.
2. **T0002** — Signatures are the only interface between declarations. Typing a
   body MUST consult only the signatures of the items, impls and traits it
   mentions, never another body; nothing in a signature is inferred. A change
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
   `continue`, of a call to a function declared `-> never` (a spelling that
   awaits Open question 1), and of a block that ends in one of these (Rule 33).
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
   `S` before any comparison, overlap test or fingerprint; inside a `trait` it
   is a rigid parameter. If aliases are ever added they MUST be transparent in
   the same way.
9. **T0009** — Type equality. Two types are equal iff they have the same
   qualifier set and the same head and their arguments are pairwise equal: type
   arguments by this rule; brand arguments by identity (the same fresh brand or
   the same brand parameter, ch01 Rules 15, 15d); const arguments by value when
   closed, by identity when a bare const parameter (Rule 13). Equality is
   syntactic on resolved, `Self`-expanded types: there is no normalisation, no
   subtyping, no variance.
10. **T0010** — There is no subtyping. `check(e, T)` with `synth(e) = S`, `S !=
    T`, succeeds only through this closed list, applied once, at the outermost
    type only, never searched or chained: (a) `never` to any `T`; (b) a closure
    type or `fn` item to an equal `fn` type; (c) a type `S` to `dyn Tr` when
    `S` implements `Tr` (Rule 12). (b) and (c) MUST be rejected for a
    brand-mentioning or scoped value (ch01 Rules 15(b), 19a). Any conversion
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
    the parameter it fills.
12. **T0012** — Bounds MUST hold at every use: for each argument `X` given to a
    parameter `P: Tr1 + ... + Trk`, `X` MUST implement every `Tri`. "`X`
    implements `Tr[As]`" is decided structurally: if `X` is a rigid parameter,
    by its declared bounds only; otherwise find the impls of `Tr` whose
    self-type head equals `X`'s head, one-way match each impl's `(trait
    arguments, self type)` against `(As, X)` — at most one matches, by Rule 19
    — and then require the matched impl's own bounds on the subterms it bound.
    Every recursive goal is about a strict subterm of `X` (Rule 18 forbids a
    bare-parameter self type and bounds attach only to parameters), so the
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
    reported on one field of the cycle. The test is on declarations (one SCC
    pass), never per instantiation, and is conservative: a generic argument
    counts as stored by value. What `Own`/`Ref` mean is ch01's.
15. **T0015** — A `gparam` is classified from its bound alone: `brand` (ch01
    Rule 15d); no bound — an unbounded type parameter; otherwise every
    `+`-joined bound is resolved, and they MUST be either all traits (a bounded
    type parameter), or exactly one non-trait type (Rule 13), or exactly one
    `fn_type` (a callable parameter, Rule 41). `+` is the only way to state
    several bounds; there is no `where` clause, so a bound's subject is always
    a parameter.

```fors
struct List { head: Option[List] }                 // rejected T0014
struct Tree[A: brand] { root: Option[Ref[Tree[A], A]] }   // accepted: Ref
fn first[T: Copyable, N: usize](let a: Array[T, N]) -> T { return a[0]; }
fn grow[T, N: usize](let a: Array[T, N]) -> Array[T, N + 1] { return a; } // rejected T0013
```

### D. Traits and impls

16. **T0016** — A `trait` declares methods only (ch07 `trait_item`). A method
    with `;` is required; one with a block is provided, and its body is checked
    once, with `Self` rigid and only the trait's own methods and the bounds of
    its generic parameters available. There are no associated types, no
    associated consts and no supertraits: a dependent type is a trait parameter
    (`Iterator[T]`), a constant is a parameterless method (`fn zero() ->
    Self;`), and a function needing two traits writes `T: Eq + Ord`. A method
    whose first parameter is named `self` MUST give it the type `Self` (in an
    impl: the self type), optionally qualified; it is a *receiver method*.
    Other functions of a trait or impl are *associated functions*.
17. **T0017** — `impl Tr[As] for S` MUST define every required method of `Tr`,
    MAY redefine provided ones, and MUST NOT define anything else. Each
    definition's signature MUST equal the trait's after substituting `Self :=
    S` and the trait parameters by `As`: same generic parameters and bounds,
    conventions, parameter names and types, result type (`scoped` included) and
    `raises` type. Contract clauses on an impl method are ch02's.
18. **T0018** — In an `impl_decl` with `for`, the first type MUST be a trait
    and the second MUST NOT be one; without `for` the type MUST be a struct or
    enum. Every generic parameter of the impl MUST occur in its self type or
    trait arguments (otherwise no match could determine it). The self type MUST
    NOT be a bare type parameter: blanket impls do not exist. Where an impl may
    be written is ch08 Rule 21.
19. **T0019** — Overlap. Two impls of the same trait MUST NOT unify: rename
    their generic parameters apart, treat them as variables, and unify the
    pairs `(trait arguments, self type)` first-order, ignoring all bounds;
    success is an error at the later impl naming the earlier. Ignoring bounds
    means there is no specialisation and no negative reasoning. The test is
    decidable and cheap: types are finite first-order terms (no aliases, no
    associated-type projections, const arguments are constants or variables),
    so unification with occurs check is near-linear, and only impls with the
    same trait and the same self-type head are compared. Two inherent impls of
    one type MAY coexist; their method names MUST be distinct (Rule 48).
20. **T0020** — The language-known traits `Index[I, T]`, `IndexMut[I, T]` and
    `Iterator[T]` are *self-determined*: a self-type head MUST have at most one
    impl of each, whatever the trait arguments, so the operator or loop that
    uses them reads `I`/`T` off the single impl instead of searching. This
    replaces associated types for the forms that need them.
21. **T0021** — The operator-trait set is closed; no other operator is
    overloadable and no other trait is consulted by an operator.

    | Operator | Trait | Method (receiver `let self`) |
    |---|---|---|
    | `+` `-` `*` `/` `%` | `Add` `Sub` `Mul` `Div` `Rem` | `add sub mul div rem (let rhs: Self) -> Self` |
    | unary `-` | `Neg` | `neg() -> Self` |
    | `&` `\|` `^` `<<` `>>` | `BitAnd` `BitOr` `BitXor` `Shl` `Shr` | `bitand bitor bitxor shl shr (let rhs: Self) -> Self` |
    | `==` `!=` | `Eq` | `eq(let rhs: Self) -> bool`; `a != b` is `not a.eq(b)` |
    | `<` `<=` `>` `>=` | `Ord` | `lt`, `le` `(let rhs: Self) -> bool`; `a > b` is `b.lt(a)`, `a >= b` is `b.le(a)` |
    | `a[i]` read | `Index[I, T]` | `at(let i: I) -> scoped(self) T` |
    | `a[i]` written or passed `&` | `IndexMut[I, T]` | `at_mut(inout self, let i: I) -> scoped(self) T` |
    | `for x in e` | `Iterator[T]` | `next(inout self) -> Option[T]` |
    | `a op= b` | the trait of `op` | `a = a op b` with the place `a` evaluated once |

    Every binary operator trait is homogeneous (`Self x Self`), so resolution
    is one lookup keyed on the left operand's type (Rule 29); operands are
    evaluated left to right whatever the desugaring. Whether a `scoped` result
    is a place is ch01 Rules 19-19a.
22. **T0022** — Not overloadable, and typed only by this chapter's fixed rules:
    `and`, `or`, `not` (operands `bool`); `=`; `?` and the `else` handler
    (ch02); `move`, `&`, `&out` (ch01 Rule 2); `as` (numeric primitives only,
    ch03 Rule 6); `..<` and `..=`; range-indexing `a[lo ..< hi]` (built-in on
    `Array` and `Slice` only, ch03 Rule 24, selected syntactically by a range
    expression directly inside the brackets); `.name`; call `( )`. Built-in
    impls: every integer type has all of Rule 21's arithmetic, bitwise, `Eq`
    and `Ord` traits (`Neg` signed only); floats have `Add Sub Mul Div Rem Neg
    Eq Ord`; `bool` has `Eq`; `mask[N]` has `BitAnd BitOr BitXor Eq`; `Array`,
    `Slice`, `vector` index by `usize`, `Arena[T, A]` by `Ref[T, A]` (ch01 Rule
    16). Their semantics (traps, IEEE, lanes) are ch03's;
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
    Rule 24a name.
24. **T0024** — A marker trait (`Shared`, `Copyable`) has no methods and
    contributes no operation to a generic body; as a bound it only restricts
    instantiation (ch01 Rule 21b). `Shared`'s field check is ch01 Rules 21-21d.
    A marker trait MUST NOT be used as `dyn`.
25. **T0025** — `dyn Tr` is well-formed iff `Tr` is dyn-capable: it has no
    generic methods, every method is a receiver method with convention `let` or
    `inout`, and `Self` occurs in no signature other than as the receiver's
    type. Method calls on `dyn Tr` are typed from the trait's signatures.
    Representation is ch03 Rule 16's witness table.

```fors
trait Shape {
    fn area(let self: Self) -> f64;                                  // required
    fn twice(let self: Self) -> f64 { return self.area() * 2.0; }    // provided
}
struct Circle { r: f64 }
struct Pair[T] { a: T, b: T }
impl Shape for Circle { fn area(let self: Circle) -> f64 { return self.r * self.r; } }
impl[T] Shape for Pair[T] { fn area(let self: Pair[T]) -> f64 { return 0.0; } }
impl Shape for Pair[i32] {                                           // rejected T0019
    fn area(let self: Pair[i32]) -> f64 { return 1.0; }
}
impl[T] Shape for T { fn area(let self: T) -> f64 { return 0.0; } }  // rejected T0018
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
    = synth(a)`; `S` MUST implement the trait (Rule 12, or a bound when `S` is
    rigid), else T0029 naming operator, trait and `S`; then `b` is a call
    argument whose parameter type `S` is complete, so it is checked against `S`
    (ch03 Rule 25). One syntactic exception keeps `0 ..< n` and `1 + x` usable:
    when `a` is an unsuffixed numeric literal (optionally negated) and `b` is
    not, `b` is synthesised first and `a` checked against it. When both are
    literals Rule 27's default applies. There is no other operand promotion.
    `a[i]`: `synth(a)`, then the single impl of Rule 20 gives `I`, and `i` is
    checked against it.
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
    (element `T`), or a type with an `Iterator[T]` impl (Rule 20); the body is
    checked against `()`, as are the bodies of `while`, `parallel`, `with` and
    attribute blocks. A function body is checked against the declared result
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
    (`let x = return;` is rejected; with an annotation the initialiser coerces
    by Rule 10(a)). `never` MUST NOT be bound to a generic parameter by Rule
    38's matching: an argument that synthesises `never` binds nothing (it
    coerces to whatever the parameter becomes), and a parameter left
    undetermined is T0039. `break`/`continue` outside a loop MUST be rejected.
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
    parameters, in order. (b) A method receiver is synthesised and matched
    one-way against the receiver parameter type. (c) In a CHECK position the
    declared result type is matched one-way against the expected type; a
    structural mismatch here binds nothing and is not yet an error. (d)
    Arguments are then visited left to right: if the parameter type, after
    substituting everything bound so far, is complete, the argument is checked
    against it; otherwise the argument is synthesised and the parameter type is
    matched one-way against the result. (e) The result type, fully substituted,
    is the call's type (subsumption applies in CHECK mode). A binding is never
    revised; a later disagreement is T0026 at that argument. No variable
    survives the call: each nested call runs the procedure to completion before
    the outer one continues.
    *Bound propagation.* Immediately after a type parameter `P` becomes bound
    in step (a), (b), (c) or (d), each declared bound `P: Tr[As]` whose trait
    is self-determined (Rule 20) and whose `As` mentions a parameter that is
    still undetermined is resolved: if `P` was bound to a rigid parameter, take
    that parameter's declared `Tr[Bs]` bound; otherwise take the single impl of
    `Tr` for the head of `P`'s binding (unique by Rule 20) one-way matched
    against that binding, giving `Tr[Bs]`; then match `As` one-way against
    `Bs`, binding the undetermined parameters, which propagate in turn. No such
    bound or impl is T0012 at the call. This is a lookup and not a search: the
    impl is unique, each (parameter, bound) pair is resolved at most once, and
    the work is linear in the number of bounds. A bound on a trait that is not
    self-determined never binds anything. Propagation happens *before* the next
    argument is visited, so a closure argument whose parameter type was just
    completed is checked (Rule 41), not synthesised.
39. **T0039** — If a parameter is still undetermined after Rule 38(d) the call
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
    *parameter* type of the signature is complete, the closure is checked by
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

fn map_sum[T, U: Add, I: Iterator[T], F: fn(sink T) -> U](sink it: I, let f: F, let zero: U) -> U { ... }
fn demo2(sink xs: Counter) {           // given: impl Iterator[i64] for Counter
    let s = map_sum(move xs, |sink x| x * 2, 0);
    // I := Counter from `move xs`; bound propagation reads the single impl
    // Iterator[i64] for Counter: T := i64; the closure is then CHECKed against
    // fn(sink i64) -> U and its body synthesises U := i64; `0` is checked as i64.
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
    traits are exactly its bounds; if `S` is `dyn Tr`, exactly `Tr`; otherwise
    they are the prelude traits and the traits with an impl for `S`'s head
    located in the module defining that head, in the current module, or in a
    module the current module has a direct edge to (ch08 Rule 7).  This uses
    the module graph, not a scope (ch08 Rule 22), so a module the caller does
    not import cannot alter the outcome. No candidate: T0043.
44. **T0044** — More than one candidate in the tier that answered MUST be an
    error listing them; the call is rewritten in a qualified form (Rule 45).
    Candidates are never ranked by specificity, import order or argument types.
    Inherent-before-trait is the only precedence, so that adding a trait impl
    never changes an existing inherent call.
45. **T0045** — Qualified forms (deferred segments, ch08 Rule 16). `Type.name`
    / `Type[args].name`: an inherent associated function or method of that
    head, else one from a candidate trait (Rules 43-44). `P.name` with `P` a
    rigid parameter: from `P`'s bounds. `Tr.name` / `Tr[args].name`: that
    trait's function, with `Self` determined like any parameter by Rule 38. In
    every qualified form a receiver is an ordinary first argument and carries
    its ch01 Rule 2 marker.
46. **T0046** — Receivers. In method-call form the receiver carries no marker:
    `let self` reads it; `inout self` requires a mutable place; `sink self`
    requires an rvalue or an explicit `(move x).m()`. There is no
    auto-dereference, auto-reference or receiver adjustment of any kind: the
    receiver's type MUST match the method's self type up to the qualifier
    access ch01 permits.
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
    named like a variant of the enum.
49. **T0049** — The checker enforces ch08 Rule 11 for every member it resolves,
    with ch08's diagnostic, and performs no scope lookup (ch08 Rule 22).

```fors
struct Counter { n: i64 }               // Shape, Circle: section D's example
impl Counter { fn bump(inout self: Counter) { self.n = self.n + 1; } }
fn total(let c: Circle, inout k: Counter) -> f64 {
    k.bump();                          // inout receiver, no marker: Rule 46
    return c.area() + Shape.twice(c);  // method form; qualified form: Rule 45
}
```

### H. Patterns

50. **T0050** — A pattern is checked against the scrutinee's type `S` (`synth`
    of the `match` head). `_`: any `S`. `let n`: any `S`, binds `n: S`. Integer
    literal (optionally `-`): `S` an integer type, value in range. String: `S =
    Str`. `true`/`false`: `S = bool`. Float literals MUST be rejected. Tuple:
    `S` a tuple of the same arity, componentwise. A `path` with no payload MUST
    resolve to a unit variant of enum `S` or to a `const` of type `S` whose
    type is an integer type, `bool` or `Str`. A `path` or `dot_lit` with a
    payload MUST name a variant of `S` (a `dot_lit` always means `S`'s variant)
    or, for a `{ }` payload, the struct `S` itself; a `( )` payload needs one
    sub-pattern per component, a `{ }` payload names visible fields at most
    once each, and omitted fields match anything.
51. **T0051** — A `let n` binding has the type of the component it faces, with
    the enum's or struct's arguments substituted. Whether it moves, copies or
    projects that component is ch01's; the type is the same in each case. The
    meaning of the `fpat` shorthand under the round-3 forms is ch08's.
52. **T0052** — Refutable patterns occur only in `match` arms. ch07's `binding`
    (in `let`, `var`, `for`) admits only names, `_` and tuples, all
    irrefutable, so no irrefutability check exists.
53. **T0053** — A `match` MUST be exhaustive. The checker runs the standard
    usefulness algorithm on the arm matrix: the match is exhaustive iff the
    all-wildcard row is not useful after the last arm. Constructors: an enum's
    variants (closed, Rule 6, so a non-local enum needs no wildcard arm and
    gaining a variant breaks its matches); `true`/`false`; the single
    constructor of a tuple or struct; integer and string literals, whose
    domains count as infinite, so such a column is exhaustive only through `_`
    or `let n`. The diagnostic names one uncovered value.
54. **T0054** — An arm that is not useful with respect to the arms before it
    MUST be rejected as unreachable.
55. **T0055** — Why this is cheap, and the guard. The grammar has no
    or-patterns, guards or range patterns, so specialising the matrix by a
    constructor never duplicates or splits a row and a column is only ever
    partitioned by the constructors that occur in it plus one default. The
    problem stays co-NP-hard in theory (wildcards over tuples of enums), so the
    computation is charged one step per row visited and MUST stop with T0055,
    asking for the match to be nested, after `MATCH_STEP_FACTOR` (256) times
    the match's pattern-node count: acceptance never depends on machine speed.
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
    aggregate, dropping it, `size_of` / `align_of`, and the methods and
    operators of `T`'s declared bounds (an operator needs its Rule 21 trait
    among the bounds; copying needs `Copyable`). Fields, literals, `as`,
    patterns other than `_` and `let n`, and methods not provided by a bound
    MUST be rejected.
58. **T0058** — A brand parameter has no operations at all and occurs only as a
    brand argument (ch01 Rule 15d). A const parameter is a constant of its type
    in the body. `Shared` and `Copyable` bounds add no methods (Rule 24).
59. **T0059** — No error may depend on an instantiation. Every diagnostic is
    raised either at the definition, against the declared bounds, or at a use
    site, from the callee's signature (arity, kinds, bounds, inference,
    const-argument fit); an instantiated body is never re-checked, no rule
    inspects which type a parameter received, and there is no specialisation.
    Hence both lowerings of ch03 Rule 16 are valid for every accepted program:
    each operation of Rule 57 is a witness-table entry (`size`, `align`,
    `copy`, `move`, `deinit`, a bound's method slot) or, monomorphised, its
    direct counterpart.
60. **T0060** — The `raises` type of a signature is a type like any other (ch02
    Rule 1): it MAY be a type parameter (`fn try_apply[T, U, E, F: fn(let T) ->
    U raises E](let x: T, let f: F) -> U raises E`), determined by Rule 38.
    Nothing abstracts over *whether* a function raises: a non-raising function
    type never equals a raising one, and `never` is not inferred for `E` (Rule
    33). A combinator that must accept both is written twice.

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

## Drafting decisions

- **Expected type before arguments** (Rule 38(c)). Alternative: bind from
  arguments first and use the expected type last. Rejected because `let b:
  Option[u8] = some(1);`, `Buffer.fixed(4096)` and `none` in a field
  initialiser (all attested in ch01/ch04) would mistype or fail; both orders
  are solver-free.
- **Bound propagation through self-determined traits** (Rule 38). Without it,
  `I: Iterator[T]` leaves `T` undetermined by any argument, so every iterator
  adaptor would need explicit type arguments and its closure would be
  unsynthesisable (T0035). Alternative: associated types (`I.Item`). Rejected
  for v0.1 because projections make impl overlap and type equality
  non-structural; uniqueness (Rule 20) gives the same functional dependency as
  a table lookup. Propagation is restricted to self-determined traits because
  only there is the impl unique, so it can never become a search.
- **Bound-by-earlier-argument means CHECK.** ch03 Rule 25 lists a generic call
  argument as SYNTH "while the parameter type still mentions a generic
  parameter"; Rule 38(d) reads "still" as "still undetermined", which is ch03's
  own definition of a complete expected type. ch03's wording should say so.
- **Operator right operands are call arguments**, hence CHECK under ch03 Rule
  25, plus one syntactic literal-on-the-left exception (Rule 29). Alternative:
  literal-typed values that adopt a type later; rejected by Rule 1. Positions
  checked here that ch03 Rule 25's list omits and should cite: index operand,
  `raise` operand, handler block, `grain` expression, function-body tail.
- **Homogeneous operator traits.** Alternative `Mul[R]` (design doc). Rejected:
  a parameterised `Mul` needs either overload resolution on the right operand
  or an associated output type. Scalar-times-vector is a method or `.splat`.
- **No associated types, consts or supertraits.** ch07's `trait_item` is a
  method only and `trait_decl` has no bound list; trait parameters plus Rule
  20's self-determined traits cover iterators and indexing, and keep overlap
  first-order (no projections to normalise).
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
- Self-review 2026-09-19, holes closed: overlap via `Self` (Rule 8); overlap
  undecidable through projections (none exist); unbounded operations and copies
  in generic bodies (Rule 57); brand escaping a `with` block by inference (Rule
  40); `Shared` bound met by an `@unsafe` impl (Rule 12); foreign enum growth
  (Rules 6, 53); `never` in bindings and inferred arguments (Rule 33);
  impl-lookup non-termination (Rules 12, 18); `1 + x` under left-keyed
  operators (Rule 29); closure result flowing outward (Rule 41: the closure is
  identified syntactically before it is typed).

## Open owner questions

1. **Prelude additions** (ch08 Rule 17). This chapter needs, unqualified:
   `Copyable never Eq Ord Add Sub Mul Div Rem Neg BitAnd BitOr BitXor Shl Shr
   Index IndexMut Iterator Range RangeIncl` (ch03 already writes `T: Ord` with
   no `use`). Recommended: add them all; this also closes README Q3's
   `Copyable`. Blocks std and the checker's lang-item table.
2. **Integer literal default**: `i32` (drafted, matches ch03) or `i64`? With
   `i32`, ch03's example `for i in 1 ..< 8 { ... v[i] ... }` is ill-typed
   because built-in indexing takes `usize`. Recommended: keep `i32` and
   `usize`-only indexing, and change that example to `1usize ..< 8`.
3. **v0.1 restrictions**, each addable later without breaking accepted code:
   homogeneous operators (no `Mul[R]`, Rule 21); no blanket impls, associated
   types or supertraits (Rules 16, 18); no arithmetic on const parameters (Rule
   13, although ch07 parses `N + 1`); no effect polymorphism, so std writes
   `map`/`try_map` pairs (Rule 60). Recommended: accept all four.
4. **`sink self` on a place is written `(move x).m()`** (Rule 46). Recommended:
   accept; it keeps every move visible (ch01 Rule 2).
5. **ch08 Q5**: a variant and an associated function of the same name are an
   error here (Rule 48). Recommended: confirm.
6. `MATCH_STEP_FACTOR` = 256: confirm or measure.

## Conformance tests

All in `tests/conformance/09-types/`; `-accepted` expects `check-ok`,
`-rejected` expects `check-error` with the code shown. R1
`let-without-type-or-init-rejected` T0001,
`literal-default-ignores-later-use-rejected` T0026; R7
`fn-item-as-value-accepted`, `generic-fn-value-without-args-rejected` T0039; R9
`nominal-structs-distinct-rejected` T0026, `brand-identity-mismatch-rejected`
T0026; R10 `never-coerces-accepted`, `array-to-slice-rejected` T0026,
`concrete-to-dyn-accepted`; R11 `type-arity-rejected` T0011; R12
`bound-unsatisfied-rejected` T0012, `bound-via-generic-impl-accepted`; R13
`const-param-float-rejected` T0013, `const-arg-arithmetic-on-param-rejected`
T0013; R14 `recursive-struct-rejected` T0014, `recursive-via-ref-accepted`; R15
`mixed-trait-and-type-bound-rejected` T0015; R16 `provided-method-accepted`,
`provided-method-uses-foreign-op-rejected` T0057,
`self-receiver-wrong-type-rejected` T0016; R17 `impl-missing-method-rejected`
T0017; R18 `blanket-impl-rejected` T0018, `unconstrained-impl-param-rejected`
T0018; R19 `overlap-generic-vs-concrete-rejected` T0019,
`overlap-via-self-rejected` T0019; R20 `two-iterator-impls-rejected` T0020; R21
`operator-via-impl-accepted`, `compound-assign-via-add-accepted`; R22
`and-on-non-bool-rejected` T0030; R23 `copyable-fieldwise-accepted`,
`copyable-with-own-field-rejected` T0023; R24 `dyn-marker-rejected` T0024; R25
`dyn-generic-method-rejected` T0025; R27 `literal-checks-to-u8-accepted`,
`int-literal-to-float-rejected` T0027, `literal-against-param-rejected` T0027;
R28 `none-in-synth-rejected` T0039; R29 `operator-missing-impl-rejected` T0029,
`literal-left-operand-accepted`, `mixed-width-operands-rejected` T0026; R30
`if-condition-non-bool-rejected` T0030; R31 `return-value-mismatch-rejected`
T0026, `for-over-non-iterable-rejected` T0031; R32
`if-branches-first-fixes-accepted`, `if-branch-mismatch-rejected` T0026,
`if-first-branch-never-accepted`; R33 `let-never-rejected` T0033,
`never-not-inferred-rejected` T0039; R34
`struct-literal-missing-field-rejected` T0034,
`struct-literal-args-from-expected-accepted`, `dot-lit-in-synth-rejected`
T0034; R35 `closure-synth-unannotated-rejected` T0035,
`closure-checked-against-fn-type-accepted`; R36 `handler-block-type-rejected`
T0026; R37 `named-arg-wrong-label-rejected` T0037; R38
`infer-from-first-argument-accepted`, `infer-from-expected-type-accepted`,
`binding-never-revised-rejected` T0026; `generic-arg-from-iterator-bound-accepted`,
`closure-param-from-iterator-bound-accepted`,
`rigid-param-iterator-bound-propagates-accepted`,
`non-self-determined-bound-does-not-bind-rejected` T0039,
`iterator-bound-no-impl-rejected` T0012; R39 `cannot-infer-rejected` T0039; R40
`brand-inferred-for-callee-accepted`, `two-brands-one-param-rejected` T0026;
R41 `callable-bound-closure-accepted`,
`closure-before-its-type-source-rejected` T0035; R42
`field-on-type-param-rejected` T0042; R43 `inherent-before-trait-accepted`,
`trait-method-without-edge-rejected` T0043, `method-on-bound-accepted`; R44
`two-traits-same-method-rejected` T0044; R45 `qualified-trait-call-accepted`;
R46 `sink-receiver-needs-move-rejected` T0046, `no-auto-deref-own-rejected`
T0043; R47 `bracket-instantiates-method-accepted`; R48
`method-named-as-field-rejected` T0048,
`duplicate-method-across-impls-rejected` T0048; R50
`pattern-float-literal-rejected` T0050; R51 `let-binding-in-pattern-accepted`;
R53 `match-non-exhaustive-enum-rejected` T0053,
`match-int-needs-wildcard-rejected` T0053,
`match-foreign-enum-no-wildcard-accepted`; R54 `unreachable-arm-rejected`
T0054; R55 `match-budget-exceeded-rejected` T0055; R57
`unbounded-op-on-param-rejected` T0057, `copy-without-copyable-rejected` T0057;
R58 `brand-param-as-value-type-rejected` (ch01 code); R59
`generic-checked-at-definition-rejected` T0057 (an uninstantiated generic with
an ill-typed body); R60 `generic-raises-type-accepted`,
`raising-closure-to-plain-fn-type-rejected` T0026. Rules 2, 49 and 52 have no
corpus test: 2 is an incremental-build property (tested in the query engine),
49 re-uses ch08's tests, 52 is a fact about the grammar.
