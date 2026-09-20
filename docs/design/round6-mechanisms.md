# Round 6 — mechanisms (linear types, `defer`/`errdefer`, iterator method chaining, `main`'s error)

Status: design contract, 2026-09-20. Implements the three owner decisions of
2026-09-20 recorded in `docs/PLAN.md` §4.3 (round 6) plus the `main`-error
decision. Authority: PLAN > the spec chapters > this file. This file settles
MECHANISMS only; it writes no spec rule and no code. The three stages that
follow (spec text, corpus, std) implement what is written here without
re-deriving it. Where a rule below is marked **normative**, it is ready to
paste into the chapter named in the heading, with that chapter assigning the
rule number and code. Every claim about an existing rule quotes it.

Callers: `docs/spec/README.md` (index; add a pointer under "Fact -> owning
chapter" once the spec stage lands), the spec stage (ch01, ch02, ch04, ch07,
ch09, ch10 edits listed in §6), the corpus stage (`tests/conformance`, the
test names of §1.9, §2.10, §3.9, §4.5) and the std stage (`std/mem/seq.fors`,
`std/mem/vec.fors`, `std/mem/hashmap.fors`, `std/mem/alloc.fors`).

The order of sections is the order of dependence: O3 first, because its
answer decides whether std's whole iteration surface is rewritten (it is),
then O1, on which O2 leans, then O2, then O4.

---

## 1. O3 — iterator method chaining

### 1.1 The claim under test

ch10 Rule 34 and its drafting decision 16 conclude: "`Iterator` is
language-known (ch09 Rule 21) and std cannot add a method to it (ch09 Rule 43
finds inherent and trait methods only, there is no blanket impl, Rule 18, and
no free-function method syntax), so `it.map(f)` is not writable."

The candidate mechanism is: PROVIDED methods on the `Iterator` trait itself,
each returning a CONCRETE adaptor struct that carries its own ordinary
`impl Iterator`. The question is whether ch09's rules, read literally, type
`it.map(f).take(3)` with that declaration, for a rigid receiver, a concrete
receiver, and a receiver that is itself an adaptor.

### 1.2 The declarations

The trait is declared once, in `std.mem.seq`. The prelude name `Iterator`
(ch08 Rule 17) and `mem.seq.Iterator` denote one item (ch10 Definitions,
"Defining module"; ch08 Rule 13's same-entity case). ch09 Rule 21 keeps
ownership of the REQUIRED part (`type Item`, `next`); the PROVIDED part is
ch10's surface. Nothing here is a blanket impl: every `impl` below has a
struct head (ch09 Rule 18: "The self type MUST NOT be a bare type parameter:
blanket impls do not exist").

```fors
// std.mem.seq — the prelude's Iterator IS this declaration
pub trait Iterator {
    type Item: Droppable;                                  // §2.3 L5
    fn next(inout self) -> Option[Self.Item];              // required (ch09 R21)

    // ---- adaptors: provided, lazy, allocation-free; each takes the source by value
    fn map[U](sink self, let f: fn (sink Self.Item) -> U) -> Mapped[Self, U] {
        return Mapped { src: self, f: f };
    }
    fn filter(sink self, let p: fn (let Self.Item) -> bool) -> Filtered[Self] {
        return Filtered { src: self, p: p };
    }
    fn take(sink self, let n: usize) -> Taken[Self] { return Taken { src: self, left: n }; }
    fn skip(sink self, let n: usize) -> Skipped[Self] { return Skipped { src: self, to_skip: n }; }
    fn enumerate(sink self) -> Enumerated[Self] { return Enumerated { src: self, at: 0 }; }
    fn zip[J: Iterator](sink self, sink other: J) -> Zipped[Self, J] {
        return Zipped { a: self, b: other };
    }
    // the one borrowing adaptor: lets an `inout` iterator, or a field, be chained
    @unsafe(invariant: "src points at the receiver for the extent of the scoped result")
    fn by_ref(inout self) -> scoped(self) ByRef[Self] { return by_ref(&self); }   // STUB

    // ---- consumers: provided, take the source by value, return plain values
    fn count(sink self) -> usize { var n: usize = 0; for x in self { n = n + 1; } return n; }
    fn fold[B](sink self, sink init: B, let f: fn (sink B, sink Self.Item) -> B) -> B {
        var acc: B = move init;
        for x in self { acc = f(move acc, move x); }
        return acc;
    }
    fn for_each(sink self, let f: fn (sink Self.Item)) { for x in self { f(move x); } }
    fn all(sink self, let p: fn (let Self.Item) -> bool) -> bool {
        for x in self { if not p(x) { return false; } }
        return true;
    }
    fn any(sink self, let p: fn (let Self.Item) -> bool) -> bool {
        for x in self { if p(x) { return true; } }
        return false;
    }
    fn find(sink self, let p: fn (let Self.Item) -> bool) -> Option[Self.Item] {
        for x in self { if p(x) { return some(x); } }
        return none;
    }
    fn try_fold[B, E](sink self, sink init: B,
                      let f: fn (sink B, sink Self.Item) -> B raises E) -> B raises E {
        var acc: B = move init;
        for x in self { acc = f(move acc, move x)?; }
        return acc;
    }
    fn try_for_each[E](sink self, let f: fn (sink Self.Item) raises E) raises E {
        for x in self { f(move x)?; }
    }
}

pub struct Mapped[I: Iterator, U] { src: I, f: fn (sink I.Item) -> U }
pub struct Filtered[I: Iterator]  { src: I, p: fn (let I.Item) -> bool }
pub struct Taken[I: Iterator]     { src: I, left: usize }
pub struct Skipped[I: Iterator]   { src: I, to_skip: usize }
pub struct Enumerated[I: Iterator]{ src: I, at: usize }
pub struct Zipped[I: Iterator, J: Iterator] { a: I, b: J }
pub struct ByRef[I: Iterator]     { src: rawptr[I] }      // the only raw pointer left in seq

impl[I: Iterator, U] Iterator for Mapped[I, U] {
    type Item = U;
    fn next(inout self) -> Option[U] {
        match self.src.next() {
            some(let x) => { return some((self.f)(move x)); }   // a callable FIELD is called as (self.f)(...)
            none => { return none; }
        }
    }
}
impl[I: Iterator] Iterator for Filtered[I] {
    type Item = I.Item;                                    // headed by an impl parameter: ch09 R61(d)
    fn next(inout self) -> Option[I.Item] {
        while true {
            match self.src.next() {
                some(let x) => { if (self.p)(x) { return some(x); } }   // x dropped otherwise: Item: Droppable
                none => { return none; }
            }
        }
        return none;
    }
}
impl[I: Iterator] Iterator for Taken[I]      { type Item = I.Item; fn next(inout self) -> Option[I.Item] { ... } }
impl[I: Iterator] Iterator for Skipped[I]    { type Item = I.Item; ... }
impl[I: Iterator] Iterator for Enumerated[I] { type Item = (usize, I.Item); ... }
impl[I: Iterator, J: Iterator] Iterator for Zipped[I, J] { type Item = (I.Item, J.Item); ... }
impl[I: Iterator] Iterator for ByRef[I]      { type Item = I.Item; ... }   // next = (*src).next(), STUB
```

Three choices inside these declarations, each with its rejected alternative:

- **Callable parameters are `fn` TYPES, not a callable type parameter `F`.**
  With `fn map[U, F: fn (sink Self.Item) -> U](sink self, let f: F)`, a
  fn-item argument binds `F` only; `U` occurs in no parameter type, and ch09
  Rule 38 binds nothing through a bound ("The bounds and constraint entries
  of the callee are then checked", never used to bind), so `it.map(double)`
  is T0039 "cannot infer `U`". Rule 41 rescues only a *closure* argument.
  With a `fn` type the fn item's type is matched one-way against
  `fn (sink i32) -> U` and binds `U` (Rule 7: fn types compare componentwise);
  a closure argument is checked against it by Rule 41 ("or of a `fn` type")
  and coerces by Rule 10(b). Second benefit: the adaptor types stay
  WRITABLE (`Mapped[SliceIter[i32], i32]`; a closure type "cannot be
  written", Rule 7), so annotated bindings and struct fields of adaptor type
  remain possible. This is also what ch10 Rule 34 does today.
- **`Mapped` carries `U` as a struct parameter.** Dropping it
  (`Mapped[I]` with `f: fn (sink I.Item) -> U` inferred somewhere) is
  impossible: the impl `impl[I: Iterator, U] Iterator for Mapped[I]` has `U`
  "unconstrained" (Rule 18: "an occurrence only in a bound, in `type A =
  ...;` or in a method does not count"). Inside the provided body the struct
  literal determines `I` and `U` from its CHECK position (Rule 38(c): the
  declared result `Mapped[I, U]` matched against the expected
  `Mapped[Self, U]`).
- **Adaptor names stay `Mapped`, `Filtered`, ... , never `Map`.** `Map` is
  the hash map, a prelude name (ch10 Rule 2); and a submodule `mem.iter`
  would collide with the function `mem.iter` in `mem`'s one namespace (ch08
  Rule 13). The task's `mem.iter.Map[Self, F]` spelling is therefore not
  available; the types are `mem.Mapped[I, U]` etc., re-exported from
  `std.mem.seq` as today.
- **`map` takes its item `sink`, predicates take it `let`.** `fn (let
  Self.Item) -> U` would forbid `|let x| x` for a non-`Copyable` item (a move
  out of a `let` parameter, ch01 Rule 3). ch09's own `map_sum` example uses
  `fn (sink I.Item) -> U`. Predicates only read.

### 1.3 The derivation, rule by rule

Setting: `fn count_small[A: brand](let v: Vec[i32, A]) -> usize { return
v.iter().map(double).take(3).count(); }` with `fn double(sink x: i32) -> i32`.

**Step 0, `v.iter()`.** Rule 43 tier (1): the inherent impls of `Vec`'s head;
`impl[T: Copyable, A: brand] Vec[T, A] { fn iter(let self) -> scoped(self)
SliceIter[T] }` (ch10 Rule 24); Rule 12 on the impl's bound: `i32: Copyable`
(Rule 23, built in). Type known: `SliceIter[i32]`, scoped to `v` (ch01 Rule
19a: the access to `v` "MUST extend to the end of the lexical scope of the
binding that receives the scoped result" — here no binding: §1.5 fixes the
extent of an unbound scoped rvalue as the statement).

**Step 1, `.map(double)`.** Rule 43: `S = SliceIter[i32]`, concrete. Tier (1):
no inherent method named `map` on `SliceIter` (§1.7 makes that a std rule).
Tier (2): "the prelude traits and the traits with an impl for `S`'s head
located in the module defining that head" — `Iterator` is a prelude trait
(ch08 Rule 17) and `impl[T: Copyable] Iterator for SliceIter[T]` is in
`std.mem.seq`, the module defining `SliceIter`; Rule 12 matches it with `T :=
i32`. Candidate set = {`Iterator.map`}: no Rule 44 ambiguity. `map` is a
*receiver method* (Rule 16: first parameter `self`, shorthand for `self:
Self`) and is provided — Rule 16 says a provided method's "body is checked
once, with `Self` rigid"; nothing in Rules 43-44 distinguishes provided from
required methods for lookup, so it is a candidate like `next`.

Rule 38: "the parameters to determine be those of the impl or trait reached
(with `Self`), then those of the function": `Self`, then `U`. (b) "A method
receiver is synthesised and matched one-way against the receiver parameter
type": `Self := SliceIter[i32]`. (c) SYNTH position: nothing. (d) argument
`double`: the parameter type `fn (sink Self.Item) -> U` "is substituted with
everything bound so far and normalised (Rule 20)": `SliceIter[i32].Item` is a
projection whose head is concrete, so Rule 20(b) reads the impl's `type Item
= T` with `T := i32` → `fn (sink i32) -> U`. Not complete (`U`), so the
argument is synthesised (Rule 28: the fn item's type `fn (sink i32) -> i32`)
and matched one-way: `U := i32`. (e) full substitution `fn (sink i32) -> i32`
equals the argument's type (Rule 9). Bounds: none beyond `Self: Iterator`,
already established by the lookup. (f) result `Mapped[SliceIter[i32], i32]`.
Ownership: Rule 46, "`sink self` takes an rvalue as it is"; the rvalue is
scoped to `v` — §1.5's ch01 addition makes the RESULT scoped to `v` too.

**Step 2, `.take(3)`.** `S = Mapped[SliceIter[i32], i32]`. Tier (1): `Mapped`
has no inherent `take`. Tier (2): `impl[I: Iterator, U] Iterator for Mapped[I,
U]` lives in `std.mem.seq`, the defining module of `Mapped`; Rule 12 matches
`I := SliceIter[i32]`, `U := i32`, then "require the matched impl's own
bounds on the subterms it bound": `SliceIter[i32]: Iterator` — the same
lookup as step 1, memoised. Candidate {`Iterator.take`}. Rule 38: `Self :=
Mapped[SliceIter[i32], i32]`; `n: usize` is complete, so `3` is CHECKed
against `usize` (Rule 27). Result `Taken[Mapped[SliceIter[i32], i32]]`,
scoped to `v` (§1.5).

**Step 3, `.count()`.** Same path; `Self := Taken[...]`; result `usize`, not
scoped (§1.5: the declared result does not mention `Self`). Inside `count`'s
provided body, `for x in self` moves `self` into the loop, "which owns and
drops the iterator" (Rule 31); dropping a rigid `Self` is legal because
`Self: Iterator` implies `Self: Droppable` (§2.3 L5), and `x: Self.Item` is
dropped at each iteration's end because `type Item: Droppable` (Rule 57:
"its declared bounds are exactly the bounds the trait declares for `A`").

**Rigid receiver.** `fn f[I: Iterator](sink it: I) -> usize { return
it.map(|sink x| x).take(3).count(); }`. Rule 43: "If `S` is a rigid parameter
the candidate traits are exactly its bounds" → `Iterator.map`. Rule 38(b):
`Self := I`. (d): `fn (sink Self.Item) -> U` → `fn (sink I.Item) -> U`;
`I.Item` is neutral (Rule 20(a): "If `H` is rigid ... `H.A` is neutral: a
normal, opaque type"), so the parameter types are complete and the argument
is a closure: Rule 41 checks it with `x: I.Item`; "if the signature's result
type is not yet complete the body is synthesised instead and the result type
matched one-way against it": `U := I.Item`. Result `Mapped[I, I.Item]`. Step
2: `S = Mapped[I, I.Item]` has a CONCRETE head with rigid arguments; tier (2)
finds the `Mapped` impl (`I' := I`, `U := I.Item`; the impl's bound `I:
Iterator` holds "by its declared bounds only", Rule 12). Then `.count()`.
Rule 46: `it` is a place, so the first call MOVES it implicitly; the later
calls take rvalues. `it` is a `sink` parameter, so the move is legal (ch01
Rule 4a(d)) and satisfies ch01 Rule 4.

**The provided body itself** (Rule 16: checked once, `Self` rigid, only
`Iterator`'s methods, the declared bounds of its associated types and the
bounds of the method's own parameters available). `map`: `Mapped { src:
self, f: f }` is "typed as a call whose parameters are the fields in written
order" (Rule 34); the CHECK position (`return` against `Mapped[Self, U]`)
binds `I := Self`, `U := U` by Rule 38(c); `self` is moved into `src`
(consumes the `sink` parameter, ch01 Rule 4); `f`'s type `fn (sink
Self.Item) -> U` equals the field type `fn (sink I.Item) -> U` under `I :=
Self` (Rule 9: neutral projections "are equal iff their heads are equal and
they name the same trait ... and the same associated type"). Well-formedness
of `Mapped[Self, U]` needs `Self: Iterator`: Rule 8, "inside a `trait` it is
a rigid parameter whose one bound is the trait itself". `Mapped.next` calls
the callable field as `(self.f)(move x)` — `self.f(x)` is METHOD-CALL form
(Rule 43) and would be T0043; the parenthesised form is `tuple_or_paren`
followed by `call`, and Rule 7 says a value of `fn` type "is called with
`( )`". The existing `std/mem/seq.fors` stubs write `self.f(x)`; the std
stage fixes them.

### 1.4 Attacking the derivation

1. *The closure's parameter type must come from `Self.Item` of a
   not-yet-determined `Self` (Rule 38 order).* Cannot happen on a method
   call: `Self` is bound in step (b), BEFORE any argument is visited in (d).
   The `map_sum` caveat of Rule 38 ("declare the head-binding parameter
   first") concerns free functions whose iterator parameter comes after the
   closure. In the qualified form `Iterator.map(move it, f)` (Rule 45) the
   receiver "is an ordinary first argument", still left of `f`. Holds.
2. *Two adaptors of the same name.* A user trait `Ext { fn take(sink self,
   let n: usize) -> ...; }` implemented for `SliceIter[i32]` in a module the
   caller has a direct edge to puts two candidates in tier (2); Rule 44 makes
   that "an error listing them", never a ranking, and the fix is the
   qualified form `Iterator.take(move it, 3)`. A user INHERENT `take` on the
   user's own type wins by tier (1); std's iterator types have no inherent
   method sharing an adaptor or consumer name (§1.7), so `SliceIter.take`
   cannot shadow `Iterator.take`. Holds, with that std rule.
3. *`it.map(f)` where `it` is `inout`.* Rule 46 makes it `(move it).map(f)`;
   ch01 Rule 4a(d): "a `let` parameter (Rule 3) and an `inout` parameter MUST
   NOT be moved from" → rejected, with Rule 46's mandatory diagnostic naming
   the call and `Iterator.map`'s `sink self`. The writable form is
   `it.by_ref().map(f)`: `by_ref` takes `inout self` (a mutable place, Rule
   46), returns `scoped(it) ByRef[I]`, and the chain continues on that
   rvalue; the result stays scoped to `it` (§1.5). Same answer for a field
   receiver: `self.it.map(f)` is a partial move (ch01 Rule 4a(c)), so
   `self.it.by_ref().map(f)`. Holds; `by_ref` is the one raw-pointer adaptor
   and the only unsafe inventory entry `seq` keeps (ch04 Rule 9).
4. *`sink self` meets the implicit receiver move inside a chain.* Only the
   first call in a chain can have a place as receiver; every later receiver
   is a call result, an rvalue that "`sink self` takes ... as it is". The one
   place moved is `it`, exactly once. A chain inside a loop on an outer `it`
   is ch01 Rule 4a(b) (a move inside a loop) and is rejected as it should be.
   Holds.
5. *An adaptor stored in a local.* `let m = it.map(double); let t =
   m.take(3);` — `m` is a place, moved by `take` (Rule 46); `let m:
   mem.Mapped[mem.SliceIter[i32], i32] = ...` is writable because the type
   mentions no closure type (§1.2). With a closure argument the binding must
   be un-annotated (`let m = it.map(|sink x| x * 2);` synthesises the type,
   Rule 31); it is the same restriction as today. Holds.
6. *The chain crosses `?`.* `let t = it.map(f).take(3); g()?; return
   t.count();` — `t` is live across the error exit; it is not linear
   (`Iterator` implies `Droppable`, §2.3 L5) so §2's scope-exit check drops it
   silently on the error path. If `t` is scoped to `v`, `v` is a `let`
   parameter and the exit ends the extent. Holds.
7. *The chain is a `for` iterable.* `for x in it.map(f).take(3) { }`: Rule 31,
   "`synth(e)` MUST be ... a type `S` that implements `Iterator` (Rule 12)",
   element type the normalised `Taken[Mapped[..]].Item` = `I.Item` = `i32`
   (Rule 20 twice). "The iterable is a value use", so the loop owns and drops
   the rvalue. For `for x in it.by_ref().take(3) { }` the scoped extent is the
   loop statement (§1.5), after which `it` is usable again. Holds.
8. *Bound checking of a callable field.* `Mapped[I, U]` is well-formed for
   any `I: Iterator`, `U`; the impl's `next` calls the `fn`-typed field. No
   closure type ever appears in a signature; Rule 41's callable-parameter
   machinery is not used at all. Holds.
9. *The trait is not dyn-capable (Rule 25).* Unchanged: `dyn Iterator` did
   not exist and still does not; provided generic methods (`map[U]`) add a
   second reason. No loss: nothing in std or the corpus uses it.
10. *Blanket impls.* None is needed anywhere: every impl above has a struct
    head. Rules 18 and 19 are untouched, the overlap test stays first-order.

### 1.5 The one gap, and the smallest addition (ch01, not ch09)

The gap is not in method lookup; it is in ownership, and it is why ch10 Rule
34 chose `inout` + `scoped(it)` free functions: "a scoped source (`v.iter()`,
`mem.iter(s)`, `s.scalars()`) MUST NOT be stored in a field (ch01 Rule 19a)
and a `sink` parameter cannot be a scoped result's designated source (ch01
Rule 19), so an adaptor that took its source by value and kept it in a
struct could never be applied to a borrowed iterator — which is every
container iterator."

Read literally, ch01 today does not reject `v.iter().map(f)` either: Rule
19a lists what a scoped VALUE must not do at the site where it is known to
be scoped, and inside `map`'s body `self` is a rigid `Self`, not known to be
scoped; ch10 Rule 35 even permits passing a scoped source to a `sink`
parameter. What is missing is a rule that says what the CALLER may conclude
about the RESULT. Without it, `let m = v.iter().map(f);` yields an unscoped
`m` holding a view of `v` — the hole that Rule 34 avoided by construction.

**Normative (ch01, new Rule 19c — scope inheritance through a generic
parameter).** At a call whose argument `a` (an ordinary argument or the
receiver) is a scoped value with designated source `q`:
(a) if the parameter's declared type is a bare type parameter `P` — a
parameter of the callee, of its `impl`, or `Self` of a trait method — the
call is legal iff no `inout` or `set` parameter of the callee has a declared
type that mentions `P` and the callee's `raises` type does not mention `P`;
the call's result is then scoped to `q` iff the callee's DECLARED result type
mentions `P` (syntactically, before substitution); if two scoped arguments
with different sources would both make the result scoped, the call MUST be
rejected (a scoped value has one source, Rule 19);
(b) if the parameter's declared type is not a bare type parameter, the
argument MAY be passed `let` or `inout` (Rules 19-19a govern what flows out
through `scoped(p)`) and MUST NOT be passed `sink`;
(c) the extent of a scoped value that is consumed within the expression that
produced it, or that is the iterable of a `for`, is that expression or that
`for` statement (extending Rule 19a's "binding that receives" to the two
binding-less cases).
*Why (a) is sound from signatures alone.* The callee's body is checked once
with `P` rigid (ch09 Rule 57); a rigid value can only be bound, passed by a
convention, moved, stored in an aggregate, dropped, or given to a bound's
method. Stored in an aggregate, it lives in a type that mentions `P`
(aggregates are typed field by field); passed on to another generic callee,
this rule applies again by induction; passed to a bound's method, that
method's signature mentions `P` only as `Self`. The remaining escape is
erasure, closed by (d) below. So a value of type `P` can reach the caller only
inside the result (mention of `P`), inside an `inout`/`set` argument (banned)
or inside the error (banned).
(d) **Normative (ch09 Rule 10(c) amendment).** `check(e, dyn Tr)` MUST be
rejected when `synth(e)` is a rigid type parameter or a neutral projection;
a generic body that wants an object takes `dyn Tr` as a parameter. (Also
needed by §2.3 L8.)

Cost to the near-linear gate: none. (a) reads the callee's declared signature
once per call (a syntactic "mentions `P`" scan, memoised per signature) and
sets one bit on the call's result; no new type, no unification.

Rejected alternatives: (i) keep `inout` + `scoped(it)` and make `inout self`
accept an rvalue receiver by materialising a temporary — breaks Rule 46's
"`inout self` requires a mutable place", and the temporary would be dropped
in the caller, which in a generic caller is a rigid drop (§2.3 L4); (ii)
`scoped(self)` on a `sink self` method — contradicts Rule 19 ("never
`sink`/`set`") and would need the callee to know the receiver was scoped;
(iii) a lifetime-like parameter on `Iterator` — a region system, forbidden
by ch01's rejected alternatives.

### 1.6 Verdict

**WORKS WITH THIS SMALL ADDITION.** The addition is ch01 Rule 19c (+ the
Rule 10(c) amendment), an ownership rule; method lookup, generic-argument
determination, projections and the provided-method body all type-check under
ch09's existing rules with NO change to Rules 16, 18, 19, 38-41, 43-46, 57 or
61. ch10 Rule 34's conclusion is DISPROVED on its stated ground (lookup) and
was right only about the ownership gap, which it worked around rather than
named. Blanket impls are not needed and are not added. The near-linear
type-check gate is untouched.

### 1.7 What the std signatures become

- `std.mem.seq` declares `pub trait Iterator` as in §1.2 (required part
  fixed by ch09 Rule 21; ch09 Rule 21's text says the declaration is std's
  and lists only the required members). The free functions `mem.map`,
  `mem.filter`, `mem.take`, `mem.skip`, `mem.enumerate`, `mem.zip`,
  `mem.count`, `mem.fold`, `mem.for_each`, `mem.all`, `mem.any`, `mem.find`,
  `mem.try_fold`, `mem.try_for_each` are DELETED. `mem.iter` (the `@unsafe`
  slice primitive) stays. `mem.try_collect_into` stays a free function in
  `std.mem.vec` (`seq` is a leaf and cannot name `Vec`; and as an inherent
  `Vec` method it would need `I.Item = T`, an equality bound that does not
  exist).
- Adaptor structs own their source (§1.2). `Zipped` owns both sources; the
  rule "second source owned" moves from the signature to the call site (Rule
  19c(a): two different scoped sources are rejected).
- `by_ref` is the seventh adaptor. `ByRef[I]` is the only struct in `seq`
  with a raw pointer; the unsafe inventory loses six entries and keeps two
  (`iter`, `by_ref`).
- **Normative (ch10, Rule 34 replacement).** No std type that implements
  `Iterator` MAY declare an inherent method whose name is that of a provided
  method of `Iterator` (ch09 Rule 44: inherent-before-trait would silently
  re-route the call).
- Consumers: `v.iter().count()`, `v.iter().fold(0, |sink a, sink x| a + x)`;
  the `try_` pair as provided methods with `E` a method parameter (ch09 Rule
  60). ch10 Rule 8's "same name modulo the prefix, same parameter order"
  holds.
- ch10 Rule 33's "No std iterator is linear or `Copyable`" becomes a
  language fact (§2.3 L5) rather than a std promise.
- Every corpus and spec example of the chain form is rewritten from one
  binding per stage to a chain: `return v.iter().map(double).filter(small).count();`.

### 1.8 What O3 forbids that is legal today

- The free-function adaptor and consumer calls (`mem.map(&it, f)`, `mem.count(move k)`).
  Corpus: `10-std/adaptor-chain-accepted`, `10-std/adaptor-with-raising-closure-rejected`
  and any spec example using them (ch10 Examples `app.chain`).
- Passing a scoped value to a `sink` parameter of CONCRETE type (Rule 19c(b)).
  No corpus site is known; the spec stage greps `sink` parameters whose
  argument is a `scoped` result.
- `check(e, dyn Tr)` on a rigid `e` in a generic body (Rule 10(c) amendment). No corpus site.
- An inherent method on a std iterator type named like a provided method (none exist).
- `impl Iterator` for a linear self type or a linear `Item` (§2.3 L5; none exist).

### 1.9 Conformance tests O3 needs (`tests/conformance/10-std` unless noted)

`adaptor-chain-method-accepted` (three stages, fn items), `adaptor-chain-closure-accepted`
(`U` from a closure body, un-annotated binding), `adaptor-chain-rigid-receiver-accepted`
(`I: Iterator`, `Mapped[I, I.Item]`), `adaptor-on-inout-receiver-rejected` (ch01 R4a(d),
detail names `Iterator.map`'s `sink self`), `adaptor-by-ref-on-inout-accepted`,
`adaptor-on-field-receiver-rejected` (ch01 R4a(c)), `adaptor-by-ref-on-field-accepted`,
`adaptor-stored-then-chained-accepted`, `adaptor-annotated-binding-accepted`
(`mem.Taken[mem.Mapped[mem.SliceIter[i32], i32]]`), `adaptor-chain-across-question-accepted`,
`adaptor-chain-as-for-iterable-accepted`, `adaptor-by-ref-for-then-reuse-accepted`,
`adaptor-name-clash-two-traits-rejected` (T0044) and `adaptor-name-clash-qualified-accepted`
(`Iterator.take(move it, 3)`), `zip-two-scoped-sources-rejected` (ch01 R19c),
`zip-scoped-and-owned-accepted`, `scoped-into-concrete-sink-rejected` (01-ownership, R19c(b)),
`scoped-through-generic-sink-result-scoped-rejected` (01-ownership: the result
outlives `v`), `scoped-through-generic-sink-consumed-accepted`,
`rigid-to-dyn-rejected` (09-types, R10(c)), `callable-field-method-form-rejected`
(09-types, T0043 on `self.f(x)`), `callable-field-paren-call-accepted`,
`iterator-impl-linear-self-rejected`, `iterator-impl-linear-item-rejected`,
`try-fold-method-accepted`, `consumer-count-drops-items-accepted`
(a non-`Copyable`, non-linear `Item`).

---

## 2. O1 — linear types

### 2.1 Mechanism in one paragraph

Linearity is a property of TYPES, `lin(T)`, computed from declarations alone:
a type constructor is declared linear by `impl Linear for T {}` (`Linear` a
prelude marker trait on the `Shared` model, ch01 Rules 21-21b) and linearity
PROPAGATES structurally through fields, payloads and tuple components (no
declaration on the aggregate). Inside a generic body a rigid type is linear
unless a bound says otherwise (`Droppable`, `Copyable`, or `Iterator`, which
implies `Droppable`); `Droppable` is a built-in structural marker that no
`impl` may define. The obligation is checked by the move/liveness pass ch01
Rule 6 already runs: a live binding of linear type at a scope exit is the
error. Two new prelude names, no keyword, no attribute.

### 2.2 Declaration versus inference — the choice and the alternatives

Chosen: **declared base, inferred propagation.** Alternatives rejected:
(i) *attribute* `@linear(by: X.deinit)` naming the consumer — it needs the
resolver to resolve a deferred method path or to carry an unchecked string;
the marker-trait form reuses ch09 Rules 12/24 and the diagnostic can name the
consumers by a signature-only rule (§2.7). (ii) *Declared propagation* on the
`Shared` model (`impl[T: Linear] Linear for Option[T] {}` required on every
generic aggregate) — forgetting it means a silent leak, and it is boilerplate
on every `struct Pair[T]`; `Shared` is opt-in safety, linearity is
opt-out-impossible safety, so the polarities differ. (iii) *Inference of the
base* from "has a `sink self` method named `deinit`/`close`" — a name
convention is not a rule. (iv) *A runtime contract instead of a static rule
in generic bodies* (ch10 Rule 11c's current answer) — the owner's decision is
"the compiler MUST reject"; the `Droppable` bound makes generic drops
static; Rule 11c's trap survives only on `deinit_empty` (§2.3 L3).

### 2.3 Normative rules (ch01 unless stated; ch01 assigns numbers, suggested Rules 22-22h)

**L1 (`Linear`, ch01 + ch08 R17 + ch09 R24).** `Linear` is a prelude marker
trait with no methods. `impl Linear for T {}` MUST appear in the module
defining `T`; `T` MUST be a `struct` or `enum` named by its declaration
(never a type parameter, ch09 Rule 18). The impl MAY have type, const and
brand parameters and MUST NOT carry a bound on any of them: whether a
constructor is linear is a fact of the constructor, never of an
instantiation. Built in: `Own[T, A]` (ch09 Rule 5) is linear by language
rule. Std declares linear: `Block[A]`, `Vec[T, A]`, `Map[K, V, A]`,
`String[A]`, `fs.File`, `fs.Entries`, `net.Conn`, `net.Listener`,
`proc.Child` (ch10 Definitions' list, plus `Entries`, which Rule 41 calls
linear but the list omits). `Linear` MAY be used as a bound; it adds no
operation (ch09 Rule 24).

**L2 (`lin`).** For a normalised type: `lin(T)` is true iff (a) `T`'s head has
an `impl Linear` (ch09 Rule 12 lookup; no bounds to check by L1), or (b) `T`
is a `struct`, `enum` or tuple and some field, payload component or tuple
component, with `T`'s arguments substituted, has `lin` true, or (c) `T` is a
rigid type parameter or neutral projection that is not `Droppable` (L4). It
is false for every primitive, `()`, `never`, `Str`, `Slice[T]`, `Ref[T, A]`,
`rawptr`, `Range`/`RangeIncl`, `Array[T, N]` and `vector[T, N]` with
non-linear `T` (L3), `mask`, `atomic[T]`, `fn` and closure types, `dyn Tr`,
`Arena[T, A]`, every allocator and root-capability type. Qualifiers (`iso`,
`imm`, `secret`) do not change `lin`. Cost: structural descent, memoised per
(head, arguments), linear in the number of distinct subterms (the shape of
ch09 Rule 20); it terminates because ch09 Rule 14 forbids an infinite type
outside the indirections `Own`/`Ref`/`Arena`/`Slice`/`rawptr`/`fn`/`dyn`, and
`lin` does not descend into those (`Own` is linear by (a) without descent;
the others are never linear).

**L3 (arrays and inline buffers).** `lin(Array[T, N]) = lin(vector[T, N]) =
lin(T)`. A CONCRETE `Array[X, N]`, `vector[X, N]`, `atomic[X]` or
`Buffer[X, N]` with `lin(X)` true MUST be rejected where the type is written
or instantiated (ch09 Rule 11's neighbourhood, new code): an element can leave
an array only by a partial move, which Rule 4a(c) forbids, so such a value
could never be consumed. In a generic body `Array[T, N]` with rigid `T` is
well-formed and its values obey L4. Consequence for std (ch10 Rules 23-25):
`clear` and `deinit` move to bounded impl blocks — `impl[T: Droppable, A:
brand] Vec[T, A] { pub fn clear(inout self); pub fn deinit[L: Allocator[A]](sink
self, inout a: L); }` (drops the elements, frees, TOTAL) — and the
unbounded block gains `pub fn deinit_empty[L: Allocator[A]](sink self, inout
a: L) pre self.len() == 0;` (frees the block; the `pre` is the one surviving
`contract` trap of Rule 11c); `Map` likewise with `V: Droppable` (`K` is
already `Copyable` through `Hash + Eq`); `Buffer.clear` needs `T: Droppable`;
`Buffer[X, N]` with linear `X` is rejected outright by this rule, which
retires Rule 11c's "container of a linear element" for `Buffer`. `Vec` and
`Map` and `String` are linear ALWAYS (not "while cap > 0"): `deinit` on an
empty container is total and free.

**L4 (rigid types; ch09 Rule 57 amendment).** `Droppable` is a prelude marker
trait that MUST NOT be implemented by any `impl` (writing one is an error).
`X: Droppable` holds iff `lin(X)` is false. A rigid type parameter is
`Droppable` iff its declared bounds include `Droppable`, `Copyable` (which
implies it) or `Iterator` (L5); a neutral projection `P.A` iff the bounds its
trait declares for `A` or the constraint entries on `P.A` in scope do. Rule
57's "dropping it" becomes "dropping it, if `Droppable`": letting a
rigid-typed value go out of scope, `discard`ing it, matching it with `_`, or
evaluating it as an expression statement is T0057 unless the type is
`Droppable`; binding, passing by a convention, moving, storing in an
aggregate and returning stay available for every rigid type. This is the
conservative assumption the owner asked for: a generic body that drops must
say so in its signature, and no error ever depends on an instantiation (ch09
Rule 59: the error is at the definition, against the bounds).

**L5 (`Iterator` prerequisites; ch09 Rule 21 amendment).** The language-known
declaration becomes `trait Iterator { type Item: Droppable; fn next(inout
self) -> Option[Self.Item]; ... }` (provided members: ch10). `impl Iterator
for S` MUST be rejected unless `S: Droppable`, and a bound `P: Iterator`
implies `P: Droppable` — the second language-known prerequisite after
`IndexMut`/`Index`, stated in the same sentence of Rule 21. Consequence: v0.1
has no linear iterator and no linear item; an iterator over a linear source
takes it `inout` and is `scoped` to it (as `SliceIter` already is), and a
container of linear elements is emptied by `pop`/`remove`, never iterated by
value.

**L6 (the obligation and its consumers).** A live binding — local, `sink`
parameter, pattern binding, `with` binding excluded (Rule 15a) — of linear
type carries an obligation. Exactly these discharge it, each a move of the
WHOLE place under Rules 2 and 4a: (i) `move p` to a `sink` parameter, the
implicit receiver move into `sink self` (Rule 2, ch09 Rule 46), `return p` /
`return move p`, the function body's tail value, `raise p`, `spawn f(move
p);` and the receiver form `spawn p.run();` (Rule 4a(e)), `for x in p`
(ch09 Rule 31 — legal only when `p` is not linear, by L5, so vacuous),
assignment `q = p;` / `q = move p;` (the obligation now lives on `q`), and
use as a struct-literal field, variant payload or tuple component (the
aggregate is linear by L2(b) and inherits the obligation); (ii)
destructuring by a `match` whose arm binds every linear component with `let
n` — a `_`, an omitted `{ }` field (ch09 Rule 50: "omitted fields match
anything") or a literal pattern facing a linear component is a drop and MUST
be rejected; (iii) a `defer` or `errdefer` body that moves `p`, on the exits
it covers (§3.5). NOT consumption: `discard p;` and `consume p;` (both end
the liveness of a non-linear place and MUST be rejected on a linear one —
ch10 Rule 11 already says so for `discard`), a `let` or `inout` pass, a copy
(L7), a closure capture (L9), a trap (§3.8), a `dyn` coercion (L8).

**L7 (`Copyable`).** `impl Copyable for T` MUST be rejected when `lin(T)`;
ch09 Rule 23's built-in `Copyable` list contains no linear type (it already
excludes `Own`).

**L8 (erasure; ch09 Rule 10(c) amendment).** A linear value MUST NOT be
coerced to `dyn Tr` — add "or linear" beside "brand-mentioning or scoped" in
Rule 10 — and neither may a rigid one (§1.5(d)).

**L9 (closures, spawn, arenas).** A closure captures by access and "MUST NOT
move a place it captures" (Rule 4a(e)), so a closure never holds an
obligation, `lin` of a closure type is false, and a linear local captured by
a closure is still consumed by the enclosing scope after the closure's last
use. A structured `spawn` consumes by `move` (Rule 13) and the callee's
`sink` parameter obeys Rule 4 in the task. A `with arena`/`with allocator`
block is a scope for L10; its binding is live for the block's own
`defer`/`errdefer` bodies (§3.5(f)), so `defer v.deinit(&a);` inside the
block is the idiom, and Rule 15 already guarantees no brand-mentioning
linear value leaves the block.

**L10 (the scope-exit check).** At every point where control leaves a scope
— a block's `}` (including a `with`, `parallel`, loop-body, arm or closure
block), `return`, `raise`, the error exit of `?`, `break`/`continue` (which
leave the loop body's scope and every scope nested in it) — after the
scope's pending `defer`/`errdefer` bodies have been accounted for (§3.5),
every binding declared in the scopes being left that is live and of linear
type MUST have been consumed; otherwise the diagnostic of L11. The same
error is reported for a linear TEMPORARY: an expression statement whose
value is linear, `let _ = e;`, a `_` binding of a tuple `binding`, a call
result not bound; for a `var` of linear type assigned while live
("overwrites an unconsumed value"); and for a `sink` parameter of linear
type (this diagnostic supersedes Rule 4's wording for linear types; Rule 4
stays for the rest).

**L11 (diagnostic; normative content).** The diagnostic MUST carry: the
value's name (or "the result of `f()` at L:C"), its type as displayed by
ch09 Rule 20, the scope left and the exit's kind and location (`}` of the
block opened at, `return` at, the `?` at, `raise` at, `break` at), and the
consumers: for a type whose head is declared linear, every `sink self`
receiver method of that head and every function or method declared in the
head's defining module that has a `sink` parameter whose type has that head,
excluding `@unsafe` declarations — for `Vec[i32, heap]` that is
`Vec.deinit(&<allocator>)`, for `Own[i64, a]` it is `Allocator.deinit`
(`a.deinit(move x)`); for an inferred-linear aggregate, the linear field or
component names and the words "destructure it with a pattern that binds
them, or move the whole"; for a rigid type, "`T` may be linear: bound it
`Droppable` or consume it". Text (not normative): "`v` of linear type
`Vec[i32, heap]` is not consumed on the path leaving `main`'s body at the `?`
at 14:5; consume it with `Vec.deinit(&<allocator>)`, or `defer`/`errdefer`
it".

### 2.4 Interaction with existing rules

- **`?` (ch02 Rules 1-3).** The error exit of `?` is a scope exit (L10) of
  every scope up to the function body. `let v: Vec[i32, h] = Vec.new();
  v.push(&h, 1)?;` alone is therefore REJECTED (`v` live at the `?`); the
  writable forms are `errdefer v.deinit(&h);` before the `?`, or `defer`. A
  raised error that is itself linear is consumed by `raise` (L6(i)); std's
  error types are `Copyable` (ch10 Rule 7), so this never arises in std.
- **Rule 4a bans.** (c) partial moves: `s.v.deinit(&h)` on a field place is
  rejected as today; the idiom is a `sink self` method on the aggregate, or
  a `match` that binds the fields. (b) loops: a linear declared outside a
  loop and consumed inside must be re-initialised before the next iteration;
  a linear declared inside is checked at the body block's `}` every
  iteration. (d) a linear `inout` parameter is never consumed by the callee
  (it cannot be moved from); a linear `let` parameter likewise. (e) closures
  cannot consume.
- **Implicit receiver move (Rule 2, ch09 Rule 46).** `v.deinit(&h)` is the
  consuming call; a use after it carries Rule 46's diagnostic. A chain
  `it.map(f)` on a linear `it` cannot occur (L5).
- **Rule 8 (merge agreement).** Unchanged and load-bearing: because every
  path must agree on liveness, "consumed on some paths" is already an error,
  so an obligation is never a maybe (§2.5).
- **ch03 Rule 16 lowering.** The `deinit` witness slot for a linear type
  traps (`contract`) — it is never reachable from accepted code (L4 forbids
  the rigid drop), so the slot exists only for the monomorphised/witness
  symmetry ch09 Rule 59 requires.
- **`secret`.** Orthogonal; `lin` ignores qualifiers.

### 2.5 The analysis is one forward pass (proof sketch)

ch01 Rule 6: "Exclusivity is one forward dataflow pass per function over
projection paths, no fixpoint, no interprocedural analysis"; Rule 8: "At a
CFG merge every path MUST agree on each local's liveness; disagreement MUST
be an error". The linearity check adds no state: the per-path state is the
liveness map Rule 6 already carries ({uninitialised, live, dead} per path),
and the obligation of a binding is the conjunction "live and `lin(type)`",
where `lin` is a function of the binding's declared type (ch09 Rule 31: every
binding's type is fixed at its declaration). At a merge Rule 8 rejects any
disagreement, so the join is the identity on agreeing states and an error
otherwise — this is where drop-flag designs go wrong (they join "live" with
"dead" into "maybe" and then need a runtime flag or a backward pass); Fors
has no such element. At a scope exit the check reads the current live set
restricted to the scopes being left: O(bindings in those scopes), which an
implementation keeps as per-scope lists. Loop bodies: the loop-head merge is
a Rule 8 merge like any other (Rule 4a(b) states the consequence); the body's
`}` is an exit visited once per textual occurrence, not per iteration.
`defer`/`errdefer` bodies are analysed once each into an effect summary
(§3.5) and applied at exits, so no body is re-walked. Hence one pass, in the
same order as the existing pass, with no backtracking.

### 2.6 What O1 forbids that is legal today (the migration list)

- Any path on which a `Vec`, `Map`, `String`, `Own`, `Block`, `File`,
  `Entries`, `Conn`, `Listener` or `Child` goes out of scope unconsumed — in
  particular EVERY `?` after creating one without an `errdefer`/`defer`. Spec
  examples: ch10 `app.words` (`v.push(&heap, 1)?` with `v` live), the
  `Allocator.create` provided body (`self.alloc(...)?` — `b` is consumed by
  `own_raw` on the success path and nothing is live at the `?`: fine), ch04's
  `fetch` (`s: net.Conn` across `?`), ch02's examples with `Own`. Corpus:
  the 33 files listed by the spec stage's grep (`Vec.new`, `.create(`,
  `from_str`, `.open(`, `.connect(`, `.run(`, `.listen(`, `.alloc(`) — at
  HEAD: `10-std/{alloc-failure-is-error-value-accepted, free-wrong-brand-rejected,
  fixed-allocator-in-needs-empty-module-accepted, alloc-without-question-rejected,
  heap-brand-mismatch-rejected, main-heap-parameter-accepted,
  heap-brand-named-by-parameter-accepted, prelude-page-allocator-without-import-accepted,
  own-sent-to-unstructured-task-rejected, linear-element-container-deinit-trap,
  linear-moved-to-caller-accepted, vec-push-wrong-brand-allocator-rejected,
  vec-dropped-without-deinit-rejected}`, `01-ownership/{arena-*, brand-param-*,
  with-*, scoped-*, shadow-with-arena-rejected}` and `09-types/{brand-inferred-for-callee-accepted,
  brand-identity-mismatch-rejected, two-brands-one-param-rejected}`; each
  `*-accepted`/`run-ok` file gains the consumption (or a `defer`), each
  `*-rejected` file must keep its ORIGINAL diagnostic first (add the
  consumption so the new error does not mask the tested one).
- `Buffer[X, N]`, `Array[X, N]`, `vector[X, N]`, `atomic[X]` with linear `X`
  (L3). `10-std/linear-element-container-deinit-trap` changes meaning: for
  `Buffer` it becomes a `check-error` (L3); for `Vec` it becomes
  `deinit_empty` with a `contract` trap.
- `Vec.clear`/`deinit`, `Map.clear`/`deinit`, `Buffer.clear` on a
  non-`Droppable` element type (L3); ch10 Rule 11c's text is replaced.
- In generic bodies: dropping a rigid-typed value without a `Droppable`/
  `Copyable`/`Iterator` bound (L4). Std: `Vec.clear` etc. (moved to bounded
  blocks); `Buffer.push` (returns the value: fine); `Map.insert` already
  returns the replaced value as `Option[V]` (ch10 Rule 25, checked), so no
  drop occurs there. Corpus: any 09-types test whose generic
  body lets a rigid local or `let`-pattern binding die (the spec stage greps
  `fn .*\[.*\]` bodies; expected to be few and fixable by a `T: Copyable`
  bound the tests mostly already carry).
- `impl Copyable for T` with linear `T` (L7); `dyn` of a linear or rigid
  value (L8); `_`/omitted fields/literals over linear components (L6(ii));
  `consume p;` on a linear (L6).
- `impl Iterator for S` with linear `S` or linear `Item` (L5).
- Two new prelude names `Linear`, `Droppable` (ch08 Rule 17): a user item so
  named is N0013 (as for `Iterator`).

### 2.7 Rejected alternatives, recorded

- **Rigid types non-linear by default with a positive `T: Linear` bound
  meaning "the callee promises to consume"** — inverts the meaning of a bound
  (an upper bound on what may be passed) and needs a per-instantiation check
  ("a linear argument to an unbounded parameter"), which ch09 Rule 59 forbids
  in spirit and Rule 1 in cost.
- **Constraint entries on impls for the drop side** (`impl[I: Iterator,
  I.Item: Droppable] Iterator for Filtered[I]`) — needs a narrow relaxation
  of ch09 Rule 62; unnecessary once `Item` is bounded in the trait (L5).
- **Runtime trap on a rigid drop** (extend ch10 Rule 11c) — not "the
  compiler MUST reject".
- **Linear as a qualifier / keyword** (`linear struct`) — a new keyword for
  what a marker trait expresses; the owner asked for none if one suffices.
- **Consumption by `discard`** — ch10 Rule 11 already forbids it; keeping
  the ban is what makes "explicit allocators" non-decorative.

### 2.8 Chapter edit map for O1

ch01: new Rules 22-22h (L1-L11), Rule 4a(e) cross-reference, Rule 8's
note; ch08 Rule 17: `Linear`, `Droppable` in the prelude; ch09: Rule 5
(`Own` linear), Rule 10(c), Rule 21 (L5), Rule 23 (L7), Rule 24 (two more
markers; `Droppable` has no impls), Rule 50 (`_` over a linear component),
Rule 57 (L4), Rule 11 (L3); ch10: Definitions (add `Entries`), Rule 11
(replace 11c), Rules 23-26 (`Droppable` blocks, `deinit_empty`), Rule 33
(now a language fact), Rule 55 (trap list: `deinit_empty` only), Rule 51
(linear types list = `Linear` impls); README fact table rows.

### 2.9 Uncertainties, with the experiment that settles each

- *Closure capture extent.* ch01 does not define how long a closure's
  captures are accessed. §1.5(a)'s induction assumes a closure cannot carry a
  rigid value out of its scope; this holds if captures are accesses whose
  extent is the closure value's lexical scope (the reading Rule 4a(e) implies).
  Experiment: corpus test `closure-returned-with-local-capture-rejected` under
  ch01 as written; if it is not rejected today, ch01 needs the extent rule
  before Rule 19c is sound.
- *Copyable scoped values through concrete `let` parameters.* `fn keep(let
  s: Str) -> Holder { return Holder { s: s }; }` called with a scoped `Str`
  yields an unscoped `Holder`. Rule 19c(b) does not close this (it is `let`,
  not `sink`). Pre-existing; independent of round 6. Experiment: test
  `scoped-copy-into-field-via-let-param-rejected`; if ch01 R19a's body-side
  wording does not catch it, ch01 must treat a `let` parameter's value as
  scoped to that parameter inside the body.

### 2.10 Conformance tests O1 needs (`tests/conformance/01-ownership` unless noted)

`linear-local-dropped-at-block-end-rejected`, `linear-local-dropped-at-return-rejected`,
`linear-local-dropped-at-question-rejected` (detail names the `?`), `linear-local-dropped-at-break-rejected`,
`linear-temporary-expression-statement-rejected`, `linear-let-underscore-rejected`,
`linear-var-overwritten-rejected`, `linear-consumed-by-sink-call-accepted`,
`linear-consumed-by-return-accepted`, `linear-consumed-by-struct-literal-then-aggregate-rejected`
(the aggregate inherits), `linear-aggregate-destructured-accepted`, `linear-match-underscore-rejected`,
`linear-match-omitted-field-rejected`, `linear-option-matched-accepted`, `linear-in-loop-reinit-accepted`,
`linear-in-loop-consumed-once-rejected` (R4a(b)), `linear-field-partial-move-rejected` (R4a(c)),
`linear-captured-by-closure-still-owed-rejected`, `linear-spawn-move-accepted`,
`linear-with-block-exit-rejected`, `linear-with-block-defer-accepted`, `linear-consume-rejected`,
`linear-copyable-impl-rejected` (09-types), `linear-to-dyn-rejected` (09-types),
`linear-array-element-rejected` (09-types, L3), `linear-buffer-element-rejected` (10-std),
`rigid-drop-without-droppable-rejected` (09-types, T0057), `rigid-drop-with-droppable-accepted`,
`rigid-drop-with-copyable-accepted`, `rigid-iterator-drop-accepted` (L5 implication),
`droppable-impl-rejected` (09-types), `linear-impl-with-bound-rejected`,
`linear-impl-outside-defining-module-rejected` (08-names N0021), `vec-clear-linear-element-rejected` (10-std),
`vec-deinit-empty-nonempty-trap` (10-std, `contract`), `vec-linear-always-empty-deinit-accepted` (10-std),
`user-linear-type-diagnostic-names-consumer-rejected` (detail: value, type, exit, `Res.close`).

---

## 3. O2 — `defer` and `errdefer`

### 3.1 Grammar (ch07, normative)

```
stmt            = ... | defer_stmt | errdefer_stmt | ... ;   (* two alternatives appended *)
defer_stmt      = "defer" ( block | expr ";" ) ;
errdefer_stmt   = "errdefer" ( block | expr ";" ) ;
```

`defer` and `errdefer` join the reserved keyword list (ch07 "Keywords —
reserved", with a production) and the statement synchronisation set (ch07
"Error recovery": `let var if match ... comptime defer errdefer`). No
identifier in `tests/conformance`, `std` or the spec is spelled either way
(checked 2026-09-20: the only hits are the words "deferred"/"defer" in
comments and a test's `detail`). The `expr ";"` form means exactly `{ expr;
}`; `defer x = 1;` is a parse error at `=` ("expected `;`": an assignment is
a `stmt`, not an `expr`), which is intended.

**Lookahead.** Disambiguation 9: "One token selects the statement: a
statement keyword". `defer`/`errdefer` are reserved tokens, so the choice is
LA 1. After the keyword, the current token decides: `{` is a `block` (no
`expr` starts with `{`, Disambiguation 2's closure-body argument), anything
else starts an `expr` that ends at `;`. LA 1. The struct-literal question
(`ident {`) cannot arise because a reserved word is not a `path` head. The
chapter's bound stays 2 tokens, and the lexer's 2 characters.

Rejected: a contextual `defer` — `defer {` would be a struct literal by
Disambiguation 1 and telling them apart needs the token after the `{`
(`ident ":"` vs anything), 3 tokens. A single `defer` with an error-only
modifier (`defer(error)`) — spends the attribute syntax on a keyword-shaped
thing; Zig's two words are the known-good spelling.

### 3.2 Semantics (ch01 or a new short section of ch02; normative)

**D1 (placement).** A `defer_stmt`/`errdefer_stmt` is a statement of the
`block` `B` that directly contains it (any block: function body, loop body,
`if`/`match` arm block, `with`, `parallel`, closure body, `comptime`
block). Its *body* is the `block` (or `{ expr; }`).

**D2 (when a `defer` body runs).** The body runs when control leaves `B` by
ANY exit — reaching `B`'s `}` (fall-through or tail value), `return`,
`raise`, the error exit of a `?`, `break` or `continue` that leaves `B` —
provided the `defer` statement was executed on that path, which, `B` being a
statement sequence, means it textually precedes the exit point in `B`. All
bodies pending in `B` run in REVERSE textual order, then the exit continues
into the enclosing block, whose pending bodies run next. On `return e;`,
`raise e;` and a tail value, `e` is evaluated (and moved into the result)
BEFORE the bodies run; a body cannot read or change the result. No runtime
registration exists: the set of bodies at each exit is static, and the
lowering is the inlining of the pending bodies at the exit (an
implementation MAY emit one copy and jump; the behaviour is the same).

**D3 (error exit; when an `errdefer` body runs).** An exit of `B` is an
*error exit* iff control leaves `B` because a `raise` statement, or a `?`
whose call failed, in `B` or in a block nested in `B`, propagates the error
out of the enclosing function (ch02 Rules 1-3); the error passes through
every block between the raise site and the function body, and each is left
by an error exit. `return`, fall-through, a tail value, `break` and
`continue` are normal exits; an `else |e| { ... }` handler that returns
makes a normal exit and one that `raise`s makes an error exit. An `errdefer`
body runs on the error exits of `B` after its statement, and never on a
normal exit; `defer` and `errdefer` bodies pending in `B` run interleaved,
in reverse textual order.

**D4 (what a body may contain).** A body is checked against `()` (ch09 Rule
31) and MUST NOT contain: `return`; `raise`; `?`; a `break` or `continue`
whose target loop is outside the body (a loop inside the body may use them).
A call to a `raises` function inside a body MUST carry an `else |e|` handler
that does not `raise` or `return` (it yields the success value or traps, ch02
Rule 5). Reason: on a normal exit there is nothing to attach an error to, and
on an error exit a second error would have to replace or be lost against the
first; a `return` from a body would turn an error exit into success
silently. Bodies MAY nest: a `defer` inside a body runs when that body's
block exits.

**D5 (captures, ownership and consumption).** A body mentions places of the
enclosing scopes; it is typed once and its ownership effects are summarised
once, as a map place → strongest access (`let` < `inout` < move), applied at
each exit where it runs. (a) Every place a body mentions MUST be live at
every exit at which the body runs (for `defer`: every exit of `B` after the
statement; for `errdefer`: every error exit after it); a move of such a
place between the statement and such an exit is Rule 4a(a)'s use-after-move,
reported as "`p` is moved at L:C but the `defer` at L':C' still needs it".
(b) A body that moves a place `p` (a `sink` argument, an implicit receiver
move, `move p`) is a *deferred consumption*: `p` stays live in `B` after the
statement and may be read and passed `inout` as usual; at each exit where
the body runs, `p` is moved by it — for §2 L10 this discharges `p`'s
obligation on exactly those exits. Hence `defer p.deinit(&h);` consumes on
every exit, and `errdefer p.deinit(&h);` consumes on the error exits only,
so the normal exits must consume `p` otherwise (typically `return move p;`,
which is legal precisely because the `errdefer` does not run there). (c) A
body's `let`/`inout` accesses are NOT accesses during `B` (else `defer
v.deinit(&h); v.push(&h, x)?;` would be a Rule 7 conflict); they are
accesses at the exit point. (d) Loops: a body in a loop's block that moves
a place declared outside the loop is Rule 4a(b)'s move inside a loop —
rejected unless re-initialised; this falls out of (b). (e) A body may
capture nothing a closure could not, but it is not a closure: it may move
(it runs at most once per exit, and exactly one exit is taken). (f) The
binding of a `with` block, and every `let`/`inout`/`sink` parameter, is live
for the bodies of its own block's exits; the allocator dies after the
block's bodies have run.

**D6 (loops).** The body block of `for`, `while`, `parallel for`, `simd for`
exits at the end of every iteration and on `break`/`continue`, so a `defer`
inside runs once per iteration. A `defer` outside the loop is unaffected by
iterations.

**D7 (`return` from inside a body).** Rejected (D4).

**D8 (traps).** A trap runs NO deferred body: ch02 Rules 6-7 make a trap
"one breakpoint-class instruction ... it MUST NOT allocate or call", and the
process ends there. Consequence for std (ch02 Rule 7 gains one sentence, ch10
Rule 40(b) two): after a trap, an open `File`, `Conn`, `Listener` or `Child`
is abandoned to the operating system, no `close`/`shutdown`/`wait`/`free`
runs, buffered `Stdout` bytes MAY be lost (already Rule 40(b)); no std
invariant MAY depend on a deferred body running on abnormal termination —
there is no temporary-file cleanup, lock-file release or flush-on-exit
promise on the trap path, and none will be added. A program that needs
durability across the risky step writes and flushes before it.

**D9 (`main`).** `main`'s bodies run as part of `main`'s exit, before the
runtime does anything of §4.

**D10 (`comptime`).** Same semantics under the FMIR interpreter (ch04 Rule
11); no special case.

Rejected alternatives: Go-style function-scoped `defer` with a runtime
stack — needs a runtime list and makes a `defer` in a loop accumulate;
block scope needs no runtime state and matches Zig. `errdefer |e|` binding
the error — nothing in v0.1 needs to inspect the error in cleanup; liftable.
Allowing `?` in a body with "first error wins" — hides errors.

### 3.3 Typing (ch09 Rule 31 sentence)

A `defer`/`errdefer` statement has type `()`; its body is checked against
`()`; the `expr` form is checked as an expression statement.

### 3.4 What O2 forbids that is legal today

Nothing: the words `defer`/`errdefer` become reserved (no identifier in the
repository uses them), and everything else is additive. What it makes
WRITABLE is the cleanup that O1 now demands on every `?` path.

### 3.5 Where O2 and O1 meet — the exact counting rule

An obligation on `p` counts as discharged on an exit `X` of the function
iff, on the path to `X`, `p` is moved by the code before `X` or by a pending
body that runs at `X` (D5(b)). Because bodies are summarised, the pass at
each exit point applies, in reverse order, the summaries of the pending
bodies of every block being left, then runs L10's check. A `defer` that
moves `p` therefore never leaves `p` live at an exit after it; an `errdefer`
does so only on normal exits, which is why `errdefer` is the right word for
"undo the allocation if we fail" and `defer` for "always release".

### 3.6 Lookahead bound

Stated in §3.1: LA 1 for both decisions; ch07's largest lookahead remains 2.

### 3.7 Chapter edit map for O2

ch07: keyword table (two reserved-with-production words), `stmt`, the two
productions, Disambiguation 9's keyword list, the statement sync set, the
formatter note (`defer x;` on one line); ch01: D1-D9 as a new rule group
next to Rule 4a (suggested Rule 23-23f) — ch01 because bodies are an
ownership/flow construct; ch02: Rule 7's trap sentence, Rule 5's cross-ref
(handler inside a body); ch09: Rule 31's sentence, Rule 33 (no `return` in a
body: T0033); ch10: Rule 40(b).

### 3.8 Traps, restated for the std stage

Nothing deferred runs on a trap. ch10 Rule 53's syscall holders and Rule 40
must not assume it.

### 3.9 Conformance tests O2 needs (`tests/conformance/07-grammar` for parse, `01-ownership` for flow, `02-failure` for run)

Parse: `defer-block-parses`, `defer-expr-parses`, `errdefer-block-parses`, `errdefer-expr-parses`,
`defer-assignment-rejected` (parse-error at `=`), `defer-as-identifier-rejected`,
`errdefer-as-identifier-rejected`, `defer-missing-semicolon-recovers`, `defer-nested-parses`.
Flow: `defer-consumes-linear-on-all-exits-accepted`, `errdefer-consumes-on-error-exit-accepted`
(`return move v;` on the normal exit), `errdefer-normal-exit-unconsumed-rejected`,
`defer-place-moved-before-exit-rejected` (D5(a) diagnostic), `defer-inout-use-after-defer-accepted`
(D5(c)), `defer-in-loop-moves-outer-rejected` (R4a(b)), `defer-in-loop-per-iteration-accepted`,
`defer-return-inside-rejected`, `defer-raise-inside-rejected`, `defer-question-inside-rejected`,
`defer-break-outer-loop-rejected`, `defer-inner-loop-break-accepted`, `defer-handler-inside-accepted`,
`defer-with-block-allocator-live-accepted`, `defer-in-closure-body-accepted`, `defer-nested-body-accepted`.
Run (`run-ok`, stdout order): `defer-reverse-order-run-ok` (prints `3 2 1`), `defer-runs-on-return-run-ok`,
`errdefer-skipped-on-return-run-ok`, `errdefer-runs-on-question-run-ok` (see §4.5's `run-error` kind),
`defer-per-iteration-run-ok`, `defer-result-evaluated-first-run-ok`, `defer-not-run-on-trap` (`trap`
kind: stdout must NOT contain the deferred line — note ch10 Rule 40(b): use `Stderr` for the marker).

---

## 4. O4 — an error raised out of `main`

### 4.1 Ownership

ch02 owns what a raise DOES (Definitions: "only this chapter defines what a
trap *does*"; the same for a raise that nobody catches) → the semantics and
the line format are ch02's, as a new Rule 16. ch04 Rule 8 owns `main`'s
shape → one sentence: `main` MAY declare `raises E` for any `E`, and an error
leaving `main` is ch02 Rule 16. ch10 Rule 40 owns the runtime entry shim's
observable behaviour → the ordering with the `Stdout` flush, the exit-status
table and the `SIGPIPE` clause.

### 4.2 Normative (ch02, new Rule 16)

If `main` is declared `raises E` and an error `e: E` propagates out of it,
then, after `main`'s own `defer`/`errdefer` bodies have run (§3 D9): (a) the
runtime flushes `Stdout` exactly as on a normal return (ch10 Rule 40(a)),
ignoring any failure; (b) it writes exactly ONE line to the standard error
file descriptor, unbuffered: the bytes `error: `, then `render(e)`, then
`\n`; (c) the process exits with status 1, whether or not (a) or (b)
succeeded; nothing is written to `Stdout` by this rule. `render` is defined
on the static type `E`, recursively: an enum value is its type's
fully-qualified path (module path and item name, e.g. `std.net.Error`,
`app.Error`), `.`, the variant name, and, for a variant with a payload, `(`
the rendered components separated by `, ` `)` or `{ ` `name: ` rendered
`, ... }` for a struct-form variant; a struct value is its path followed by
`{ name: rendered, ... }` over its fields in declaration order; a tuple is
`( ... )`; an integer is base 10 with a leading `-` if negative, no grouping
or padding; `bool` is `true`/`false`; `()` is `()`; `Str` is the text
between double quotes with `\`, `"`, newline, carriage return and tab
escaped as `\\`, `\"`, `\n`, `\r`, `\t` (so the line stays one line);
any other type (`Own`, `Slice`, `fn`, `dyn`, a root-capability or allocator
type, a rigid type) renders as `..`. No locale, no width, no colour. Example:
`error: std.io.Error.closed`, `error: app.Error.timeout(3, "host")`.

**Failure of stderr.** If the write in (b) fails — an error return, a short
write, a closed descriptor — the runtime MUST NOT retry, MUST NOT write the
line anywhere else, MUST NOT trap, and MUST still exit with status 1. The
entry shim installs `SIG_IGN` for `SIGPIPE` before `main` runs, so a write to
a closed pipe fails as `io.Error.closed` in `main` (ch10 Rule 39's latching
then works as described) and cannot end the process with a signal here.

### 4.3 Exit-status table (ch10 Rule 40(d), normative)

0: `main` returned and the final `Stdout` flush succeeded with no latched
error. 1: an error left `main` (this rule). 2: `main` returned but the final
flush failed or an error was latched on `Stdout` (Rule 40(a) said "non-zero";
this pins it, and keeps it distinct from 1 so a script can tell "the program
failed" from "the output did not arrive"). A trap: the process dies by the
breakpoint instruction (ch02 Rule 6) and reports through the operating
system's signal status, never through 1 or 2.

Rejected: printing the payload through a `Writer` trait the error type must
implement — a trait obligation on every error type for a line that is
almost always an enum name; printing nothing but the status — throws away
the only diagnostic a script gets; exit status from the variant's ordinal —
unstable across a variant addition (ch09 Rule 6).

### 4.4 What O4 forbids that is legal today

Nothing in the language; it defines behaviour that was "currently nowhere"
(ch10 Open question 5). Corpus `run-ok` tests whose `main` raises did not
exist because their exit could not be specified; the harness gains one
expectation kind (§4.5).

### 4.5 Conformance tests O4 needs (`tests/conformance/02-failure`; harness change in `tests/conformance/README.md`)

New expectation kind `run-error`: exits with status 1 and stderr equals
`detail` (one line, without the trailing newline in the directive). Tests:
`main-raises-unit-variant-run-error` (`error: main.Error.boom`),
`main-raises-payload-run-error` (`error: main.Error.code(7, "x\n")` with the
escape), `main-raises-std-error-run-error` (`error: std.mem.AllocError.out_of_memory`
via `mem.Counting`), `main-raises-flushes-stdout-run-error` (stdout content still
present, status 1), `main-raises-after-defer-run-error` (the deferred line precedes
on `Stderr`), `main-raises-nested-payload-run-error` (`..` for an `Own`),
`main-returns-latched-stdout-exit-2` (a new kind or `run-error` with status 2 —
the harness decides; document it), `main-raises-not-declared-rejected`
(ch02 Rule 1, existing behaviour, `check-error`).

---

## 5. Migration summary (what each later stage does first)

1. Spec stage: paste §2.3, §3.2, §4.2 into the chapters named in §2.8, §3.7,
   §4.1; amend ch09 Rules 10(c), 21, 23, 24, 50, 57, 11 and ch01 Rule 19c;
   rewrite ch10 Rules 11, 23-26, 33-35, 40, 51, 55 and drafting decision 16
   ("Adaptors and consumers are free functions" becomes "are provided
   methods; the ownership rule that made this writable is ch01 Rule 19c");
   update the README fact table.
2. Corpus stage: the test names of §1.9, §2.10, §3.9, §4.5; the migration
   list of §2.6; the `run-error` kind. `fors check` (resolver only) must stay
   clean on every new `check-error` test whose code is a ch01/ch09 code, as
   the 09-types rule already says.
3. Std stage: `seq.fors` per §1.2 and §1.7 (delete the free functions, add
   the trait with provided members, `(self.f)(...)`), `vec.fors`/
   `hashmap.fors` per L3 (`Droppable` blocks, `deinit_empty`), `alloc.fors`
   (`impl Linear for Block[A] {}`, `Own`), `fs.fors`/`net.fors`/`proc.fors`
   (`impl Linear for ...`), every std body that lets a linear value die on a
   `?` path (`errdefer`).

## 6. The five places the implementation will go wrong

1. **Treating the `defer` body's uses as accesses during the block** (D5(c))
   — the natural way to implement "the body needs `v` live" is to open an
   access at the `defer` statement, which then conflicts with every later
   `inout` use of `v`. The access opens at the EXIT, and only liveness is
   required in between.
2. **Joining liveness at merges with a "maybe" element** to accommodate
   linear obligations — ch01 Rule 8 already forbids disagreement; adding
   drop flags to "be helpful" breaks the one-pass property and the no-flags
   promise.
3. **Binding `U` through a callable BOUND** (`F: fn(...) -> U`) instead of
   through a `fn`-typed parameter — Rule 38 never binds through bounds, and
   the first `it.map(double)` with a fn item will be T0039. §1.2 fixes the
   signatures; the std stage must not "simplify" them back.
4. **Making `lin` an instantiation-time error** — e.g. rejecting
   `Pair[Own]` because `Pair` "does not declare linearity". `lin` is a
   FUNCTION of the type; the only errors are at scope exits (concrete code)
   and at rigid drops against bounds (generic code). Conversely, forgetting
   L3 and letting `Array[Own, 4]` exist creates an unconsumable value.
5. **Scoped chains**: the resolver/checker will be tempted to keep ch10's
   old `scoped(it)` on the adaptor signatures or to reject `v.iter().map(f)`
   under Rule 19a's "stored in a field" wording. Rule 19c(a) is the rule:
   the result inherits `v`'s scope because `Mapped[Self, U]` mentions
   `Self`; the field store inside the generic body is not the caller's
   concern. And `(self.f)(x)`, not `self.f(x)`.

## 6a. Verification amendments (round-6 verification stage, 2026-09-20)

Two of §1's claims were wrong as written and one of §6's warnings was
incomplete; the normative text is the spec's, this is the record.

- **`Mapped[I, U]` needs `U: Droppable`.** `impl[I: Iterator, U] Iterator
  for Mapped[I, U] { type Item = U; }` violates ch09 R17 (the RHS of `type
  Item` must satisfy the trait's `Item: Droppable` at the impl, with `U`
  rigid). `map[U: Droppable]` carries the same bound so a closure returning
  a linear value fails at `map` with T0012. `BufferIter`'s impl needs `T:
  Droppable` for the same reason (`Self: Droppable` with a rigid `T`).
- **The closure-capture hole was not optional** (§1 left it as ch01 Q5).
  With `Mapped` storing its callable, `return v.iter().map(|sink x| x +
  k)` under `scoped(v)` carried a closure over the dead local `k` out of
  the function: R19c(a) tracked the receiver's source and nothing tracked
  the closure's. Fix: ch01 R19d (a capturing closure is a scoped value
  whose sources are its captures), R19c(a′) (a `Copyable` or `fn`-typed
  argument is accounted for by a "contains `D`" descent of the declared
  result — which also closes ch01 Q6), and R19c(d) (a result keeps the
  sources of EVERY scoped argument; "two sources → reject the call" was
  replaced, because `v.iter().map(|sink x| x + k)` has two sources and
  must be a legal local, and ch01 R19 already decides what may be
  returned). ch09 R10(b) no longer rejects a capturing closure's coercion
  to its `fn` type; the sources survive on the value.
- **`it.map(same)` with a generic item is T0039** (ch09 R28: a generic
  `fn` in SYNTH mode needs explicit arguments, and the parameter type is
  not complete while `U` is unbound); write `same[I.Item]`.
- **An `errdefer` after which no error exit follows is an error** (ch01
  R23b): it is the diagnostic for the "errdefer written after the fallible
  call" mistake, and costs nothing because ch02 R16's exit set is
  syntactic.
- **"Hold `Option[X]`" for an array of linear elements was wrong**:
  `lin(Option[X]) = lin(X)`, so `Array[Option[X], N]` is ill-formed by ch01
  R22b too. A fixed number of linear values is a struct; a variable number
  is a `Vec`/`Map` released by `deinit_empty`.
- A sixth place the implementation will go wrong: opening a closure's
  capture accesses at the closure expression instead of for the extent of
  the value that holds it (ch01 R19d), which would let `let c = || k;`
  outlive `k` inside an adaptor.

## 7. Drafting decisions (round 6, mechanisms stage)

1. O3 first, and the verdict is "works with ch01 Rule 19c": lookup was never
   the obstacle; ownership was. No blanket impls.
2. `fn`-typed callable parameters, `Mapped[I, U]` with `U` a struct
   parameter, adaptor names unchanged, `by_ref` added, six raw pointers
   removed.
3. Linearity: `Linear` marker (declared base) + structural `lin` (inferred
   propagation) + `Droppable` structural marker for the drop side + rigid =
   linear unless bounded + `Iterator` implies `Droppable` and `Item:
   Droppable`. Arrays of linears are ill-formed. `Vec`/`Map`/`String` are
   linear always; `deinit` for `Droppable` elements, `deinit_empty` with a
   `pre` for the rest.
4. `defer`/`errdefer` reserved, block-scoped, statically inlined at exits,
   bodies summarised once; no `return`/`raise`/`?` inside; traps run nothing.
5. `main`'s error: ch02 Rule 16, `error: <path>.<variant>(...)`, status 1,
   stderr failure ignored, `SIGPIPE` ignored by the shim, status 2 for a
   failed final flush.
6. Everything above is signature-only and adds no unification, no worklist
   and no per-instantiation check; the near-linear type-check gate is
   unaffected, and the ownership pass stays one forward pass.
