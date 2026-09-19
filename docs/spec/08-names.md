# Chapter 8: Modules, names and visibility

## Status

Draft, 2026-09-19; verified and repaired the same day (see Drafting
decisions). Name resolution is a phase of its own: it runs after parsing
(ch07) and before type checking, and every MUST in this chapter is
decidable from the CSTs of the build's files plus the set of module
names. No rule here consults a type. What needs a type is listed in
Rule 22 and belongs to the checker.

## Scope

Owns exclusively: file-to-module mapping (one module per file) and legal
file names; `use` forms (per ch07's `use_decl`) and what each binds;
`pub use` re-export; non-transitive imports; the edge set of the module
graph and its acyclicity; order-independence of module-level
declarations; visibility (`pub`, private-by-default, fields, variants,
methods); the ban on a private item in a public signature; one namespace
per module scope; scopes and lookup; no-shadowing; which syntax positions
introduce or use a name, and which identifiers are not names at all;
segment-by-segment path resolution; binding-versus-reference in
patterns; the prelude's closed name list; the `impl` orphan rule and that
impls are not names; the boundary between this phase and the checker's
type-directed lookup. Not owned: capability semantics, the manifest, the
root module and what a re-export does to capability requirements (ch04);
brands (ch01); receiver-type dispatch (checker); grammar productions
(ch07). The grammar has no labels and no nested `fn`; none are defined.

## Definitions

- **Package**: a name (a `path`, from the manifest, ch04) and a source
  root directory. A build with no manifest (the conformance corpus) has
  one package whose name is empty and whose source root is the directory
  of the root file.
- **Universe**: the modules of the root package, of every resolved
  dependency (ch04 Rule 17), and of package `std`, which every build has.
- **Module**: the declarations of exactly one source file; its **name**
  is given by Rule 1.
- **Item**: a module-level `decl` of kind `fn`, `extern fn`, `struct`,
  `enum`, `trait` or `const`. An `impl_decl` is a declaration but not an
  item: it has no name (Rule 21).
- **Entity**: what a name denotes: an item, a module, a prelude entity
  (Rule 17), an enum variant, or a binding.
- **Binding**: a name introduced by a `gparam`, a `param`, a `let`/`var`
  or loop `binding`, a `with_stmt` identifier, a closure `cparam`, a
  `handler` identifier, a binding pattern (Rule 25), or the implicit
  `Self` (Rule 26).
- **Module scope**: the single mapping, per module, from identifier to
  entity made of the module's items, its imports and the prelude
  (Rule 13). There is no separate type, value or module namespace.
- **Member name**: a field, variant, method or trait-method name. Member
  names live in a table attached to their struct, enum, trait or `impl`
  block (Rule 27), never in a scope.

## Rules

1. **N0001** — Each `.fors` file under a package's source root MUST
   define exactly one module. Its name is the package name's segments,
   then the directory segments of the file's path relative to the source
   root, then the file name without `.fors`, joined by `.` (an empty
   package name contributes nothing). `R/img/decode.fors` in package
   `app` is `app.img.decode`. A `module` header is optional; when present
   its path MUST equal that name, else a compile error naming both.
2. **N0002** — Which module is the root module is decided by the build
   (ch04 Rule 8), never by a file name or by which module declares a
   `main`. Every module of the root package MUST be resolved under this
   chapter whether or not the root module reaches it; modules of other
   packages only when reached by an edge (Rule 7).
3. **N0003** — A `use` item takes exactly the forms of ch07's `use_decl`:
   `use p;`, `use p as c;`, `use p1, p2, ...;` (any comma-separated mix of
   the two), each optionally prefixed `pub`. No brace group, glob or
   relative form exists. Every `use` path is an absolute name in the
   universe; it is never looked up in a scope, so a local, item or
   prelude name never affects what a `use` means. `"as" ident` renames
   only the bound name (Rule 4); it does not change which path is
   resolved or which module-graph edge it creates (Rule 7).
4. **N0004** — A `use` path `s1. ... .sn`, optionally followed by
   `"as" c`, resolves as follows and binds exactly one name — `c` if an
   alias is given, else `sn` — in the importing module's scope.
   (a) If `s1. ... .sn` is the name of a module in the universe, the
   name denotes that module. (b) Otherwise, if `n >= 2` and
   `s1. ... .s(n-1)` is the name of a module `M`, then `sn` MUST be a
   `pub` module-scope name of `M` — a `pub` item of `M`, or a name `M`
   re-exports (Rule 5) — and the name denotes the same entity; a
   non-`pub` or absent `sn` MUST be a compile error naming `sn` and `M`.
   (c) Otherwise the path MUST be a compile error (unresolved import).
   If (a) holds and (b) would also succeed, the `use` MUST be a compile
   error naming both candidates. A `use` cannot reach deeper than an
   item: variants and other member names are never import targets. An
   alias binds only `c`; `sn` (or any intermediate segment) is not
   itself bound by an aliased `use` — `use a.b as c;` does not bind `b`.
   `"as" "_"` cannot be written: `_` is not an `ident`, so ch07 already
   rejects it as a parse error (an alias must be a usable name).
5. **N0005** — `pub use` additionally makes each name it binds — `sn`, or
   its alias `c` when `"as" ident` is given — a `pub` module-scope name
   of the importing module, denoting the same entity (item or module).
   Re-export chains are followed to the original entity; they terminate
   because the graph is acyclic (Rule 7). A re-exporting alias (`pub use
   a.b as c;`) makes `c`, not `b`, the name a third module sees when it
   imports this module's re-export. What an import or re-export does to
   capability requirements, and that a sealed capability never travels
   along one, is ch04 Rules 2-2a; this chapter adds nothing to it and a
   `pub use` grants nothing beyond the name.
6. **N0006** — Imports are not transitive: a name module `M` binds by
   `use` (aliased or not) is in `M`'s scope only. Another module sees it
   only by its own `use` of the original, or of `M`'s `pub use`
   (Rule 5) — under whatever name that `use`/`pub use` gives it, which
   may itself be a further alias.
7. **N0007** — The module graph has one edge per `use` path: to the
   module itself in Rule 4(a), to `M` in Rule 4(b); plus the implicit
   edges of Rule 17. Which prefix of a `use` path is a module depends
   only on the set of module names, so the explicit edge set is known
   from file names and headers before any item is examined. The graph
   MUST be acyclic; a cycle MUST be one compile error naming every
   module on it in edge order, starting from the cycle's
   lexicographically least module name. The check MUST precede every
   other rule of this chapter except Rules 1, 3 and 24, and is the
   rejection ch04 Rule 2 requires before its capability check. Modules
   are then resolved in dependency order, so an imported module's
   `pub` names are complete when its importers are resolved. When a
   cycle is reported, a Rule 4(b) "no such `pub` name" error whose
   target module is on a cycle with the importer MUST NOT be reported
   as well: with `pub use b.Y as X;` in `a` and `pub use a.X as Y;` in
   `b` the missing name is the cycle itself, reported once.
8. **N0008** — A `use` path whose edge (Rule 7) targets the module it
   appears in — `use m;` or `use m.item;` inside `m` — is a cycle of
   length one and MUST be a compile error naming the module.
9. **N0009** — Module scope is order-independent: an item MAY be
   referred to anywhere in its module regardless of textual order,
   including from `const` initialisers and signatures (a cyclic `const`
   dependency is a comptime error, ch04, not a name error). Bindings in
   a function body are order-dependent: each is in scope only over the
   region Rule 26 gives it, and a reference before that region does not
   see it (it is unresolved, Rule 14, unless something else has the
   name).
10. **N0010** — An item is private to its defining module unless marked
    `pub`. Naming a non-`pub` item of another module, by `use`
    (Rule 4) or as a path segment after a module (Rule 16), MUST be a
    compile error naming the item and its module.
11. **N0011** — Member visibility. A struct field is private to the
    module defining the struct unless marked `pub`. An enum variant and
    its payload fields are exactly as visible as the enum; `pub` on a
    field inside an `evariant` MUST be a compile error. A trait's
    methods are exactly as visible as the trait. A method in an inherent
    `impl T { }` is private to the module containing that `impl` unless
    marked `pub`; a method in `impl Tr for T { }` has the trait's
    visibility and `pub` on it MUST be a compile error. Naming a private
    member from another module — in `.name`, a struct literal `finit`,
    an `fpat`, or a method call — MUST be a compile error; because
    finding the member needs the type, the checker enforces this clause
    (Rule 22) using the visibility defined here.
12. **N0012** — The signature of a `pub` item MUST NOT name a non-`pub`
    item of its own module. "Signature" is: for `fn`/`extern fn`, every
    `gparam` bound, parameter type, `ret_type` and `raises` type; for a
    `struct`, its `gparam` bounds and the types of its `pub` fields; for
    an `enum`, its bounds and every payload type; for a `trait`, its
    bounds and every method signature; for a `const`, its type; and the
    signature of every `pub` method in an `impl` whose type is `pub`.
    The test is syntactic: each `path` in those positions is resolved
    (Rule 16) and its head entity inspected. Violation MUST be a compile
    error naming the leaked item.
13. **N0013** — A module scope holds each identifier at most once. It
    MUST be a compile error, reported at the second declaration in
    source order and naming the first, for two items of one module to
    share a name, whatever their kinds (a `struct` and a `fn` collide);
    reported at the item, for an item to have a prelude name (Rule 17);
    reported at the `use` path (or its `"as" ident`, when given), for an
    import — under the name it binds, `sn` or its alias — to bind the
    name of an item of the importing module (even one declared textually
    later) or a prelude name. An import that binds a name to the entity
    that name already denotes (a repeated `use`, the original plus its
    re-export, two aliases spelling the same name for the same entity,
    `use std.io;` beside the prelude's `io`) is not a collision. No
    item, import or binding may be named `Self` (Rule 26).
14. **N0014** — A name is looked up through the scopes enclosing its
    use, innermost first: bindings of enclosing blocks, match arms,
    closures, loops, `with` statements and handlers of the same
    function; the function's parameters; its generic parameters, then
    those of the enclosing `trait`/`impl` and `Self`; then module scope.
    A closure body sees the bindings of the function around it (whether
    a capture is legal is ch01's). Because of Rules 13 and 18 at most
    one visible entity ever has a given name, so the order is not
    observable. The names looked up this way are: the first segment of
    every `path` in an expression, a type, a `targ`, a `bracket_arg`, a
    `struct_lit`, an `impl` header or a pattern (subject to Rule 25),
    and the first identifier of a `place`. No hit MUST be a compile
    error (unresolved name). Nothing else is looked up (Rule 23).
15. **N0015** — Two imports (of one module or of different modules) that
    bind the same name — `sn` or an `"as" ident` alias — to different
    entities MUST be a compile error at the second `use` path, naming
    both, whether or not the name is ever used. The same entity imported
    twice under the same name (with or without an alias) is not a
    collision (Rule 13).
16. **N0016** — A multi-segment `path` resolves left to right. The
    first segment resolves by Rule 14. Then, by the kind of entity
    reached so far: **module** — the next segment MUST be a `pub`
    module-scope name of that module (Rules 5, 10), reaching that
    entity; a path that ends on a module, outside `use`, MUST be a
    compile error, and a module is reachable only through a name bound
    by `use` or the prelude (`a.b.f` needs `use a.b;` and is then
    written `b.f`). **enum item** — if the next segment is one of the
    enum's variants (Rule 27) it reaches that variant; otherwise it is a
    deferred segment. **anything else** (struct, trait, `fn`, `const`,
    prelude type or value, generic parameter, `Self`, variant, local,
    parameter) — every remaining segment is deferred. A **deferred
    segment** is a field, method or associated-item name: this phase
    records it unresolved and the checker resolves it by type
    (Rule 22). The algorithm is identical in type and expression
    position. Whether the entity finally reached is of a kind legal in
    its position (a type where a type is needed, a constant `targ`, a
    brand) is the checker's, since a bare `targ` path is classified
    there (ch07 Disambiguation 11).
17. **N0017** — The prelude is a closed list, present in every module
    scope. Types and traits: `i8 i16 i32 i64 u8 u16 u32 u64 isize usize
    f32 f64 bool Str Slice Array vector mask atomic rawptr Own Ref Arena
    Option Shared ErrorFrom`. Values: `some none reduce`. Modules: `io fs
    net proc time rand env gpu`, denoting `std.io`, `std.fs`, `std.net`,
    `std.proc`, `std.time`, `std.rand`, `std.env`, `std.gpu` (the homes
    of ch04 Rule 21's root-capability types). Resolving a path through a
    prelude module name adds an implicit edge (Rule 7) to that module,
    identical in every respect, ch04 Rule 2 included, to a `use std.x;`
    in the header. Package `std` has no dependencies, so an implicit
    edge from a non-`std` module cannot close a cycle; inside package
    `std` the prelude module names are not provided and `use` is written
    out, keeping Rule 7's header-only edge set exact wherever a cycle is
    possible. No other name is available without `use`. A function-local
    binding is allowed to shadow a prelude module name (Rule 18); this
    rule's implicit edge is computed from the path's name alone and MAY
    therefore over-approximate when a local shadows a prelude module: the
    edge to that `std` module is still added even where the name
    actually resolves to the local shadow instead of the module. This is
    harmless (an unneeded dependency edge, never a missing or wrong one).
18. **N0018** — No shadowing, with one exception. A binding MUST NOT
    have a name that Rule 14 would resolve at the point of the binding:
    a binding of an enclosing scope of the same function, a parameter, a
    generic parameter of the function or of its enclosing `trait`/
    `impl`, `Self`, or any module-scope name (item — including one
    declared textually later — import, or prelude name) — EXCEPT that a
    function-local binding (a `let`/`var` binding, a `for`/`parallel
    for`/`simd for` binding, a `param`, a `cparam`, a `"let" ident`
    pattern binding, or a `with arena`/`with allocator` identifier) MAY
    share a name with a prelude name (a prelude type, value or module,
    Rule 17): within its scope the name then denotes the binding, Rule 14
    already looking innermost first (`fn f(let net: net.Net) { net.
    connect(...) }` — the parameter's own type annotation is resolved
    before the parameter is in scope, so `net.Net` there still resolves
    to the prelude module, and only the body's `net.connect` sees the
    parameter). A generic parameter MAY NOT shadow a prelude name
    (type-level names stay unambiguous); every other case above — items,
    imports, other bindings, `Self` — keeps no exception. Bindings
    introduced together MUST be pairwise distinct: the parameters of one
    `params`, the generic parameters of one `generics`, the identifiers
    of one tuple `binding`, the `cparam`s of one closure, and all
    `"let" ident` bindings of one match-arm pattern (`(let x, let x)` is
    an error). A second `let x` in a block where an earlier `x` is still
    in scope is a violation. Two scopes that do not enclose one another
    MAY reuse a name (sibling blocks, successive loops, different match
    arms, different functions), and a name is free again once its scope
    has ended. Violation MUST be a compile error at the new binding
    naming the earlier declaration. Member names (Rule 27) and the
    non-names of Rule 23 are not bindings and never conflict with
    anything in scope.
19. **N0019** — `with arena a: T { ... }` and `with allocator a: T
    { ... }` introduce one binding `a`, in scope in the header type `T`
    and in the block (ch01 Rule 15 owns the use of `a` as a brand in
    type position, and its open question 3 the header case). It is a
    single binding under Rule 18.
20. **N0020** — The identifier in `scoped(p)` (ch07 `ret_type`) is
    looked up only among the parameters of the same `fn_sig`, not by
    Rule 14; anything else MUST be a compile error.
21. **N0021** — An `impl_decl` introduces no name: it is never a `use`
    target and never in a scope. Orphan rule: resolve (Rule 16) the head
    path of the trait (the type before `for`) and of the implementing
    type (the type after `for`, or the only type), through re-exports,
    to their items. `impl Tr for T` MUST appear in the module defining
    `Tr` or, when `T`'s `type_core` is a `type_app` whose path reaches a
    `struct` or `enum` item, the module defining that item. An inherent
    `impl T` MUST appear in the module defining `T`'s item. Prelude
    types are defined in package `std`; a tuple, `fn`, `dyn` or
    generic-parameter type has no defining module. Violation MUST be a
    compile error naming the permitted module(s). Overlap between impls
    is the checker's.
22. **N0022** — Deferred to the checker, because each needs a type:
    every deferred segment of Rule 16; every postfix `.name` whose
    operand is not a `path` continuation (`f().x`, `a[i].x`, `x?.y`);
    method names and receiver dispatch; a Bracket's index-or-instantiate
    reading; the field names of `finit` and `fpat`; the labels of named
    arguments; the variant named by a `dot_lit`; associated items
    reached through a generic parameter, `Self`, a struct, a trait or a
    prelude type; whether a name reached in a pattern (Rule 25) is a
    legal constant or constructor; and enforcement of Rule 11. The
    checker MUST NOT perform scope lookup of its own: the only names it
    resolves are member names, in the tables of Rule 27 selected by a
    type.
23. **N0023** — The following identifiers are not names: they are never
    looked up, never bind, and never conflict with a scope. Capability
    words in `needs { }` (ch04); `inputs` strings; the `contracts:`
    `dot_lit`; attribute names, `attr_arg` labels, and `attr_arg` `path`
    values (interpreted by the chapter owning the attribute); an
    `asm_expr`'s architecture identifier and the register identifiers of
    its `in`/`out`/`clobber` items (ch04 Rules 24-25; the `expr` of an
    `in` item is an ordinary expression); named-argument labels; `finit`
    and `fpat` field names; postfix `.name`; `dot_lit`s; numeric
    suffixes; the `extern` ABI string; every segment of a `module`
    header and of a `use` path (Rule 3). `needs { clock };` does not
    bind `clock`.
24. **N0024** — File names. Every directory segment and the file stem of
    a source file's path relative to its source root MUST match
    `[a-z_][a-z0-9_]*`, MUST NOT be `_`, and MUST NOT be a reserved word
    of ch07; a `.fors` file violating this MUST be a build error naming
    the file. Module names are therefore lowercase, and no two files of
    one source root can differ only in case. The compiler MUST find
    modules by enumerating each source root and comparing names
    byte-for-byte; it MUST NOT test for a module by opening a path built
    from a `use`, so `use Foo;` never finds `foo.fors` on a
    case-insensitive file system. Two files of the universe that map to
    one module name MUST be a build error naming both. A file `a.fors`
    and a directory `a/` may coexist (modules `a` and `a.b`).
25. **N0025** — Patterns. A `binding` (`let`/`var`, `for`) always
    introduces bindings; `_` introduces none. Inside a `pattern`, the
    ONLY way to introduce a binding is `"let" ident` — directly as a
    `pattern` alternative, or as the `fpat` form `"let" ident` inside a
    `payload`'s `{ }`. A one-segment `path` with no `payload` is ALWAYS a
    reference, looked up by Rule 14, never a binding: resolving to a
    module-scope entity — a `const`, a unit `enum` variant, or a prelude
    value (e.g. `none`) — is fine for this chapter (whether the entity is
    a legal constant to compare against is the checker's, Rule 22; a
    unit variant is in practice reached by a `dot_lit` or a two-segment
    path, since Rule 4 never imports a variant; a name that resolves to a
    module is Rule 16's path-ends-on-a-module error, N0016); resolving to a local binding, a
    parameter or a generic parameter MUST be a compile error, N0025 (a
    pattern compares against compile-time entities only, so naming a
    run-time binding there is meaningless, not a fresh binding as it
    would once have been); not resolving at all MUST be the ordinary
    unresolved-name error, N0014, whose message adds the hint `to bind,
    write "let n"`. A `path` with a `payload`, or of two or more
    segments, is always a reference resolved by Rule 16 and never binds.
    An `fpat` `x: p` uses `x` as a field name only and never binds it
    itself (whatever binding `p` performs is `p`'s); the `fpat` form
    `"let" x` uses `x` as both the field name and the bound name — it is
    shorthand for `x: let x` (no parentheses: `(let x)` would be a
    one-element tuple pattern). Rule 18's pairwise-distinct and
    no-shadowing requirements apply to every `"let" ident` binding of a
    pattern exactly as they apply to any other binding. Literals and
    `dot_lit`s involve no name. `"var" ident` is not a `pattern` or
    `fpat` alternative (ch07): patterns never introduce a mutable
    binding.
26. **N0026** — Scope of each binding. A `gparam`: the whole
    declaration that carries the `generics` — the other bounds of the
    list, parameters, `ret_type`, `raises` type, contracts, fields,
    variants, body; for an `impl`, the header types and every method. A
    method's generic parameters are subject to Rule 18 against those of
    its `impl`/`trait`. `Self`: an implicit binding, behaving as a
    generic parameter, of every `trait_decl` and `impl_decl`, in scope
    between its braces. A `param`: the type annotations of the parameters
    that FOLLOW it in the same `params`, the `ret_type`, `raises` type
    and contracts of the `fn_sig`, and the body — NOT its own type
    annotation and not those of earlier parameters (parameters come into
    scope left to right, like `let` statements; so in `fn f(let net:
    net.Net, let peer: net.Addr)` the first `net.Net` is the prelude
    module's and the second `net` is the parameter, Rule 18, and a
    parameter used as a brand in another parameter's type must precede
    it); any further name a contract clause may see is ch02's. The
    pairwise-distinct requirement of Rule 18 covers the whole `params`
    list regardless of this order. A `let`/`var`
    binding: from the end of its statement to the end of the enclosing
    block, so not in its own initialiser. A `for`, `parallel for` or
    `simd for` binding: the loop block only, not the iterable or `grain`
    expression. A `with` identifier: Rule 19. A `cparam`: the closure
    body only. A `handler` identifier: the handler block only. Pattern
    bindings: the arm's body only. A struct-level `invariant` and a
    `const` initialiser see generic parameters (if any) and module scope.
    `comptime`, `parallel`, attribute and plain blocks are ordinary
    nested block scopes. A `"let" ident` pattern binding (directly or as
    the `fpat` form) is a pattern binding for this purpose, whatever
    payload depth it occurs at.
27. **N0027** — Member tables. Within one `struct_decl` the field names,
    within one struct-form `evariant` its field names, within one
    `enum_decl` the variant names, within one `trait_decl` the method
    names, and within one `impl_decl` the method names MUST be pairwise
    distinct, else a compile error at the second naming the first.
    Duplicates across different `impl` blocks of one type, and a method
    sharing a name with a field or variant, are the checker's.

## Examples

```fors
// manifest-less build, file hello.fors
module hello;
needs { io.stdout };

fn main(inout out: io.Stdout) raises io.Error {   // io: prelude module, Rule 17
    out.write_line(greeting())?;   // greeting is below: Rule 9
}

fn greeting() -> Str { return "hi"; }
```

```fors
// package app, file greet.fors
module app.greet;

pub fn hi() -> Str { return "hi"; }
```
```fors
// package app, file start.fors
module app.start;
needs { io.stdout };
use app.greet;                     // binds the module name `greet`, Rule 4(a)

fn main(inout out: io.Stdout) raises io.Error {
    out.write_line(greet.hi())?;   // module, then pub item: Rule 16
}
```

```fors
// package lib, file inner.fors
module lib.inner;

pub struct Point { pub x: i32, pub y: i32 }
```
```fors
// package lib, file api.fors
module lib.api;
pub use lib.inner.Point;           // re-export of an item, Rule 5
```
```fors
// package app2, file start.fors
module app2.start;
use lib.api.Point;                 // Rule 4(b), through the re-export

fn origin() -> Point { return Point { x: 0, y: 0 }; }
```

```fors
module demo;

const LIMIT: i32 = 10;

fn classify(let n: i32) -> i32 {
    match n {
        LIMIT => 1,                // resolves to a const: reference, Rule 25
        let other => other,        // "let" binds: fresh binding, Rule 25
    }
}

fn f() {
    with arena a: Arena {
        var v: Own[i32, a] = Own.alloc(a, 1);   // `a` in type position, Rule 19;
        discard v;                              // `.alloc` is deferred, Rule 16
    }
}
```

```fors
// aliasing: D2, Rules 3-6
module app.util;

pub struct Net { pub host: Str }
```
```fors
module app.start;
use app.util.Net as N;             // binds `N`, not `util`; Rule 4

fn f() -> N { return N { host: "x" }; }   // N.host is a deferred segment, Rule 16
```

```fors
// local shadowing a prelude name: D3, Rule 18
module app.io_demo;

fn f(let net: net.Net) {   // type annotation resolved before `net` is in scope
    net.connect();          // here `net` denotes the parameter, Rule 14
}
```

## Rejected alternatives

- Glob imports and brace groups: no ch07 production; a design-doc sketch
  predates the frozen grammar. Import aliases (`use a as b;`) were
  rejected in the first draft for this reason too but are now in the
  grammar (owner decision 2026-09-19, round 3, D2; Rules 3-6); before
  that, a name clash between two imports of same-named modules had to be
  solved by importing the modules and writing `a.tag`, `b.tag`.
- Shadowing (Rust/C style): rejected for Zig-style no-shadowing (Rule 18).
- Items outranking the prelude, and lazy (use-site) import ambiguity: both
  were in the first draft. With order-independent items they make the
  meaning of a name depend on a declaration anywhere in the file, and a
  `pub use` of an ambiguous name has no meaning for importers. Replaced by
  "each module-scope name has exactly one meaning" (Rules 13, 15).
- Fully qualified paths without `use` (`std.math.sqrt(x)` in a body): the
  edge set would depend on bodies; ch04's graph check wants headers only.
- A separate namespace for types, values or modules: would make
  `x.y` in an expression need kind information to pick a namespace.
- Package-level (`export`) visibility: no third visibility keyword exists
  in ch07; deferred.
- Relative `use` paths: a `use` would then depend on the importing file's
  location and on scope.

## Drafting decisions

- Superseded for prelude names by round 3 (D3, below): No-shadowing
  (Rule 18) was total: bindings could not reuse a local,
  parameter, generic parameter, item, import or prelude name. Cost the
  owner was asked to weigh: `io fs net proc time rand env gpu`, `some`, `none`
  and `reduce` are unusable as local names in every module. ch04's
  `fetch` example named a parameter `net` and was renamed to `conn`.
- Verifier: prelude modules (Rule 17) exist because 32 corpus tests and
  ch04's examples write `io.Stdout`, `io.Error` with no `use`. The
  alternative is to require `use std.io;` and fix those files.
- Verifier: `use` binds a module or an item, by the longest-module rule
  of Rule 4; the first draft's examples used an imported module's items
  unqualified, which no rule allowed. A module/item tie is an error.
- Verifier: import-versus-import, import-versus-item and
  item-versus-prelude clashes are all eager errors (Rules 13, 15),
  overturning the draft's lazy ambiguity and item-outranks-prelude.
- Verifier: fields are private unless `pub` (the draft contradicted
  ch07's `field` production and its own test); variant payloads follow
  the enum; trait-impl methods follow the trait (Rule 11).
- Superseded by round 3 (D1): a one-segment pattern used to be a
  reference iff it resolves to a module-scope name, else a fresh
  binding (Rule 25) — so a misspelt constant silently became a
  catch-all binding, guarded only by an (unwritten) unused-binding lint.
  Round 3 closes that hole: a bare one-segment pattern name is now
  always a reference (module-scope entity, or N0025/N0014 error); the
  only way to bind in a pattern is `"let" ident`.
- Owner decision 2026-09-19, round 3 (D1) — Closed by owner decision: a
  pattern binds a name only via `"let" ident`; the old implicit
  bind-if-unresolved rule and the bare `fpat` shorthand are both removed.
  `"var" ident` is deliberately not a pattern form: mutable pattern
  bindings are a separate, still-open question (see Open questions),
  and this draft's recommendation there is "no" — a pattern binding that
  needs mutation can be copied into a `var` in the arm body.
- Owner decision 2026-09-19, round 3 (D2) — Closed by owner decision:
  import aliases (`use p as c;` / `pub use p as c;`) bind the alias `c`
  only; `b`, in `use a.b as c;`, stays unbound; the module-graph edge
  (Rule 7) is computed from the path, not the alias, so aliasing does
  not change what the build graph looks like. `"as" "_"` and aliasing to
  a prelude name are both errors, by the same reasoning as the
  unaliased cases (Rules 3-6, 13).
- Owner decision 2026-09-19, round 3 (D3) — Closed by owner decision: a
  function-local binding (not a generic parameter, not a module-scope
  item or import) may shadow a prelude name; Rule 14's innermost-first
  lookup already makes this unambiguous. Generic parameters keep no
  exception, so type-level names stay unambiguous everywhere a type can
  appear. This is the only carve-out in Rule 18's total no-shadowing;
  everything else (items, imports, other bindings, `Self`) is unchanged.
- Round 3 verifier (D3): Rule 26 used to put a parameter in scope over
  the entire `fn_sig`, its own type annotation included, which
  contradicts D3's `fn f(let net: net.Net)`. Parameters now come into
  scope left to right (own and earlier annotations excluded). Cost: a
  brand parameter must be declared before the parameter whose type
  names it; no spec example or corpus test did otherwise.
- Round 3 verifier (D2): `as _` is a ch07 parse error, not a ch08 check
  error (`_` is not an `ident`); `let _` in a pattern likewise.
- Verifier: the root module is the build's choice (ch04 Rule 8), not
  "whichever module declares `main`"; all root-package modules are
  resolved (Rule 2).
- Verifier: lowercase-only file names (Rule 24) turn the design doc's
  naming lint into a hard rule, which is what makes the mapping
  deterministic on case-insensitive file systems.
- `Self` is an implicit binding (Rule 26); no earlier chapter defines it.
- Diagnostic codes `N00xx` equal the rule numbers; tests cite `08.Rk`.

## Open questions for the owner

1. Prelude contents (Rule 17). Used unqualified elsewhere but defined
   nowhere, so currently unresolved names: `Buffer` (ch04 example, 5
   tests), `Vec`, `PageAllocator`, `Copyable`. Add to the prelude, or
   require `use`? And confirm prelude modules versus mandatory
   `use std.io;`.
2. ~~Confirm total no-shadowing including prelude names (Decision 1).~~
   Closed by owner decision 2026-09-19, round 3 (D3): total no-shadowing
   stays for items, imports, other bindings and `Self`; a function-local
   binding may shadow a prelude name (Rule 18); a generic parameter may
   not.
3. ch04 should define the manifest's package name and source root; Rule 1
   assumes both.
4. Package-level visibility and globs: schedule before v1.0? Aliases are
   closed (owner decision 2026-09-19, round 3, D2; Rules 3-6): two
   same-named modules (`a.util`, `b.util`) can now both be imported, as
   `use a.util as autil; use b.util as butil;`.
5. Should a variant and an inherent associated function of the same name
   be an error (Rule 16 currently lets the variant win; Rule 27 leaves
   the clash to the checker)?
6. Mutable pattern bindings (`"var" ident` in a pattern): left open by
   round 3's D1, which recommends "no" — a pattern binding is always by
   `let`, and code needing to mutate it copies into a local `var` in the
   arm body. Confirm, or add a `"var" ident` pattern/`fpat` alternative.

## Conformance tests

All in `tests/conformance/08-names/`; each cites its rule as `08.Rk`.
R1 `module-header-match-accepted`, `module-header-mismatch-rejected`,
`module-name-from-directory-accepted`; R4 `use-module-then-item-path-
accepted`, `use-item-accepted`, `use-unresolved-rejected`,
`use-module-item-tie-rejected`, `use-variant-rejected`,
`private-item-cross-module-rejected`; R3 `use-multiple-paths-accepted`;
R5 `pub-use-reexport-accepted`, `pub-use-module-reexport-accepted`;
R6 `import-not-transitive-rejected`; R7 `import-cycle-2`,
`import-cycle-3`, `import-diamond-accepted`; R8 `self-import-rejected`,
`self-import-item-rejected`; R9 `order-independent-items-accepted`,
`use-before-let-rejected`, `let-initialiser-self-reference-rejected`;
R10 `private-item-via-module-path-rejected`; R11 `private-field-cross-
module-rejected`, `pub-on-variant-field-rejected`, `pub-in-trait-impl-
rejected`; R12 `private-type-in-public-signature-rejected`,
`private-type-in-private-field-accepted`; R13 `duplicate-fn-rejected`,
`struct-fn-same-name-rejected`, `item-named-as-prelude-rejected`,
`import-collides-with-item-rejected`, `import-same-entity-twice-
accepted`, `use-std-io-beside-prelude-accepted`; R14 `unresolved-name-
rejected`; R15 `ambiguous-import-rejected`, `ambiguous-import-unused-
rejected`; R16 `path-ends-on-module-rejected`, `enum-variant-path-
accepted`, `unimported-module-path-rejected`; R17 `prelude-usable-
without-use-accepted`, `prelude-module-without-use-accepted`; R18
`shadow-{local,param,gparam,for,closure-param,else-handler,with-
arena,item,later-item,import}-rejected` (round 3, D3: `shadow-pattern-
rejected` moved to R25 below; `shadow-prelude-rejected` and
`shadow-prelude-module-rejected` flip to `local-shadows-prelude-{type,
module}-accepted` under R18 — a function-local binding may now shadow a
prelude name),
`duplicate-param-rejected`, `duplicate-gparam-rejected`, `pattern-let-
duplicate-in-one-pattern-rejected` (renamed from round 2's
`duplicate-in-one-pattern-rejected`; D1 rewrites it with `let`),
`duplicate-in-tuple-binding-rejected`,
`redeclare-in-same-block-rejected`, `gparam-named-as-item-rejected`,
`method-gparam-shadows-impl-gparam-rejected`, `sibling-scopes-reuse-
accepted`; R19 `with-arena-brand-type-accepted`; R20 `scoped-parameter-
accepted`, `scoped-non-parameter-rejected`; R21 `impl-in-third-module-
rejected`, `impl-in-trait-module-accepted`; R23 `capability-word-not-a-
name-accepted`, `non-names-do-not-collide-accepted`; R25 `pattern-const-
reference-accepted`, `pattern-let-fresh-binding-accepted` (renamed from
round 2's `pattern-fresh-binding-accepted`; D1 rewrites it with `let`),
`pattern-names-local-rejected`, `shadow-pattern-rejected` (both moved
here from R18: a bare pattern name resolving to a local/parameter is
N0025 directly, round 3, D1); R26 `for-binding-not-in-iterable-rejected`, `self-type-
in-impl-accepted`, `self-type-outside-impl-rejected`, `handler-binding-
scope-rejected`; R27 `duplicate-field-rejected`, `duplicate-variant-
rejected`, `duplicate-method-in-impl-rejected`. Added by the resolver review (adversarial, same format): R4 `use-module-
beside-directory-accepted`, `use-module-private-item-no-tie-accepted`,
`use-module-reexport-tie-rejected`, `use-unresolved-used-many-times-
rejected`; R12 `private-type-in-pub-{enum-payload,trait-method,const,
method}-rejected`, `private-type-in-private-positions-accepted`; R13
`item-named-as-prelude-module-rejected`; R16 `private-import-via-module-
path-rejected`, `enum-variant-via-reexport-accepted`, `path-ends-on-
prelude-module-rejected`, `prelude-module-backed-by-std-rejected`; R17
`prelude-module-backed-by-std-accepted`; R18
`shadow-in-closure-body-rejected`, `shadow-nested-closure-
rejected`, `shadow-deeply-nested-block-rejected`, `duplicate-cparam-
rejected`, `with-brand-nested-same-name-rejected`, `name-free-after-scope-
ends-accepted`; R19 `with-brand-in-closure-type-accepted`; R21 `impl-
inherent-foreign-type-rejected`, `impl-type-argument-does-not-count-
rejected`, `impl-foreign-trait-for-prelude-type-rejected`, `impl-own-
trait-for-generic-type-accepted`; R22 `checker-questions-not-diagnosed-
accepted`; R25 `pattern-misspelt-const-binds-N0014-rejected` (renamed
from, and flips, round-2's `pattern-misspelt-const-binds-accepted`: a
misspelt constant in a bare pattern position is now N0014, not a fresh
binding — round 3, D1), `pattern-prelude-
value-reference-accepted`; R26 `with-brand-out-of-scope-rejected`, `self-
in-impl-header-rejected`, `gparam-visible-in-sibling-bound-accepted`; R27
`duplicate-trait-method-rejected`, `duplicate-variant-field-rejected`,
`same-method-in-two-impls-accepted`. Rules 2 and 24 have no corpus test:
they need a manifest or an illegal file name, which the corpus format
cannot carry.

Added by owner decision 2026-09-19, round 3 (D1/D2/D3; new tests, this
round; `local-shadows-prelude-{type,module}-accepted` and
`pattern-{let-fresh-binding,let-duplicate-in-one-pattern,misspelt-const-
binds-N0014}-...` above are the flipped/renamed round-2 tests, listed at
their rule already): R18 `local-shadows-prelude-value-accepted`,
`gparam-shadows-prelude-rejected` (item-vs-prelude is still rejected —
see round 2's `item-named-as-prelude-rejected` at R13, unchanged); R25
`pattern-let-shadows-outer-local-rejected`, `pattern-unresolved-hint-
mentions-let-rejected`, `fpat-let-binds-field-accepted` (the successor
to round 2's now-removed `fpat-shorthand-shadow-rejected`, whose
bare-`fpat`-shorthand premise no longer parses — the parse error is
ch07's `pattern_bare_shorthand_removed`); R3-R6 `use-alias-binds-alias-
not-source-accepted`, `use-alias-collision-rejected`, `use-alias-of-
module-as-path-head-accepted`; R5 `pub-use-alias-reexport-seen-from-
third-module-accepted`; R13/R15 `use-alias-same-entity-twice-accepted`.

Added by the round-3 verifier (adversarial, same format): R4
`pub-use-alias-hides-source-name-rejected`; R5 `pub-use-alias-then-
realias-to-original-accepted`; R7 `pub-use-alias-cycle-rejected` (one
diagnostic: the follow-on Rule 4 error is suppressed); R13
`use-alias-spelling-original-name-accepted`, `use-alias-to-prelude-name-
rejected`; R14 `use-alias-source-name-unbound-rejected`; R15
`use-alias-collides-with-unaliased-import-rejected`; R16
`pattern-names-module-rejected`; R18 `local-shadows-prelude-module-path-
head-accepted`, `closure-param-shadows-prelude-accepted`,
`pattern-let-named-as-prelude-value-accepted`, `gparam-named-as-prelude-
type-rejected`, `pattern-let-shadows-item-rejected`, `pattern-let-duplicate-across-
nested-payload-rejected`; R25
`pattern-variant-through-alias-accepted`, `pattern-let-nested-tuple-in-
payload-accepted`, `pattern-bare-name-of-shadowing-local-rejected`; R26
`param-named-as-prelude-type-own-annotation-accepted`,
`param-in-scope-in-later-param-type-accepted`, `param-not-in-scope-in-
earlier-param-type-rejected`, `pattern-let-binding-not-in-sibling-arm-
rejected`.
