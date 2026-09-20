# Chapter 8: Modules, names and visibility

## Status

Draft, 2026-09-19; verified and repaired the same day, then round-5 owner
decisions applied (see Drafting decisions — "Closed by owner decision
2026-09-19, round 5"). Name resolution is a phase of its own: it runs after parsing
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
  dependency (ch04 Rule 17), and of package `std`, which every build has
  — as source once `std` ships, and until then as Rule 17's synthetic
  table of module names.
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
7. **N0007** — The module graph has one edge per `use` path, and NO other
   edge: to the module itself in Rule 4(a), to `M` in Rule 4(b). The edge
   set is therefore exactly the explicit `use` edges of the file headers
   — there is no implicit edge of any kind, no body scan, and no
   over-approximation (owner decision 2026-09-19, round 5, D3: the
   imports-first property is that a file's dependencies are readable from
   its header without parsing its body, so every dependency must be
   written there). Which prefix of a `use` path is a module depends
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
    methods and associated types are exactly as visible as the trait
    (an `assoc_type_def` in an impl likewise; ch07 gives neither form a
    `pub`). A method in an inherent
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
    bounds, every method signature and the bounds of every associated
    type; for a `const`, its type; the signature of every `pub` method in
    an `impl` whose type is `pub`; and, in an impl of a `pub` trait for a
    `pub` type, the right-hand side of every `type A = T;`. The bounds of
    a constraint entry (Rule 26) count as `gparam` bounds.
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
    the same std module imported twice) is not a collision. No
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
    compile error, and a module is reachable ONLY through a name bound
    by `use` (`a.b.f` needs `use a.b;` and is then written `b.f`;
    `io.Stdout` needs `use std.io;` — round 5, D3: the prelude binds no
    module). A module bound by a `use` of the synthetic `std` table
    (Rule 17) has no known names, so every segment after it is deferred.
    **enum item** — if the next segment is one of the
    enum's variants (Rule 27) it reaches that variant; otherwise it is a
    deferred segment. **anything else** (struct, trait, `fn`, `const`,
    prelude type or value, generic parameter, `Self`, variant, local,
    parameter) — every remaining segment is deferred. A **deferred
    segment** is a field, method, associated-function or associated-type
    name: this phase records it unresolved and the checker resolves it by
    type (Rule 22). In particular a type path headed by a generic
    parameter or `Self` — the projection `I.Item`, `Self.Item` (ch09 Rule
    61), also as the subject of a constraint entry — has its head
    resolved here and its second segment deferred: this phase never asks
    which trait declares `Item`, nor whether the head is a *type*
    parameter. The algorithm is identical in type and expression
    position. Whether the entity finally reached is of a kind legal in
    its position (a type where a type is needed, a constant `targ`, a
    brand) is the checker's, since a bare `targ` path is classified
    there (ch07 Disambiguation 11).
17. **N0017** — The prelude is a closed list, present in every module
    scope, and it contains NO modules (owner decision 2026-09-19, round 5,
    D3). Types and traits: `i8 i16 i32 i64 u8 u16 u32 u64 isize usize
    f32 f64 bool Str Slice Array vector mask atomic rawptr Own Ref Arena
    Option Shared ErrorFrom never Range RangeIncl Copyable Eq Ord Add Sub
    Mul Div Rem Neg BitAnd BitOr BitXor Shl Shr Iterator Index IndexMut
    Allocator AllocError PageAllocator Buffer Vec Map String Utf8Error
    Linear Droppable`
    (the second line is round 4's addition: the names ch09 Rules 4, 5, 21
    and 23 make language-known; the third is the eight names std
    contributes, ch10 Rule 2, which closes Open question 1 — types and
    traits only, each defined in `std.mem` or a submodule of it, and each
    denoting the SAME item as its module path, `mem.Vec`, so the two
    spellings never collide under Rule 13; the fourth is round 6's two
    marker traits, ch01 Rules 22 and 22c, which are language-known like
    `Copyable` and `Shared` and belong to no module — a user item named
    `Linear` or `Droppable` is the ordinary N0013 collision, exactly as
    for `Iterator`).
    Values: `some none reduce`. No other name
    is available without `use`: in particular a std module — `io`, `fs`,
    `net` and the rest — is a name only in a module whose header imports
    it (`use std.io;`), and using such a name without importing it is the
    ordinary unresolved-name error of Rule 14, N0014, reported at the head
    segment (a diagnostic for a name in this rule's known list SHOULD name
    the missing import). There is no implicit edge (Rule 7) and no scan of
    any body.

    **The synthetic `std` table.** Package `std` is in every universe
    (Definitions) but no `std` source exists yet, so until it ships the
    compiler knows its module names and nothing else: `use std.<m>;` MUST
    resolve, for `m` one of

        io  fs  net  proc  time  rand  env  gpu  mem  ffi

    — `io fs net proc time rand env gpu` are the homes of ch04 Rule 21's
    root-capability types, `mem` the home of the explicit allocators of
    ch01 (round 5, D5), and `ffi` the module ch04's sealed-capability
    examples import (`use std.ffi;`). The `use` binds its last segment as a module name
    exactly as Rule 4(a) does, and every member access through it
    (`io.Stdout`, `fs.Dir`, `mem.Allocator`) is a deferred segment left to
    the checker (Rule 16, Rule 22), because this phase has no `std` items
    to look up. A `use std.<name>;` whose `name` is not in the list above
    MUST be a compile error with this rule's code, N0017, naming the
    known list; `use std;` alone is Rule 4(c)'s unresolved import
    (`std` is a package, not a module). A path deeper than a module
    (`use std.io.Writer;`) binds its last segment and is likewise left to
    the checker, with no diagnostic from this phase. Once `std` ships as
    source, its modules resolve like any other module of the universe and
    this table is not consulted: a build that contains `std` sources
    resolves `use std.<m>;` against them, and an absent `std.<m>` is then
    Rule 4(c)'s error. Nothing else about `std` is built in — no item, no
    trait, no capability.
18. **N0018** — No shadowing, with one exception. A binding MUST NOT
    have a name that Rule 14 would resolve at the point of the binding:
    a binding of an enclosing scope of the same function, a parameter, a
    generic parameter of the function or of its enclosing `trait`/
    `impl`, `Self`, or any module-scope name (item — including one
    declared textually later — import, or prelude name) — EXCEPT that a
    function-local binding (a `let`/`var` binding, a `for`/`parallel
    for`/`simd for` binding, a `param`, a `cparam`, a `"let" ident`
    pattern binding, or a `with arena`/`with allocator` identifier) MAY
    share a name with a prelude name (a prelude type or value, Rule 17):
    within its scope the name then denotes the binding, Rule 14
    already looking innermost first (`fn f(let usize: i32) -> i32 {
    return usize; }` — the parameter's own type annotation is resolved
    before the parameter is in scope, so a prelude name used there still
    means the prelude entity, and only the body sees the parameter).
    Since round 5 (D3) a std module is NOT a prelude name but an import,
    so this exception no longer covers one: in a module whose header says
    `use std.io;`, a binding named `io` shadows a module-scope name and is
    an error like any other import clash, while in a module that does not
    import it `io` is an ordinary free identifier.
    A generic parameter MAY NOT shadow a prelude name
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
    arguments; the variant named by a `dot_lit`; associated items —
    functions and associated types, so every projection (Rule 16) —
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
    bind `clock`. Not being a name is not a licence to spell one with a
    reserved word: ch07 still requires an `ident` token in each of these
    positions, so a field, member, label or `dot_lit` may not be called
    `type`, `spmd` or `kernel` (round 5, D2) — that is ch07's parse
    error, not this chapter's. A std module name (`io`, `mem`, ...) is
    an ordinary identifier and MAY be a member name (`c.io`, `s.mem`) in
    any module, imported or not, since a member name is never looked up
    in a scope.
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
    variants, body; for an `impl`, the header types, every `type A = T;`
    and every method; for a `trait`, every associated-type bound and
    method. A constraint entry (ch07 `gconstraint`, `I.Item: Add`)
    introduces NO name and has no scope of its own. Its head identifier
    is looked up by Rule 14 and MUST resolve to a generic parameter
    declared EARLIER (to its left) in the same `generics` list, to a
    generic parameter of the enclosing `impl`/`trait`, or to `Self`; any
    other entity, a parameter declared later in the list, or no hit MUST
    be a compile error with this rule's code, naming the head. (This is
    the one place where order inside a `generics` list matters: ordinary
    bounds still see every parameter of the list.) Its second identifier
    is a deferred segment (Rule 16) and the paths in its bounds resolve
    like those of any `gparam` bound. A
    method's generic parameters are subject to Rule 18 against those of
    its `impl`/`trait`. `Self`: an implicit binding, behaving as a
    generic parameter, of every `trait_decl` and `impl_decl`, in scope
    between its braces. A `param`: the type annotations of the parameters
    that FOLLOW it in the same `params`, the `ret_type`, `raises` type
    and contracts of the `fn_sig`, and the body — NOT its own type
    annotation and not those of earlier parameters (parameters come into
    scope left to right, like `let` statements; so in `fn f(let Option:
    Option[i32])` the annotation's `Option` is still the prelude type and
    only the body sees the parameter, Rule 18, and a parameter used as a
    brand in another parameter's type must precede it — `fn f(let a:
    Arena, let x: Own[i32, a])`); any further name a contract clause may
    see is ch02's. The
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
    `enum_decl` the variant names, within one `trait_decl` the names of
    its methods and associated types, and within one `impl_decl` the
    names of its methods and associated-type definitions MUST be pairwise
    distinct, else a compile error at the second naming the first.
    Methods and associated types share one table per trait and per impl:
    `type Item;` beside `fn Item()`, or `type A = X;` twice in one impl,
    is this error. Whether an impl defines exactly the associated types
    its trait declares is the checker's (ch09 Rule 17). Duplicates across
    different `impl` blocks of one type, and a method sharing a name with
    a field or variant, are the checker's (ch09 Rule 48).

## Examples

```fors
// manifest-less build, file hello.fors
module hello;
needs { io.stdout };
use std.io;                        // mandatory since round 5 (D3), Rule 17

fn main(inout out: io.Stdout) raises io.Error {   // io: the imported module
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
use std.io, app.greet;             // binds `io` (Rule 17) and `greet`, Rule 4(a)

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

fn f(let Option: Option[i32]) -> i32 {  // annotation resolved before `Option`
    match Option { some(let v) => v, none => 0 }   // the parameter, Rule 14
}
```
```fors
// round 5, D3: a std module is an import, never a prelude name
module app.net_demo;
use std.net;

fn f(inout c: net.Conn) { }   // `net` is the imported module, Rule 16
// `let net = 1;` in this module would be N0018 (it shadows the import);
// in a module without `use std.net;` it is an ordinary free name, and
// `net.Conn` there is N0014 with a "add `use std.net;`" hint (Rule 17).
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
- Superseded by round 5 (D3, below): prelude modules (Rule 17) existed
  because 32 corpus tests and ch04's examples wrote `io.Stdout`,
  `io.Error` with no `use`. The alternative — require `use std.io;` and
  fix those files — is what the owner chose.
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
- Round 4 (2026-09-19; associated types, ch09 Rules 16-20, 61-62): the
  prelude gains the language-known names (Rule 17), which also settles
  `Copyable` from open question 1; associated types join the member
  tables (Rule 27), the deferred segments (Rules 16, 22), the visibility
  and signature rules (Rules 11-12); a constraint entry's head must be
  an earlier parameter (Rule 26) — the resolver owns that test because
  it is positional and needs no type, while "is it a *type* parameter
  with a bound declaring that name" is ch09 Rule 61's. `type` is now
  reserved (ch07), so Rule 24 already forbids a module named `type`.
- Diagnostic codes `N00xx` equal the rule numbers; tests cite `08.Rk`.

### Closed by owner decision 2026-09-19, round 5

- **D3 — std modules require an import.** The owner chose mandatory
  `use std.io;` over prelude modules, for the plan's imports-first
  property: a file's dependencies MUST be readable from its header
  without parsing its body. Consequences, all applied above: the prelude
  keeps only types, values and traits and NO modules (Rule 17); the
  module graph is exactly the explicit `use` edges, with no implicit
  edge, no body scan and no over-approximation (Rule 7 — the deleted
  sentence "an extra edge to a std module is harmless" was the only
  place in the spec where the edge set was allowed to be inexact); a
  module is reachable only through a `use` (Rule 14/16); using a std
  module without importing it is N0014 at the head segment (Rule 17),
  with a hint naming the missing import; and `std` is a known package
  whose module names the compiler carries as a synthetic table until
  `std` ships, with `use std.<unknown>;` an N0017 error naming the list
  (Rule 17). Costs accepted with the decision: 37 corpus files and four
  example blocks of ch02/ch04/ch08 gained a `use std.<m>;` line (a file
  that only NAMES a capability in `needs { io.stdout }` needs no import,
  so the count is lower than the count of files mentioning `io`); a
  local named `io` is now an error in a module that imports `std.io` (it
  shadows an import — Rule 18's prelude carve-out no longer covers a std
  module), which flipped two corpus tests, renamed and re-aimed four
  more (one of them ch09's) and deleted one whose premise is now
  impossible; and the resolver's weakest component, a whole-file token
  scan that manufactured the implicit edges (it also saw `needs` words
  and shadowed locals), is deleted rather than repaired.
- **D3 drafting decision (not in the owner's answer).** The synthetic
  table is consulted only while `std` has NOT shipped: a build that
  contains `std` sources resolves `use std.<m>;` against them, so an
  absent `std.<m>` in such a build is Rule 4(c)'s error rather than a
  silently synthesised module. Two further gaps the answer left open,
  decided here: `use std;` alone is Rule 4(c)'s unresolved import
  (`std` is a package, not a module), and a path deeper than a module
  (`use std.io.Writer;`) binds its last segment with no diagnostic,
  since this phase has no `std` items to check it against. `mem` is in
  the known list because round 5's D5 puts the explicit allocators
  there; ch04's root-capability homes supply the other eight.
- **D1 — receiver shorthand.** `inout self` means `inout self: Self`
  (ch07 Disambiguation 21). For this chapter nothing changes: the
  shorthand introduces the same binding `self` under Rules 18 and 26, and
  a parameter with no type annotation simply has no annotation to
  resolve.
- **D2 — `spmd`/`kernel` reserved.** Rule 24 already forbids a module
  named with a reserved word, so both are now illegal file/directory
  names; Rule 23 gains the sentence that "not a name" does not let a
  member, field or label be spelled with a reserved word.

## Open questions for the owner

1. ~~Prelude contents (Rule 17): `Buffer`, `Vec`, `PageAllocator` used
   unqualified but defined nowhere.~~ CLOSED by ch10 (2026-09-20, the std
   surface chapter, Rule 2): all three go INTO the prelude, together with
   `Allocator`, `AllocError`, `Map`, `String` and `Utf8Error` — eight
   names, all defined in `std.mem` or a submodule of it. The deciding
   argument is that every site using them today is a module with no header
   imports, so requiring `use std.mem;` would turn accepted tests into
   defects for no gain. ~~And confirm prelude modules versus mandatory
   `use std.io;`.~~ The module half was closed by owner decision
   2026-09-19, round 5 (D3): mandatory `use std.io;`, no prelude modules,
   a synthetic `std` table until `std` ships (which ch10 Rule 1 leaves
   unchanged: std adds no eleventh module).
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
5. ~~Should a variant and an inherent associated function of the same
   name be an error?~~ Closed, round 4 (2026-09-19, drafting default
   taken with the ch09 decisions): it is an error, ch09 Rule 48, so Rule
   16's variant-first reading never decides an accepted program.
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
accepted`, `use-std-module-accepted` (round 5, D3: renamed from
`use-std-io-beside-prelude-accepted`, whose "beside the prelude's `io`"
premise is gone); R14 `unresolved-name-rejected`; R15 `ambiguous-import-rejected`, `ambiguous-import-unused-
rejected`; R16 `path-ends-on-module-rejected`, `enum-variant-path-
accepted`, `unimported-module-path-rejected`; R17 `prelude-usable-
without-use-accepted` (round 5, D3: round 2's `prelude-module-without-
use-accepted` FLIPS and is renamed `std-module-without-use-rejected`,
listed with the round-5 tests below); R18
`shadow-{local,param,gparam,for,closure-param,else-handler,with-
arena,item,later-item,import}-rejected` (round 3, D3: `shadow-pattern-
rejected` moved to R25 below; `shadow-prelude-rejected` and
`shadow-prelude-module-rejected` flip to `local-shadows-prelude-type-
accepted` and — round 5, D3 — `local-named-as-std-module-without-import-
accepted`, a function-local binding being free to shadow a prelude type
and free to take a std module's name in a module that does not import it),
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
`item-named-as-std-module-without-import-accepted` (round 5, D3: flips
and renames round 2's `item-named-as-prelude-module-rejected`); R16
`private-import-via-module-path-rejected`,
`enum-variant-via-reexport-accepted`, `path-ends-on-std-module-rejected`
(renamed, round 5), `use-std-module-backed-by-source-rejected` (renamed
from `prelude-module-backed-by-std-rejected`); R17
`use-std-module-backed-by-source-accepted` (likewise); R18
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

Added by round 4 (associated types): R16 `projection-second-segment-
deferred-accepted` (`I.Item` and `Self.Item` resolve with no N-error even
when no bound declares `Item`; that is ch09's T0061); R17 `prelude-
operator-traits-without-use-accepted`, `item-named-as-prelude-trait-
rejected` (an item named `Iterator` or `Add` is N0013, so the test cites Rule 13); R26 `constraint-
entry-head-earlier-param-accepted`, `constraint-entry-head-later-param-
rejected`, `constraint-entry-head-impl-param-accepted`, `constraint-
entry-head-self-accepted`, `constraint-entry-head-not-a-gparam-rejected`,
`constraint-entry-head-unresolved-rejected`; R27 `duplicate-assoc-type-in-
trait-rejected`, `duplicate-assoc-type-in-impl-rejected`, `assoc-type-
named-as-method-rejected`.

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
rejected`. Round 3's `local-shadows-prelude-module-path-head-accepted`
is gone: round 5's D3 makes its premise impossible (a parameter cannot
shadow an import), and it is replaced by
`param-shadows-imported-std-module-rejected` below.

Added by owner decision 2026-09-19, round 5 (D3; the flipped and renamed
round-2/round-3 tests are listed at their rule above): R17
`std-module-without-use-rejected` (`io.Stdout` with no `use std.io;` is
N0014 at the head segment) and one per known module name —
`std-module-without-use-{fs,net,proc,time,rand,env,gpu,mem,ffi}-rejected`;
`use-std-module-accepted` (`use std.io;` then `io.Stdout`, every member
access deferred), `use-std-mem-accepted` (the round-5 D5 name),
`use-std-unknown-module-rejected` (N0017, the message naming the known
list), `use-std-alone-rejected` (N0004: `std` is a package, not a
module), `use-std-item-path-accepted` (`use std.io.Writer;` binds
`Writer` and is left to the checker); R13
`item-named-as-std-module-with-import-rejected`; R18
`local-shadows-imported-std-module-rejected`,
`param-shadows-imported-std-module-rejected`; R16
`path-ends-on-std-module-rejected`.

Added by the round-5 verification (2026-09-20): R7
`body-mention-of-std-module-adds-no-edge-accepted` (a build with `std.io`
source whose `std.io` says `use main;` while `main`'s body spells `io.len`
on a local `io` and its header `needs { env };` — no edge, no cycle;
before D3 the body scan made this an N0007 cycle; the same fact is
asserted on the raw edge set in `crates/fors-index/tests/corpus.rs` and
across a body-vs-header edit in `crates/fors-resolve/tests/incremental.rs`);
R18 `closure-param-named-self-shadows-receiver-rejected` (`|self|` inside
a method is a `cparam` that shadows the receiver, N0018) and
`closure-param-named-self-in-free-fn-accepted` (ch07 Disambiguation 21
touches `param` only, never `cparam`). ch04's
`main-forged-std-module-rejected` and `main-aliased-std-import-accepted`
(ch04 Rule 8) rely on this chapter's Rule 4 binding: a `main` parameter
type's head is judged by what the header binds it to, so a user module
named `io` cannot forge `io.Stdout` and an alias `use std.io as w;` still
names it.
