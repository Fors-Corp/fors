# 10. The standard-library surface

## Status

Draft, M0.5, 2026-09-20; round-6 adversarial verification applied the
same day (Decisions 16-19: free-function adaptors, no by-value views of
non-`Copyable` payloads, an acyclic `std.mem` import graph, `contract`
trap kinds). Implements the owner decisions of 2026-09-19,
round 5, D5 (explicit allocator values, no ambient allocation, the root
heap as a `main` parameter, allocation is not authority) and settles the
type half of ch08 Open question 1 (`Buffer`, `Vec`, `PageAllocator`).
Normative; PLAN §4.2/§4.3 win over `docs/design/*`.

The language is frozen for v0.1. Every signature in this chapter is
derivable from ch07's grammar and typed by ch09's rules; where a signature
could not be written under the frozen language, this chapter says so and
either drops the operation (Rule 10's list) or records an open question —
it never proposes a language change.

## Scope

Owns: the std module list and what each module contains; the closed set of
prelude additions std contributes; the allocator interface and the
concrete allocators std ships; the core owning types (`Buffer`, `Vec`,
`Map`, `String`) and the borrowed views (`Str`, `Slice[T]`); the iterator
surface (adaptors and consumers, not the `Iterator` trait itself); the
operations each capability module unlocks and their failure behaviour;
what std exposes of concurrency; the rules std itself obeys; the v0.1
interface-stability promise.

Not owned, and only cited here: conventions, moves, brands, arenas,
`Own[T, A]`, `Shared`, scoped values (ch01); `raises`/`?`/traps (ch02);
integers, floats, `reduce`, array literals, `Slice[T]`'s origin (ch03);
capabilities, sealing, `main`'s parameters, the root-capability type list
(ch04); names, imports, the prelude's mechanism (ch08); traits, associated
types, coercions, member lookup, the two judgements (ch09).

## How to read the declarations

A block marked `fors` is literal source and parses under ch07 (every one in
this chapter is checked with `fors parse`). A block marked `fors-sig` is a
SIGNATURE LISTING — ch09 Rule 2's signature-only interface — because ch07's
`impl_item` requires a body, so a method's signature cannot appear alone
inside an `impl`. In a listing the `;` stands for the elided body; a `trait`
declaration inside one is literal source, since `trait_item` permits `;`.
Nothing about the meaning changes: a listed signature is as normative as a
parsed one, and `std/` holds the same signatures with placeholder bodies.

## Definitions

- **Std module**: one of the ten names in Rule 1. A std name is reachable
  only as a prelude name (Rule 2) or through `use std.<m>;` (ch08 Rule 17).
- **Defining module**: the module whose source declares an item. For a
  prelude name this is an implementation detail; the prelude name and the
  module path denote ONE item (ch08 Rule 13's same-entity case).
- **Total operation**: one declared without `raises` that reaches no trap
  condition of ch02 Rule 15. A total operation cannot fail.
- **Fallible operation**: one declared `raises E`.
- **Linear type**: a type `T` for which `lin(T)` is true (ch01 Rules 22,
  22a). Std DECLARES `impl Linear for ...` for exactly nine types:
  `Block[A]`, `Vec[T, A]`, `Map[K, V, A]`, `String[A]`, `fs.File`,
  `fs.Entries`, `net.Conn`, `net.Listener` and `proc.Child`; `Own[T, A]` is
  linear by language rule with no written impl (ch01 Rule 22). Every other
  std type is non-linear, and any user type that HOLDS one of these is
  linear by inference, with nothing to declare (ch01 Rule 22a(b)). Values
  of a linear type MUST be consumed on every path by a named `sink self`
  method — `deinit`, `deinit_empty`, `free`, `close`, `shutdown`, `wait` —
  or moved to a caller that consumes them; Rule 11 states std's half of the
  discipline and ch01 Rules 22-22i are the language rule.
- **Latching writer**: a writer whose per-write operations are total and
  whose first failure is recorded in the value, to be surfaced by `check`
  or `flush` (Rule 39).
- **Caller-buffer form**: an operation named `*_into` that writes into a
  `Slice` the caller owns and returns the byte or element count, so that it
  allocates nothing (Rule 5).

## Rules

### The shape of std

1. **S0001** — The std module list is closed for v0.1 and is exactly ch08
   Rule 17's ten names:

       io  fs  net  proc  time  rand  env  gpu  mem  ffi

   This chapter adds NO module: `crates/fors-resolve/src/prelude.rs`'s
   `STD_MODULES` is correct as it stands. Every std item is declared in one
   of these ten or in a submodule of one — `std.mem.alloc`, `std.mem.vec`,
   `std.mem.hashmap`, `std.mem.text`, `std.mem.seq` — and a submodule's
   public items MUST be re-exported ITEM-WISE by its parent (`pub use
   std.mem.vec.Vec;`, ch08 Rules 4(b) and 5; never `pub use std.mem.vec;`,
   which would re-export the submodule NAME), so that every user-facing
   name is either a prelude name (Rule 2) or a member of one of the ten
   (`mem.Allocator`, `mem.iter`, `io.Stdout`). The parent imports its
   submodules and NO submodule imports its parent (ch08 Rule 7's
   acyclicity): `std.mem.alloc` and `std.mem.seq` are leaves, and the
   containers import only those two. A submodule is a defining home only,
   this chapter names none in a signature, and a module outside package
   `std` MUST NOT import one (`use std.mem.vec;` is an error citing this
   rule): the ten names are the whole importable surface, so the submodule
   layout is not a compatibility promise (Rule 9). Every `use` path is
   absolute (ch08 Rule 3), inside std as outside: a std file writes
   `use std.io;`, never `use io;`.
2. **S0002** — Std contributes exactly eight names to ch08 Rule 17's
   prelude, all types or traits, no modules and no values:

   | Name | Kind | Defining module | Why it is in the prelude |
   |---|---|---|---|
   | `Allocator` | trait | `std.mem.alloc` | every allocating signature carries the bound `L: Allocator[A]` |
   | `AllocError` | enum | `std.mem.alloc` | the error type of every allocating operation, so of every wrapper a user writes |
   | `PageAllocator` | struct | `std.mem` | `with allocator heap: PageAllocator` in ch01's examples and 2 accepted tests, in modules with no import |
   | `Buffer` | struct | `std.mem` | `Buffer[u8]`/`Buffer[i64]` in ch02's and ch04's examples and 5 tests, in modules with no import |
   | `Vec` | struct | `std.mem.vec` | ch01's prose and 2 grammar tests, unqualified |
   | `Map` | struct | `std.mem.hashmap` | 1 grammar test, unqualified; the pair of `Vec` |
   | `String` | struct | `std.mem.text` | the owned half of the prelude's `Str`; asymmetry would be a defect |
   | `Utf8Error` | enum | `std.mem.text` | `Str`'s only failure mode; `Str` is already a prelude type, so its error must be nameable without an import |

   `Own`, `Ref`, `Arena`, `Option`, `Str`, `Slice`, `Array`, `Iterator`,
   `Index`, `IndexMut`, `Eq`, `Ord`, `Copyable`, `Shared`, `ErrorFrom`,
   `Range` and `RangeIncl` are already prelude names (ch08 Rule 17) and
   this chapter only gives them a surface. Every other std name needs its
   module's import. The prelude MUST NOT gain a std function or a std
   value: `some`, `none` and `reduce` remain its only values.
   **Defining modules of the language-known prelude types.** ch08 Rule 21
   says a prelude type is "defined in package `std`" and an inherent
   `impl` must appear in the defining module; this chapter nominates the
   module: `Str` → `std.mem.text`; `Own`, `Option`, `Array`, `Slice`,
   `bool` and every integer and float type → `std.mem`. An inherent
   `impl` of one of these anywhere else, in std or out, is ch08 Rule 21's
   error.
3. **S0003** — No std operation reads or writes anything outside the
   process, and no std operation allocates, except through a value the
   caller passed it: a capability value (ch04 Rule 21) for the outside
   world, an allocator value (Rule 12) for memory. A std signature with
   neither is a pure function of its arguments. The one carve-out is Rule
   50's `proc.hardware_threads`.
4. **S0004** — Receiver conventions in std are fixed by what the operation
   does, not by taste: `let self` iff it only reads the receiver;
   `inout self` iff it mutates the receiver in place; `sink self` iff it
   consumes the receiver, and then the method is named `deinit`, `free`,
   `close`, `finish`, `wait` or `into_*`. No std method takes `set self`.
   A `sink self` method moves its receiver implicitly at the call site
   (ch09 Rule 46, ch01 Rule 2's single exception), so `v.deinit(&heap);`
   ends `v`'s life with no marker.
5. **S0005** — Naming is a contract, not a style: `*_into` is the
   caller-buffer form and allocates nothing; `try_*` is the fallible
   sibling of a higher-order function (Rule 8); `*_or` is the total variant
   of a fallible or partial operation, taking the fallback as its last
   argument; `*_mut` returns an `inout`-derived view of the receiver;
   `*_raw` names an operation in the unsafe inventory (ch04 Rules 9-10).
   Functions and methods are `snake_case`, types `UpperCamel`, enum
   variants `snake_case`; no name is abbreviated except `len`, `cap`,
   `ptr`, `buf`, `fmt` and `nanos`.
6. **S0006** — Failure discipline. Every std operation is exactly one of:
   total (Rule 6a), fallible with ONE error type (Rule 6b), or partial
   (Rule 6c).
   6a. A total operation MUST NOT be able to fail. It MUST NOT trap except
   at ch02 Rule 15's conditions reached through its own arguments (an index
   out of range, an arithmetic overflow the caller's values caused, an
   arena generation mismatch).
   6b. A fallible operation declares `raises E` for exactly ONE `E`, and
   `E` is a closed enum of Rule 7's set. **Where two failure modes would
   meet in one operation, std SPLITS the operation** rather than joining
   the error types: validation and allocation are never one call
   (`Str.from_utf8` then `String.from_str`, never a `String.from_utf8`
   that raises both). This is a rule, not a preference: `raises` takes one
   type (ch02 Rule 1), and an `ErrorFrom` hop inside std would hide which
   mode fired.
   6c. A partial operation — one whose absent answer is not a failure and
   has no cause to report — returns `Option[T]` and is total
   (`Vec.pop`, `Map.get`, `env.Args.at`). `Option` MUST NOT be used to
   report a failure that has a cause, and a cause MUST NOT be reported by
   a sentinel value.
   6d. **A failed allocation is an error value, never a trap** (owner
   decision, round 5, D5): every allocating operation is fallible with
   `E = AllocError`. Std MUST NOT abort on allocation failure, and MUST NOT
   offer an "infallible allocation" variant.
7. **S0007** — The std error types are closed and there is at most one per
   module: `mem.AllocError` (prelude `AllocError`), `mem.Utf8Error`
   (prelude `Utf8Error`), `io.Error`, `fs.Error`, `net.Error`,
   `net.TimeoutError` (Rule 43's deadline operations only), `proc.Error`,
   `env.Error`, `gpu.Error`, `ffi.Error`. `time` and `rand` have none:
   every operation of theirs is total (Rules 45, 47). Every std error type
   is a closed enum, `Copyable`, allocation-free, with no payload larger
   than 16 bytes and no field that borrows. Std ships NO `ErrorFrom` impl
   between its own error types: a conversion is the caller's declaration
   (ch02 Rule 3).

       pub enum AllocError { out_of_memory, too_large, unsupported_align }
       pub enum Utf8Error  { invalid_sequence, not_a_boundary, incomplete }

8. **S0008** — There is no effect polymorphism (owner decision, round 4),
   so a callable parameter of a std function MUST NOT be declared `raises`.
   A higher-order std operation whose callable may fail is a SEPARATE
   `try_`-prefixed function that takes a `raises E` callable and is itself
   declared `raises E` with `E` a generic parameter of the function. The
   pure and the `try_` sibling MUST have the same name modulo the prefix
   and the same parameter order. The `try_` set std ships is closed:
   `try_fold`, `try_for_each`, `try_collect_into`, `try_sort_by`.
9. **S0009** — v0.1 interface stability. Std promises SOURCE compatibility
   only: within v0.1.x no declaration in this chapter is removed or
   narrowed, and additions are new names. Std promises NO binary ABI: no
   std type's size, alignment, layout or field order is stable, `pub`
   fields this chapter names excepted (`Buffer.len`, `Buffer.data`,
   `Layout.size`, `Layout.align`, `time.Instant.nanos`,
   `time.Wall.unix_nanos`, `time.Duration.nanos`, `fs.Meta`'s fields,
   `gpu.Info`'s fields). A build MUST recompile std from source with the
   program; there is no std dynamic library in v0.1. The only stable binary
   interfaces of the implementation remain ch02 Rule 4's failure ABI and
   `extern "c"`.
10. **S0010** — Not in v0.1. This list is closed; each entry names its
    reason, and nothing outside it is "coming later" by implication.
    (a) A default or global allocator, and any ambient allocation — owner
    decision D5. (b) A `Result[T, E]` type — errors travel as `raises`
    (ch02), and a second channel would let a callee choose. (c) Locks,
    channels, thread handles, atomics beyond ch01's `atomic[T]`, and any
    blocking synchronisation — Rule 50. (d) An iterator over `inout` data
    (`iter_mut`) — its `Item` would have to be a borrow, and `Iterator`'s
    `Item` is a plain associated type with no scope parameter (ch09 Rule
    21); mutate by index. (e) A consuming iterator for an allocator-backed
    container — the iterator would have to free the storage when the loop
    drops it (ch09 Rule 31) and it cannot hold the allocator (ch01 Rule
    15a); use `while` + `pop`, then `deinit`. (f) Dynamic format strings,
    `printf`-shaped formatting, and any reflection — Rule 39's typed
    writers cover v0.1's needs and a format string is a second, untyped
    type system. (g) Locales, collation, case mapping, time zones, and
    calendar arithmetic — Rule 56. (h) A `Path` type, relative-path
    traversal, `..`, absolute paths, symlink following, and an ambient
    current directory — Rule 41. (i) An HTTP client, TLS, `net.Client`
    and `get_into` (both appear in ch02's and ch04's examples; see the
    corpus defects) — they are libraries, not std. (j) Async, futures,
    coroutines and fibers as a library surface — ch02 Rule 8 knows fibers,
    the language owns `spawn`. (k) A `char` type and character literals —
    ch07 Open question 4; `Str` and `u32` scalar values instead. (l)
    Environment mutation (`setenv`) — process-global mutable state. (m)
    Process spawning beyond `proc.Exec.run`/`Child.wait` — no pipes, no
    signals, no `fork`. (n) GPU kernel launch and buffer management — the
    language owns `@device`/`kernel` (ch07 reserved). (o) Sorting that
    allocates, and any stable sort — Rule 31 ships an in-place unstable
    one. (p) A hash map with a randomised seed by default — Rule 25.
    (q) A container, array or inline buffer OF a linear element that can be
    iterated by value, and `Array`/`vector`/`Buffer` of a linear element at
    all — round 6 makes the last ill-formed (ch01 Rule 22b, ch09 Rule 11)
    and `Iterator`'s `Item: Droppable` forbids the first (ch09 Rule 21);
    empty such a container with `pop`/`remove` and release it with
    `deinit_empty` (Rule 11c). (r) `iter_mut`, a `chain` adaptor, a
    `collect` that invents its container, a `raises` callable in an
    adaptor, and any adaptor or consumer beyond Rules 34-35 — the two sets
    are closed. (s) Blanket impls, in std as in the language (ch09 Rule
    18): round 6 confirmed that iterator method chaining does not need
    them, so nothing in std is waiting on them.

### Memory

11. **S0011** — Linearity and leaks. The LANGUAGE rule is ch01 Rules
    22-22i (round 6, owner decision O1): the compiler MUST reject any path
    on which a value carrying an outstanding cleanup obligation leaves its
    scope unconsumed, with a diagnostic naming the value, its type, the
    scope and exit it escapes, and the method that would consume it (ch01
    Rule 22i). This chapter's half is only the list: which std types
    declare `impl Linear` (Definitions) and which operations consume them
    (`deinit`, `deinit_empty`, `free`, `close`, `shutdown`, `wait`, each a
    `sink self` receiver method, so the consuming call is written
    `v.deinit(&a)` and moves `v` implicitly — Rule 4, ch09 Rule 46). This
    is what makes "no destructors + explicit allocators"
    safe: the allocator is not reachable at scope exit, so the only place
    the storage can be returned is an explicit call. `discard x;` and
    `consume x;` MUST NOT satisfy the obligation for a linear type (ch01
    Rule 22d). The cleanup is WRITTEN ONCE, with `defer` or `errdefer`
    (ch01 Rules 23-23f): `defer v.deinit(&a);` immediately after
    `Vec.new()` discharges the obligation on every `?` path as well as on
    the normal one, and `errdefer v.deinit(&a);` discharges it on the error
    paths only, leaving `return move v;` free to hand the value on. Without
    those two words the discipline would demand the cleanup at every `?`,
    which is why round 6 added them together with linearity.
    11c. **Linear elements.** A container MUST NOT be able to drop an
    element it cannot name. Round 6 makes all three consequences STATIC and
    retires this rule's earlier runtime contract: (i) `Buffer[X, N]`,
    `Array[X, N]` and `vector[X, N]` with a linear `X` are ILL-FORMED
    (ch09 Rule 11, ch01 Rule 22b) — an element could leave one only by a
    partial move, which ch01 Rule 4a(c) forbids; (ii) the operations that
    DROP elements — `Vec.clear`, `Vec.deinit`, `Map.clear`, `Map.deinit`,
    `Buffer.clear` — are declared in `T: Droppable` (for `Map`, `V:
    Droppable`) impl blocks (Rules 23-26) and so are simply unavailable for
    a linear element type; (iii) for a linear element type the release is
    `deinit_empty`, declared in the unbounded block and carrying `pre
    self.len() == 0`, after the caller has `pop`ped or `remove`d every
    element and consumed each. That `pre` is the ONE trap this rule keeps
    (kind `contract`; Rule 55). Every std iterator is non-linear and every
    `Item` is `Droppable` — a language fact now (ch09 Rule 21), not a std
    promise — so ch09 Rule 31's "the loop owns and drops the iterator"
    never drops a linear value.
    *Handoff*: DONE. ch01 Rules 22-22i are the sentences this rule asked
    for in round 5; Open question 2's third item is closed.
12. **S0012** — The allocator interface. Verbatim, in `std.mem.alloc`
    (re-exported as `mem.Allocator` and the prelude's `Allocator`):

    ```fors
    pub trait Allocator[A: brand] {
        fn alloc(inout self: Self, let layout: Layout) -> Block[A] raises AllocError;
        fn alloc_zeroed(inout self: Self, let layout: Layout) -> Block[A] raises AllocError;
        fn grow(inout self: Self, inout b: Block[A], let layout: Layout) raises AllocError;
        fn shrink(inout self: Self, inout b: Block[A], let layout: Layout);
        fn free(inout self: Self, sink b: Block[A]);
        fn owns(let self: Self, let b: Block[A]) -> bool;
        // provided (ch07 trait_item permits a body): written once in the
        // trait, in terms of alloc/free and the two @unsafe placement
        // primitives own_raw/disown_raw of Rule 28.
        // Round 6: `T: Droppable`, because the `?` below drops `v` on the
        // error exit and a rigid type may be linear (ch01 R22c, ch09 R57).
        // An `Own` of a LINEAR payload is still constructible, through
        // `alloc` plus the @unsafe `own_raw` of Rule 28, where the caller
        // can hold the payload across the fallible step itself.
        fn create[T: Droppable](inout self: Self, sink v: T) -> Own[T, A] raises AllocError {
            var b: Block[A] = self.alloc(Layout.of[T]())?;
            return own_raw(move b, move v);
        }
        fn deinit[T](inout self: Self, sink o: Own[T, A]) -> T {
            let (b, v) = disown_raw(move o);
            self.free(move b);
            return v;
        }
    }
    ```

    `deinit` RETURNS the payload: with no destructors, a `deinit` that
    dropped a linear `T` silently would leak it (Rule 11), so the caller
    receives it and consumes or drops it under ch01's rules (`heap.deinit(
    move b);` as a statement drops a non-linear payload, ch09 Rule 31).
    An allocator author implements the six required methods and inherits
    both provided ones.

    The brand parameter `A` is the allocator's own brand (ch01 Rules
    15-15e): an allocator value's type always mentions it
    (`PageAllocator[A]`, `mem.Heap[A]`), and the omitted form
    (`PageAllocator`) is legal only in a `with allocator` header (ch01 Rule
    15b) or as `main`'s heap parameter (Rule 17, the second and last such
    position). `Allocator` is therefore never a `dyn` type and never a type
    parameter's bound subject in an erased position (ch01 Rule 15(b)):
    allocator polymorphism in std is static, `[L: Allocator[A]]`.
    `mem.Allocator` names the same trait as the prelude's `Allocator`.
13. **S0013** — Layout, alignment, zeroing.

    ```fors-sig
    pub struct Layout { pub size: usize, pub align: usize }
    impl Layout {
        pub fn of[T]() -> Layout;
        pub fn array[T](let n: usize) -> Layout raises AllocError;
    }
    ```

    `align` MUST be a power of two and at most `MEM_MAX_ALIGN`, the named
    constant this chapter fixes at **16** until measured; a `Layout` value
    that violates either is impossible to construct (`of`/`array` are the
    only constructors and both compute it), and an allocator that cannot
    satisfy a legal `align` MUST raise `AllocError.unsupported_align`.
    `Layout.array[T](n)` MUST raise `AllocError.too_large` when
    `n * size_of[T]()` overflows `usize`, so no std allocation path can
    overflow silently. `alloc` returns UNINITIALISED bytes and std MUST
    NOT zero them; `alloc_zeroed` guarantees every byte is `0` on return.
    No std allocator zeroes on `free`, and freeing MUST NOT be assumed to
    scrub: a `secret` payload is scrubbed by the caller before `free`
    (ch05 owns the CT rules).
14. **S0014** — Reallocation. `grow` MAY move the block; on success `b`
    denotes the new block, on failure `b` is unchanged and still valid
    (so `grow` never loses memory). `shrink` is total and MAY be a no-op.
    Because both take `inout b: Block[A]`, every `Slice` or view derived
    from `b` is dead at the call under ch01 Rules 6-7 — reallocation
    invalidation is an exclusivity fact, not a convention.
15. **S0015** — `Block[A]`.

    ```fors-sig
    pub struct Block[A: brand] { }          // opaque, linear, not Copyable
    impl[A: brand] Block[A] {
        pub fn len(let self: Self) -> usize;
        pub fn alignment(let self: Self) -> usize;
        @unsafe(invariant: "the returned view spans exactly this block and is dead at the next grow/free")
        pub fn bytes_raw(inout self: Self) -> scoped(self) Slice[u8];
    }
    ```

    A `Block[A]` records its own size, so `free` takes no `Layout` and a
    wrong-size free is unrepresentable. `Block[A]` is linear (Rule 11) and
    MUST NOT be `Copyable`, stored in a type that outlives its allocator's
    brand, or converted to an erased form (ch01 Rule 15(b)).
16. **S0016** — Freeing. `free` and `deinit` are TOTAL: they MUST NOT be
    declared `raises` and MUST NOT trap. Brand equality makes them safe
    without a runtime check: `free`/`deinit` accept only a `Block[A]` /
    `Own[T, A]` whose `A` equals the receiver's, which ch01 Rule 18 checks
    per call, so a safe program cannot free with the wrong allocator (PLAN
    R2) and cannot double-free (linearity, Rule 11). Freeing is the only
    way storage returns to an allocator; std has no finaliser, no
    destructor and no `defer`.
17. **S0017** — The process heap. `mem.Heap` is the type of the process
    heap and is a root-capability-typed `main` parameter (ch04 Rule 21, as
    amended by this chapter), with **no capability and no `needs` entry**:
    allocation is not authority (owner decision D5), and no capability
    word for allocation exists. `mem.Heap` is opaque and constructorless
    (ch04 Rule 7) and obeys ch01 Rule 15a exactly as a `with allocator`
    binding does: not `Copyable`, never stored in a field, never moved,
    passed only `let` or `inout`, at most one live value per process.
    **Its brand is a fresh brand named by the parameter**: in
    `fn main(inout heap: mem.Heap)` the identifier `heap` denotes both the
    value and the brand β inside `main`'s body, so `Own[i64, heap]` and
    `Vec[T, heap]` are written exactly as inside a `with allocator heap:`
    block, β has no other spelling, and `main` stays non-generic (ch04
    Rule 8). The type is `mem.Heap[A]`, and the parameter writes it with
    the brand argument OMITTED (`inout heap: mem.Heap`), which is the
    second position where ch01 Rule 15b's omitted form is legal — the
    first being the `with` header. ch04 Rule 8's "exactly and nominally"
    test is satisfied by the omitted form and by no other. A program that wants heap memory in a callee passes the
    allocator down, as an ordinary `let`/`inout` parameter with a brand
    parameter in the callee's `generics` (ch01 Rule 15d).
    *Handoff*: ch01 Rule 15/15a should cite this as the second origin of
    an allocator value and of a fresh brand.
18. **S0018** — `PageAllocator`. A page-granular allocator that obtains
    whole pages from the operating system and returns them on `free`; it
    is the only std allocator a program can create without a `main`
    parameter, through `with allocator p: PageAllocator { ... }` (ch01 Rule
    15). It needs no capability, because allocation is not authority; the
    syscalls behind it are sealed inside `std.mem` (Rule 53). Its
    `Layout.align` support is `MEM_MAX_ALIGN`, its granularity is the
    target page size, and `alloc` of a small layout still consumes a page:
    `PageAllocator` is the substrate `mem.Heap` and `mem.Bump` are built
    on, not a general-purpose allocator.
19. **S0019** — `mem.Bump`, the arena allocator: `with allocator a:
    mem.Bump { ... }` gets regions from the operating system, serves
    `alloc` by bumping a pointer, makes `free` a no-op that keeps
    linearity honest, and releases every region at the block's close.
    `fn reset(inout self: Self)` releases every allocation made since the
    last `reset` in one step; every `Block[A]` and `Own[T, A]` of its brand
    is dead at that call by ch01 Rules 6-7, since `reset` takes `inout
    self` and every such value's type mentions the brand. `mem.Bump` is
    NOT ch01's `Arena[T, A]`: `Arena[T, A]` is the typed, generation-
    checked arena with `Ref[T, A]` handles (ch01 Rules 15-17), whose
    surface is
    `fn alloc(inout self: Arena[T, A], sink v: T) -> Ref[T, A] raises AllocError`,
    `fn reset(inout self: Arena[T, A])`, and `Index[Ref[T, A]]`;
    `mem.Bump` is an untyped `Allocator` for the containers of Rules
    23-26. A program may use either or both.
20. **S0020** — `mem.Fixed[N: usize, A: brand]`, the fixed-buffer
    allocator, whose brand argument is last so that the `with` header may
    omit it (ch01 Rule 15b): `with
    allocator f: mem.Fixed[65536] { ... }` serves allocations out of `N`
    bytes of storage inline in the block's frame, touches no operating
    system, and raises `AllocError.out_of_memory` when exhausted. It is the
    allocator for freestanding code and for tests: a module with
    `needs { };` and no import can use it.
    *Why not "over a caller-owned slice", as the owner's brief asks*:
    `with_stmt` is `"with" ("arena"|"allocator") ident ":" type block`
    (ch07) — the header takes a TYPE and no arguments — ch01 Rule 15a
    forbids a constructor, and ch01 Rule 19a forbids storing the caller's
    `Slice` in a field. A const-generic capacity is the only spelling the
    frozen language leaves. Open question 3 asks the owner whether v0.2
    should give `with_stmt` an argument list.
21. **S0021** — `mem.Counting[N: usize, A: brand]`, the testing allocator: a
    `mem.Fixed[N]` that also counts. `fn bytes_live(let self: Self) ->
    usize`, `fn allocs(let self: Self) -> u64`, `fn frees(let self: Self)
    -> u64`, `fn peak_bytes(let self: Self) -> usize`, and
    `fn assert_empty(let self: Self)` which traps (kind `contract`, ch02
    Rule 15) iff `bytes_live() != 0`. It is a standalone allocator, not a
    wrapper around a parent one, for the reason in Rule 20: ch01 Rule 15a
    forbids holding another allocator value in a field, so a wrapping
    allocator is not expressible in v0.1.
22. **S0022** — `Own[T, A]`, the single heap value (ch01 Rule 18 owns its
    brand rule). Std's surface:

    ```fors-sig
    impl[T: Copyable, A: brand] Own[T, A] {
        pub fn get(let self: Self) -> T;                       // a copy
        pub fn set(inout self: Self, let v: T);
    }
    impl[T, A: brand] Own[T, A] {
        pub fn replace(inout self: Self, sink v: T) -> T;      // exchange, total
    }
    ```

    An `Own[T, A]` is created only by `Allocator.create` and destroyed only
    by `Allocator.deinit` (Rule 12), which hands the payload back; it is
    linear (Rule 11). The language has NO dereference operator (ch07's
    `unary_expr` has no `*`) and no reference type, so a method cannot
    return a *view* of a non-`Copyable` payload: a `fn get(let self) ->
    scoped(self) T` would return `T` BY VALUE, giving the caller a second
    owner of the heap payload (a call result is not a `place`, so ch01
    Rule 4a(c)'s partial-move ban cannot catch it). Hence the surface
    above: a `Copyable` payload is copied in and out, and any payload is
    reached by exchange or by `deinit`. Open question 4 records the
    ergonomic cost.

### The core types

23. **S0023** — `Buffer[T, N: usize]`, the inline fixed-capacity buffer:

    ```fors-sig
    pub struct Buffer[T, N: usize] { pub len: usize, pub data: Array[T, N] }
    impl[T, N: usize] Buffer[T, N] {
        pub fn empty() -> Buffer[T, N];
        pub fn cap(let self: Self) -> usize;                     // = N
        pub fn push(inout self: Self, sink v: T) -> Option[T];    // some(v) iff full: v comes back
        pub fn pop(inout self: Self) -> Option[T];
        pub fn items(let self: Self) -> scoped(self) Slice[T];    // self.data[0 ..< self.len]
        pub fn items_mut(inout self: Self) -> scoped(self) Slice[T];
        pub fn into_iter(sink self: Self) -> BufferIter[T, N];
    }
    impl[T: Droppable, N: usize] Buffer[T, N] {
        pub fn clear(inout self: Self);                          // drops elements: Rule 11c
    }
    impl[T: Copyable, N: usize] Buffer[T, N] {
        pub fn filled(let v: T) -> Buffer[T, N];                 // len = N
        pub fn iter(let self: Self) -> scoped(self) SliceIter[T]; // = mem.iter(self.items())
    }
    impl[T, N: usize] Index[usize] for Buffer[T, N] { type Output = T; }
    impl[T, N: usize] IndexMut[usize] for Buffer[T, N] { }
    ```

    `Buffer` owns its storage INLINE and takes no allocator, so it is the
    one container usable in a module with no allocator in scope — which is
    exactly how every corpus site uses it. `N` is its capacity and is part
    of its type; `len` is the initialised prefix; `Index`/`IndexMut` are
    bounds-checked against `len`, not `N`, and trap (kind `bounds`) out of
    range. It is not linear: it owns no allocation. `push` is total and
    reports fullness by RETURNING the value (`some(v)`; `none` means
    stored): a `sink` parameter MUST be moved or consumed on every path
    (ch01 Rule 4), and a full buffer can do neither with a non-`Copyable`
    `v`, so a `bool` result was unsound. Fullness is a capacity fact the
    caller can see with `cap`, not an allocation failure (Rule 6c).
    `items`/`items_mut` are ordinary range-indexings of the `data` field,
    so they need no unsafe primitive (ch03 Rule 24).
    `Buffer` has no one-parameter form: a heap-free buffer whose capacity
    is a runtime value is not implementable without an allocator, and
    under D5 there is no ambient one. See the corpus defects.
    **Round 6.** `Buffer[X, N]` with a linear `X` is ILL-FORMED, because
    its `data` field is an `Array[X, N]` (ch09 Rule 11, ch01 Rule 22b),
    and so is `Buffer[Option[X], N]`, since `lin(Option[X])` is `lin(X)`;
    a variable number of linear values lives in a `Vec` (Rule 24). `clear`
    drops its elements, so it moved to a `T: Droppable` block; `push` and
    `pop` need no bound, because each hands the value back. `BufferIter`'s
    `impl Iterator` is `impl[T: Droppable, N: usize]` (round-6
    verification): `Self: Droppable` and `Item: Droppable` (Rule 32) both
    need it with `T` rigid, and no `Buffer` of a non-`Droppable` `T` exists
    anyway.
24. **S0024** — `Vec[T, A: brand]`, the growable array:

    ```fors-sig
    pub struct Vec[T, A: brand] { }         // opaque
    impl[T, A: brand] Linear for Vec[T, A] { }      // linear ALWAYS: Rule 11, ch01 Rule 22
    impl[T, A: brand] Vec[T, A] {
        pub fn new() -> Vec[T, A];                                          // allocates nothing
        pub fn len(let self: Self) -> usize;
        pub fn cap(let self: Self) -> usize;
        pub fn push[L: Allocator[A]](inout self: Self, inout a: L, sink v: T) raises AllocError;
        pub fn pop(inout self: Self) -> Option[T];
        pub fn reserve[L: Allocator[A]](inout self: Self, inout a: L, let extra: usize) raises AllocError;
        pub fn shrink_to_fit[L: Allocator[A]](inout self: Self, inout a: L);
        pub fn swap_remove(inout self: Self, let i: usize) -> T;
        @unsafe(invariant: "the view spans len initialised elements and is dead at the next push/reserve/deinit")
        pub fn items(let self: Self) -> scoped(self) Slice[T];
        @unsafe(invariant: "as items, and exclusive for the extent of the borrow")
        pub fn items_mut(inout self: Self) -> scoped(self) Slice[T];
        pub fn deinit_empty[L: Allocator[A]](sink self: Self, inout a: L) pre self.len() == 0;
    }
    impl[T: Droppable, A: brand] Vec[T, A] {        // Rule 11c: these DROP elements
        pub fn clear(inout self: Self);
        pub fn deinit[L: Allocator[A]](sink self: Self, inout a: L);
    }
    impl[T: Copyable, A: brand] Vec[T, A] {
        pub fn iter(let self: Self) -> scoped(self) SliceIter[T];         // = mem.iter(self.items())
    }
    impl[T, A: brand] Index[usize] for Vec[T, A] { type Output = T; }
    impl[T, A: brand] IndexMut[usize] for Vec[T, A] { }
    ```

    The allocator is a PARAMETER of every growing operation, never a field:
    ch01 Rule 15a forbids storing it. `A` is the allocator's brand, so
    `v.push(&other, x)` with an allocator of another brand is a compile
    error (ch01 Rules 15d, 18) and `Vec`'s storage can only ever be
    returned to the allocator that produced it. `Vec.new()` allocates
    nothing and determines `T` and `A` from its CHECK position (ch09 Rule
    38(c)); in a SYNTH position write `Vec.new[i32, heap]()`. Growth is
    amortised by doubling from a first capacity of 4 elements; the growth
    schedule is deterministic and part of this rule, because `cap` is
    observable. **`Vec` is linear ALWAYS**, not "once it has capacity"
    (round 6): linearity is a fact of the constructor, never of a value's
    state or of an instantiation (ch01 Rule 22), and `deinit` on an empty
    `Vec` is total and free, so nothing is lost by the simpler rule. The
    release is `deinit` when `T: Droppable` and `deinit_empty` — after
    `pop`ping and consuming every element — when it is not (Rule 11c); one
    of the two MUST be called on every path (ch01 Rule 22h), and `defer` or
    `errdefer` is how that is written once (ch01 Rule 23d(b)).
25. **S0025** — `Map[K, V, A: brand]`, the hash map:

    ```fors-sig
    pub struct Map[K, V, A: brand] { }      // opaque
    impl[K, V, A: brand] Linear for Map[K, V, A] { }    // linear ALWAYS: Rule 11
    impl[K: Eq + Hash, V, A: brand] Map[K, V, A] {
        pub fn new() -> Map[K, V, A];
        pub fn seeded(let seed: u64) -> Map[K, V, A];
        pub fn len(let self: Self) -> usize;
        pub fn has(let self: Self, let k: K) -> bool;
        pub fn insert[L: Allocator[A]](inout self: Self, inout a: L, sink k: K, sink v: V)
            -> Option[V] raises AllocError;
        pub fn remove(inout self: Self, let k: K) -> Option[V];
        pub fn reserve[L: Allocator[A]](inout self: Self, inout a: L, let extra: usize) raises AllocError;
        pub fn deinit_empty[L: Allocator[A]](sink self: Self, inout a: L) pre self.len() == 0;
    }
    impl[K: Eq + Hash, V: Droppable, A: brand] Map[K, V, A] {   // Rule 11c: these DROP values
        pub fn clear(inout self: Self);
        pub fn deinit[L: Allocator[A]](sink self: Self, inout a: L);
    }
    impl[K: Eq + Hash, V: Copyable, A: brand] Map[K, V, A] {
        pub fn get(let self: Self, let k: K) -> Option[V];
        pub fn get_or(let self: Self, let k: K, let fallback: V) -> V;
    }
    impl[K: Eq + Hash, V, A: brand] Index[K] for Map[K, V, A] { type Output = V; }   // m[k]; traps (bounds) if absent
    impl[K: Eq + Hash, V, A: brand] IndexMut[K] for Map[K, V, A] { }
    pub trait Hash { fn hash(let self: Self, let seed: u64) -> u64; }
    ```

    The value at a present key is reached as the PLACE `m[k]` (`Index`/
    `IndexMut`), never by a method returning `V`: a call result is a
    value, so an `at(let self, k) -> scoped(self) V` would hand a
    non-`Copyable` `V` to a second owner, whereas `m[k]` is a ch07 `place`
    on which ch01 Rule 4a(c) forbids the partial move and ch09 Rule 21
    types the assignment. `m[k]` traps (kind `bounds`) if `k` is absent;
    the checked form is `has` then `m[k]`. `Hash` lives in
    `std.mem.hashmap` and is re-exported as `mem.Hash`, not in the
    prelude: a program that implements it for its own key type is already
    writing `use std.mem;`. `Hash` and `Eq` MUST agree — `a.eq(b)` implies
    `a.hash(s) == b.hash(s)` for every `s` — and an impl that breaks this
    is a defect in that impl, which std cannot detect. `Map.new()` uses a
    FIXED seed, so a program's behaviour is reproducible by default
    (ch03's D1 determinism); `Map.seeded(s)` takes a seed the program
    chose, which is the only way to get hash-flooding resistance, and it
    requires the program to have obtained entropy through `rand.Rng`
    (Rule 47). Iteration order is unspecified but deterministic: the same
    sequence of operations on the same build yields the same order.
    Two `get`-shaped methods exist because `Option[V]` can return a value
    only when `V` is `Copyable`; for a non-`Copyable` `V` use `has` +
    `m[k]`. **Round 6.** `Map` is linear always (as `Vec` is, Rule 24), and
    `clear`/`deinit` need `V: Droppable` because they drop the values; `K`
    is already `Copyable` through `Eq + Hash` (Rule 29), so a linear key
    cannot arise. For a linear `V` the release is `deinit_empty` after
    `remove`ing and consuming every value (Rule 11c).
26. **S0026** — `String[A: brand]` and `Str`.

    ```fors-sig
    pub struct String[A: brand] { }         // opaque; UTF-8 by invariant
    impl[A: brand] Linear for String[A] { }        // linear ALWAYS: Rule 11
    impl[A: brand] String[A] {
        pub fn new() -> String[A];
        pub fn len(let self: Self) -> usize;                                 // bytes
        @unsafe(invariant: "the view spans this String's initialised, valid UTF-8 bytes")
        pub fn as_str(let self: Self) -> scoped(self) Str;                    // block storage: Rule 28
        pub fn push_str[L: Allocator[A]](inout self: Self, inout a: L, let s: Str) raises AllocError;
        pub fn push_scalar(inout self: Self, let cp: u32) raises Utf8Error;  // pre cap - len >= 4: reserve first
        pub fn from_str[L: Allocator[A]](inout a: L, let s: Str) -> String[A] raises AllocError;
        pub fn reserve[L: Allocator[A]](inout self: Self, inout a: L, let extra: usize) raises AllocError;
        pub fn clear(inout self: Self);
        pub fn deinit[L: Allocator[A]](sink self: Self, inout a: L);
    }
    impl Str {
        pub fn len(let self: Self) -> usize;                                 // bytes, never code points
        pub fn at(let self: Self, let i: usize) -> u8;                       // byte; traps (bounds)
        pub fn slice(let self: Self, let start: usize, let end: usize)
            -> scoped(self) Str raises Utf8Error;
        pub fn eq(let self: Self, let rhs: Str) -> bool;                     // byte equality
        pub fn starts_with(let self: Self, let p: Str) -> bool;
        pub fn find(let self: Self, let needle: Str) -> Option[usize];
        pub fn from_utf8(let bytes: Slice[u8]) -> scoped(bytes) Str raises Utf8Error;
        @unsafe(invariant: "the view spans exactly this Str's bytes")
        pub fn bytes_raw(let self: Self) -> scoped(self) Slice[u8];
        pub fn scalars(let self: Self) -> scoped(self) Scalars;              // Iterator, Item = u32
    }
    ```

    **A `Str` is a borrowed, always-valid UTF-8 view. Indexing is by BYTE
    and nothing else**: there is no code-point index, no length in
    characters, and no `char` type (Rule 10(k)). `len`, `at` and `find`
    are byte-denominated; `at` traps out of range like every index.
    `slice(start, end)` traps (kind `contract`: it carries `pre start <=
    end and end <= self.len()`) if `start > end` or `end > len` — that is
    a bug — and raises `Utf8Error.not_a_boundary` if either endpoint falls
    inside a multi-byte sequence — that is data. `from_utf8` is the ONLY
    validating entry and the only way a `Str` is built from bytes;
    `String`'s UTF-8 invariant then holds by construction, which is why
    `push_str` cannot fail on validity and `push_scalar` is the one text
    operation whose failure is `Utf8Error` (a surrogate or out-of-range
    scalar). `push_scalar` takes NO allocator and never grows: it carries
    `pre self.cap() - self.len() >= 4` (kind `contract`), so that it has
    exactly one failure mode (Rule 6b) — a caller `reserve`s, then pushes. A `Str` from a literal has
    static storage and is not scoped; a `Str` derived from a `String`,
    `Buffer` or `Slice` is scoped to it (ch01 Rules 19-19a). Comparison is
    byte-wise: std has no case folding, no normalisation and no collation
    (Rule 56). **Round 6.** `String[A]` is linear always; its elements are
    bytes, which are `Copyable` and therefore `Droppable`, so `clear` and
    `deinit` need no bound and there is no `deinit_empty` for `String`.
27. **S0027** — `Option[T]` is ch09 Rule 5's built-in enum with `some(T)`
    and `none`, whose constructors the prelude binds as values (ch08 Rule
    17); this chapter adds only
    `fn unwrap_or(sink self: Option[T], sink fallback: T) -> T` and
    `fn is_some(let self: Option[T]) -> bool`, and no `unwrap` that traps.
    There is NO `Result`-shaped type in v0.1 (Rule 10(b)): a std operation
    that can fail says `raises` (Rule 6b), and a std operation whose answer
    may be absent returns `Option` (Rule 6c).
28. **S0028** — `Slice[T]` and std's slice primitives. A `Slice[T]` is
    obtained only by range-indexing an array or another slice (ch03 Rule
    24) and is a scoped value (ch01 Rules 19-19b). Every std accessor that
    hands out a `Slice[T]`, a `Str` or an iterator over storage that is
    NOT an `Array` field — `Block.bytes_raw`, `Vec.items`, `Vec.items_mut`,
    `String.as_str`, `String`'s and `Str`'s `bytes_raw`, `Str.scalars`,
    `split_at`, `mem.iter` (Rule 33) and `Iterator.by_ref` (Rule 34) — is
    therefore an `@unsafe(invariant: "...")` declaration (ch04 Rules
    9-10) and appears in the published unsafe inventory; ch01 Rule 19b
    already fixes this shape for `split_at`. The two placement primitives
    Rule 12's provided bodies use are in the same inventory:
    `@unsafe fn own_raw[T, A: brand](sink b: Block[A], sink v: T) ->
    Own[T, A]` (`b` MUST have `Layout.of[T]()`'s size and align) and
    `@unsafe fn disown_raw[T, A: brand](sink o: Own[T, A]) -> (Block[A],
    T)`, both in `std.mem.alloc`. Everything std adds ON a slice is safe
    and total: `fn fill(inout s: Slice[T], let v: T)` (`T: Copyable`),
    `fn copy_from(inout dst: Slice[T], let src: Slice[T])` (traps on
    unequal length, kind `contract`), `fn swap(inout s: Slice[T], let i:
    usize, let j: usize)`, `fn eq(let a: Slice[T], let b: Slice[T]) ->
    bool` (`T: Eq`).
    *Handoff*: ch03 Rule 24's "no other constructor for `Slice[T]` exists"
    should gain "outside the `@unsafe` std primitives of ch10 Rule 28",
    exactly as ch01 Rule 19b words it. Recorded as Open question 2.
29. **S0029** — `mem.Hash` is implemented by std for `Str`, every integer
    type, `bool` and `Slice[T]` where `T: Hash`; the hash function is
    fixed, documented as non-cryptographic, and MUST NOT depend on the
    target, the build or any address. Std does NOT implement `Hash` for
    `f32`/`f64` (`Eq` on floats does not agree with any hash on `-0.0` and
    NaN, ch03).
30. **S0030** — `Copyable` and `Shared` for std types. `Str`, `Slice[T]`,
    `Layout`, `time.Instant`, `time.Wall`, `time.Duration`, `net.Addr`,
    every std error type and `Option[T]` for `Copyable` `T` are
    `Copyable`. `Buffer[T, N]` is `Copyable` iff `T` is. No linear type
    (Definitions) is `Copyable`, no allocator is `Copyable` (ch01 Rule
    15a), and no root-capability type is `Copyable` (ch04 Rule 7). Which
    std types implement `Shared` is Rule 51.
31. **S0031** — Ordering. `fn sort(inout s: Slice[T])` for `T: Ord + Copyable`
    is in-place, allocation-free, UNSTABLE, and deterministic: the
    permutation it produces is a pure function of the input sequence, the
    same on every target and build mode, so a program's output cannot
    depend on the sort's implementation freedom. `fn try_sort_by[E](inout s:
    Slice[T], let less: fn (let T, let T) -> bool raises E) raises E`
    is its `try_` sibling (Rule 8); `fn binary_search(let s: Slice[T], let
    key: T) -> Option[usize]` requires a sorted slice and its result is
    unspecified-but-total otherwise.

### Iteration

32. **S0032** — The `Iterator` trait. Its REQUIRED part is language-known
    (ch09 Rule 21): `type Item: Droppable;` and `fn next(inout self) ->
    Option[Self.Item];`. Std DECLARES that same trait, in `std.mem.seq`,
    and adds to it the PROVIDED methods of Rules 34-35; the prelude name
    `Iterator` and `mem.seq.Iterator` denote ONE item (Definitions,
    "Defining module"; ch08 Rule 13's same-entity case), so there is one
    trait, not two. Three std obligations follow. `next` is TOTAL for
    every std iterator: it cannot be `raises`, so a failing source MUST NOT
    be modelled as an iterator. `next` MUST NOT trap except through ch02
    Rule 15 conditions in the user code it calls. And no std type that
    implements `Iterator` MAY declare an INHERENT method whose name is that
    of a provided method of `Iterator` (Rule 34): ch09 Rule 44's
    inherent-before-trait precedence would silently re-route the call.
    Round 6 also makes "no std iterator is linear, and no `Item` is linear"
    a LANGUAGE fact rather than a std promise: `impl Iterator for S`
    requires `S: Droppable` and the trait bounds `Item: Droppable` (ch09
    Rule 21).
33. **S0033** — How a container yields an iterator, under the convention
    system, is exactly two forms in v0.1, plus indexing:
    (a) over `let` data: ONE iterator type, `SliceIter[T]` (`std.mem.seq`,
    `mem.SliceIter`), with `Item = T` and `T: Copyable` — it yields
    COPIES — produced by the one unsafe primitive
    `@unsafe fn mem.iter[T: Copyable](let s: Slice[T]) -> scoped(s)
    SliceIter[T]`. A container's `fn iter(let self: Self) -> scoped(self)
    SliceIter[T]` is `mem.iter(self.items())`, safe in itself (the scoped
    derivation flows from `self` through `items`, ch01 Rule 19), and its
    `scoped(self)` result keeps the container borrowed `let` for the
    iterator's whole life (ch01 Rule 19a), so a concurrent mutation is an
    exclusivity error, not an invalidation bug. `SliceIter` holds a base
    and a count, NOT a `Slice` field, because a scoped value MUST NOT be
    stored in a field (ch01 Rule 19a); that is why `mem.iter` is
    `@unsafe` and in the inventory (ch04 Rule 9).
    (b) consuming, for allocator-free containers only:
    `fn into_iter(sink self: Self) -> BufferIter[T, N]` with `Item = T`,
    which moves elements out; `Buffer[T, N]` has it, `Vec`, `Map` and
    `String` do NOT (Rule 10(e)); `Array[T, N]` is iterated by `for`
    directly (ch09 Rule 31) and has no `into_iter`.
    (c) over `inout` data: NOT PROVIDED (Rule 10(d)). Mutate by index:
    `for i in 0 ..< v.len() { v[i] = f(v[i]); }`, which is also the form
    `parallel for` and `simd for` accept (ch01 Rule 9's varying-index
    rule).
    No std iterator is linear or `Copyable`; every one is a plain value
    whose only obligation is the scoped extent of (a). A scoped iterator is
    chained by the adaptor methods of Rule 34, whose results inherit that
    extent (ch01 Rule 19c(a)); a container of LINEAR elements is emptied by
    `pop`/`remove`, never iterated by value, because no linear `Item` can
    exist (Rule 32).
34. **S0034** — The adaptor set is closed for v0.1. **Each is a PROVIDED
    METHOD of `Iterator`** (ch09 Rules 16, 43), taking its source by value
    and returning a CONCRETE adaptor struct that carries its own ordinary,
    struct-headed `impl Iterator`. This is NOT a blanket impl (ch09 Rule 18
    is untouched) and needs no new language feature: round 6 disproved this
    rule's earlier conclusion that `it.map(f)` "is not writable" — the
    obstacle was never method lookup but OWNERSHIP, and it is removed by
    ch01 Rule 19c, which makes a call's result inherit its scoped argument's
    extent when the callee's declared result type mentions the parameter
    that argument went into. `v.iter().map(f)` therefore yields a value
    scoped to `v`, exactly as the old one-binding-per-stage chain did.

    | Provided method of `Iterator` | Result | `Item` of the result |
    |---|---|---|
    | `fn map[U: Droppable](sink self, let f: fn (sink Self.Item) -> U)` | `Mapped[Self, U]` | `U` |
    | `fn filter(sink self, let p: fn (let Self.Item) -> bool)` | `Filtered[Self]` | `Self.Item` |
    | `fn take(sink self, let n: usize)` | `Taken[Self]` | `Self.Item` |
    | `fn skip(sink self, let n: usize)` | `Skipped[Self]` | `Self.Item` |
    | `fn enumerate(sink self)` | `Enumerated[Self]` | `(usize, Self.Item)` |
    | `fn zip[J: Iterator](sink self, sink other: J)` | `Zipped[Self, J]` | `(Self.Item, J.Item)` |
    | `fn by_ref(inout self)` | `scoped(self) ByRef[Self]` | `Self.Item` |

    The adaptor structs, all in `std.mem.seq` and re-exported as
    `mem.Mapped`, `mem.Filtered`, …:

    ```fors-sig
    pub struct Mapped[I: Iterator, U: Droppable] { src: I, f: fn (sink I.Item) -> U }
    pub struct Filtered[I: Iterator]  { src: I, p: fn (let I.Item) -> bool }
    pub struct Taken[I: Iterator]     { src: I, left: usize }
    pub struct Skipped[I: Iterator]   { src: I, to_skip: usize }
    pub struct Enumerated[I: Iterator] { src: I, at: usize }
    pub struct Zipped[I: Iterator, J: Iterator] { a: I, b: J }
    pub struct ByRef[I: Iterator]     { src: rawptr[I] }
    ```

    Five constraints on these declarations, each with the rule that forces
    it. **(1) A callable parameter is a `fn` TYPE, never a callable type
    parameter `F`**: ch09 Rule 38 never binds a parameter through a BOUND,
    so `fn map[U, F: fn (sink Self.Item) -> U](sink self, let f: F)` would
    make `it.map(double)` a T0039 "cannot infer `U`"; with a `fn` type the
    fn item's type is matched componentwise and binds `U`, and a closure
    argument is handled by ch09 Rule 41. It also keeps the adaptor types
    WRITABLE (`mem.Taken[mem.Mapped[mem.SliceIter[i32], i32]]`), since a
    closure type cannot be written (ch09 Rule 7) — which a `var`
    annotation needs (ch09 Rule 31). **(2) An adaptor carries every
    parameter it needs in its own head** (`Mapped[I, U]`), because
    `impl[I: Iterator, U] Iterator for Mapped[I]` would leave `U`
    unconstrained (ch09 Rule 18). **(3) The names are `Mapped`,
    `Filtered`, …, never `Map` or `Filter`**: `Map` is the hash map and a
    prelude name (Rule 2), and a submodule `mem.iter` is impossible because
    `mem` has one namespace already holding the function `mem.iter` (ch08
    Rule 13). **(4) `map` takes its item `sink`, predicates take it
    `let`**: `fn (let Self.Item) -> U` would forbid `|sink x| x` for a
    non-`Copyable` item (ch01 Rule 3). **(5) A callable FIELD is called as
    `(self.f)(move x)`**, never `self.f(x)`, which is method-call form and
    is ch09 T0043.
    Every adaptor is lazy and allocates nothing, so the set has no
    `collect`, no `sorted` and no `group_by`; a callable passed to one MUST
    NOT be `raises` (Rule 8; ch09 Rule 60 makes the type mismatch the
    diagnostic). There is no `chain`: its `Item` needs `J.Item = I.Item`,
    and ch07's `gconstraint` states a bound, not an equality.
    `by_ref` is the ONE borrowing adaptor and the only struct in `seq` with
    a raw pointer, so it is an `@unsafe(invariant: "...")` declaration in
    the inventory (Rule 28, ch04 Rules 9-10); it is how an `inout`
    iterator or an iterator held in a field is chained, since every other
    adaptor takes `sink self` and ch01 Rule 4a(c)-(d) forbid moving out of
    a field or an `inout` parameter. `zip` owns BOTH sources; the old rule
    "the second source is owned" is gone from the signature: a result with
    two scoped sources keeps both (ch01 Rule 19c(d)) and is an ordinary
    local that Rule 19 forbids returning. `map[U: Droppable]` and the
    `U: Droppable` on `Mapped`'s head and impl are forced by ch09 Rules
    17 and 21 (`type Item = U;` must satisfy `Item: Droppable` with `U`
    rigid): a closure returning a linear value is rejected at `map`
    (T0012), and no iterator of linear items exists. **Round 6 deletes** the free functions `mem.map`,
    `mem.filter`, `mem.take`, `mem.skip`, `mem.enumerate` and `mem.zip`;
    `mem.iter` stays. The unsafe inventory loses six adaptor entries and
    keeps two, `mem.iter` and `Iterator.by_ref`.

    ```fors
    module std.mem.seq;
    needs { };

    // The shape of every adaptor, in full: a provided method of the trait
    // returns a concrete struct that carries its own impl.
    pub struct Mapped[I: Iterator, U: Droppable] { src: I, f: fn (sink I.Item) -> U }

    impl[I: Iterator, U: Droppable] Iterator for Mapped[I, U] {   // U: Droppable — ch09 Rules 17, 21
        type Item = U;
        fn next(inout self) -> Option[U] {
            match self.src.next() {
                some(let x) => { return some((self.f)(move x)); }
                none => { return none; }
            }
        }
    }
    ```
35. **S0035** — The consumer set is closed for v0.1 and is also PROVIDED
    METHODS of `Iterator`, each taking its source `sink self` (it is used
    up) and returning a plain value:

    | Provided method of `Iterator` |
    |---|
    | `fn count(sink self) -> usize` |
    | `fn fold[B](sink self, sink init: B, let f: fn (sink B, sink Self.Item) -> B) -> B` |
    | `fn for_each(sink self, let f: fn (sink Self.Item))` |
    | `fn all(sink self, let p: fn (let Self.Item) -> bool) -> bool` |
    | `fn any(sink self, let p: fn (let Self.Item) -> bool) -> bool` |
    | `fn find(sink self, let p: fn (let Self.Item) -> bool) -> Option[Self.Item]` |
    | `fn try_fold[B, E](sink self, sink init: B, let f: fn (sink B, sink Self.Item) -> B raises E) -> B raises E` |
    | `fn try_for_each[E](sink self, let f: fn (sink Self.Item) raises E) raises E` |

    Each body is `for x in self { ... }`, which is legal because `Self:
    Iterator` implies `Self: Droppable` and `Self.Item: Droppable` (ch09
    Rule 21), so the loop may own and drop the iterator and drop each item
    even with `Self` rigid (ch09 Rules 16, 31, 57). The two `try_` siblings
    carry `E` as a method parameter (ch09 Rule 60) and satisfy Rule 8's
    "same name modulo the prefix, same parameter order". A consumer's
    result mentions no type parameter of the receiver's head, so nothing it
    returns is scoped (ch01 Rule 19c(a)): `v.iter().count()` ends `v`'s
    borrow at the statement (ch01 Rule 19c(c)).
    Collecting stays a FREE FUNCTION,
    `fn try_collect_into[I: Iterator, A: brand, L: Allocator[A]]
    (sink it: I, inout dst: Vec[I.Item, A], inout a: L) raises AllocError`,
    declared in `std.mem.vec` and re-exported as `mem.try_collect_into`:
    `seq` is a leaf and cannot name `Vec` (Rule 1), and as an inherent
    `Vec` method it would need the equality `I.Item = T`, which v0.1 has no
    way to state (ch09 Rule 16). It names its destination and its
    allocator, because a `collect` that invented a container would allocate
    ambiently (Rule 3). **Round 6 deletes** the free functions `mem.count`,
    `mem.fold`, `mem.for_each`, `mem.all`, `mem.any`, `mem.find`,
    `mem.try_fold` and `mem.try_for_each`.
36. **S0036** — `for` over std. `for p in e` accepts `Range`/`RangeIncl`,
    `Array[T, N]`, `Slice[T]` and any `Iterator` (ch09 Rule 31), which is
    the whole surface: `for x in v.items()` (a `Slice`, elements by value),
    `for x in v.iter()` (an `Iterator`, copies), `for i in 0 ..< v.len()`
    (indices, the only mutating form), `for x in buf.into_iter()`
    (consuming, allocator-free containers). The iterable is a value use, so
    `for x in it` with a named iterator MOVES it (ch09 Rule 31), which is
    harmless: no std iterator is linear (Rule 33).
37. **S0037** — Determinism of iteration. Every std iterator and adaptor
    visits its elements in one fixed order, is sequential, and MUST NOT be
    parallelised by any pass: `reduce` (ch03 Rules 11-13) is the ONLY
    parallel reduction in the language, its tree shape is fixed, and no
    std consumer is an alias for it. `fold` and `try_fold` are strictly
    left-to-right and MUST NOT be reassociated, whatever the operation's
    algebra. Being provided METHODS (Rules 34-35) changes none of this: a
    provided body is ordinary code, checked once (ch09 Rule 16).

### I/O and authority

38. **S0038** — For every capability module, the root-capability type
    `main` receives and the capability it pairs with are ch04 Rule 21's,
    unchanged: `io.Stdout`→`io.stdout`, `io.Stderr`→`io.stderr`,
    `io.Stdin`→`io.stdin`, `fs.Dir`→`fs.read`/`fs.write`, `net.Net`→`net`,
    `proc.Exec`→`exec`, `time.Clock`→`clock`, `rand.Rng`→`rng`,
    `env.Env`→`env`, `env.Args`→`env`, `gpu.Device`→`gpu`, plus this
    chapter's `mem.Heap`→(none) (Rule 17). Every operation below takes its
    capability value as its receiver or a parameter; a module using one
    declares the capability in its own `needs` (ch04 Rule 1) and imports
    the module for the NAME (ch08 Rule 17) — two independent obligations.
    No std operation derives authority from anything else.
39. **S0039** — `io`. The traits and the standard streams:

    ```fors-sig
    pub trait Writer {
        fn write(inout self: Self, let bytes: Slice[u8]) -> usize raises Error;
        fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error;
        fn flush(inout self: Self) raises Error;
    }
    pub trait Reader {
        fn read(inout self: Self, inout into: Slice[u8]) -> usize raises Error;
    }
    pub struct Stdout { }       // root capability, opaque (ch04 Rule 7)
    impl Stdout {
        pub fn write_line(inout self: Self, let s: Str);     // total, latching
        pub fn write_str(inout self: Self, let s: Str);      // total, latching
        pub fn write_int(inout self: Self, let v: i64);      // total, latching
        pub fn write_uint(inout self: Self, let v: u64);     // total, latching
        pub fn write_bytes(inout self: Self, let b: Slice[u8]);   // total, latching
        pub fn check(inout self: Self) raises Error;         // surface a latched error
        pub fn clear_error(inout self: Self);
    }
    impl Writer for Stdout { }
    impl Stderr { /* the same five total methods, check, clear_error */ }
    impl Writer for Stderr { }
    pub struct Stdin { }
    impl Stdin {
        pub fn read_line_into(inout self: Self, inout into: Slice[u8]) -> Option[usize] raises Error;
    }
    impl Reader for Stdin { }
    pub enum Error { closed, would_block, interrupted, no_space, invalid_utf8, other }
    ```

    **The five `write_*` methods on `Stdout`/`Stderr` are TOTAL and
    latching**: a failure sets a sticky flag in the stream instead of
    becoming an error value, and `check` or the trait's `flush` surfaces
    it. This is the one place std records a failure rather than returning
    it, and it is deliberate: a per-line error on a standard stream is
    almost never actionable, ch02 Rule 7 forbids a trap for an expected
    condition, and it keeps every `out.write_line("ok");` in the corpus
    legal without a `?`. The FALLIBLE surface is the trait's `write`,
    `write_all` and `flush`, which every generic and `dyn`-typed use goes
    through (ch04 Rule 21: the trait is never a root-capability type). A
    stream's numeric methods take `i64`/`u64` and format in base 10 with
    no locale, no grouping and no padding (Rule 56); floats are not
    formatted by std in v0.1 (Rule 10(f)).
40. **S0040** — `io` buffering and what survives an abort. `Stdout` is
    block-buffered with an internal buffer of `IO_BUF_BYTES` = **8192**
    bytes, or line-buffered when the runtime entry shim reports a terminal;
    `Stderr` is UNBUFFERED, so a diagnostic is on the file descriptor
    before the next statement runs. Guarantees: (a) the runtime flushes
    `Stdout` after `main` returns normally and reports a latched or flush
    error as a non-zero exit status, printing nothing extra to `Stdout`;
    (b) on a TRAP, buffered `Stdout` bytes MAY be lost, because a trap is
    one breakpoint-class instruction that MUST NOT call or allocate (ch02
    Rules 6-7) and therefore cannot flush — a program whose output must
    survive a trap writes to `Stderr` or flushes explicitly; **and no
    `defer`/`errdefer` body runs on that path either** (ch02 Rule 7, ch01
    Rule 23f), so an open `File`, `Conn`, `Listener` or `Child` is
    abandoned to the operating system, nothing is closed, flushed or freed,
    and NO std invariant depends on cleanup after an abnormal
    termination — there is no temporary-file removal, no lock-file release
    and no flush-on-exit promise on the trap path, and none will be added;
    (c) no std operation flushes `Stdout` as a side effect of anything
    else; (d) **the exit-status table is closed**: `0` — `main` returned
    and the final `Stdout` flush succeeded with no latched error; `1` — an
    error left `main` (ch02 Rule 17, which also fixes the one stderr line
    and its format); `2` — `main` returned but the final flush failed or an
    error was latched on `Stdout`, which (a) called "non-zero" and this
    clause pins, keeping it distinct from `1` so that a script can tell
    "the program failed" from "the output did not arrive". A TRAP is in
    neither row: the process dies by the breakpoint instruction (ch02 Rule
    6) and reports through the operating system's signal status, never
    through `1` or `2`. Before `main` runs, the entry shim installs
    `SIG_IGN` for `SIGPIPE`, so a write to a closed pipe surfaces as
    `io.Error.closed` through Rule 39's latching instead of killing the
    process (ch02 Rule 17).
41. **S0041** — `fs`. `fs.Dir` is the rooted capability and there is NO
    ambient current directory:

    ```fors-sig
    pub struct Dir { }          // root capability, opaque
    impl Dir {
        pub fn open_dir(let self: Self, let name: Str) -> Dir raises Error;
        pub fn read_into(let self: Self, let name: Str, inout into: Slice[u8]) -> usize raises Error;
        pub fn write_all(let self: Self, let name: Str, let bytes: Slice[u8]) raises Error;
        pub fn open(let self: Self, let name: Str) -> File raises Error;
        pub fn create(let self: Self, let name: Str) -> File raises Error;
        pub fn metadata(let self: Self, let name: Str) -> Meta raises Error;
        pub fn remove(let self: Self, let name: Str) raises Error;
        pub fn rename(let self: Self, let from: Str, let to: Str) raises Error;
        pub fn entries(let self: Self) -> Entries raises Error;
    }
    pub struct File { }         // linear: close is the only release
    impl File {
        pub fn read_into(inout self: Self, inout into: Slice[u8]) -> usize raises Error;
        pub fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error;
        pub fn len(let self: Self) -> u64 raises Error;
        pub fn close(sink self: Self) raises Error;
    }
    impl Reader for File { }    // io.Reader; orphan rule: local type, foreign trait
    impl Writer for File { }
    pub struct Entries { }      // linear
    impl Entries {
        pub fn next_into(inout self: Self, inout name: Slice[u8]) -> Option[Meta] raises Error;
        pub fn close(sink self: Self);
    }
    pub struct Meta { pub len: u64, pub kind: Kind, pub modified_unix_nanos: i64 }
    pub enum Kind { file, dir, other }
    pub enum Error { not_found, exists, permission, invalid_name, is_dir, not_dir, no_space, would_block, interrupted, other }
    ```

    **Every operation names a single directory ENTRY, never a path**: a
    `name` MUST be non-empty, MUST NOT contain `/` or a NUL byte, and MUST
    NOT be `.` or `..`; a violation raises `Error.invalid_name` BEFORE any
    syscall. Traversal is repeated `open_dir`, which ch04 Rule 7 already
    requires to be downward-only, so the capability a program holds is
    exactly the subtree it was handed and no string can widen it. There is
    no `Path` type, no relative-path resolution and no symlink following in
    v0.1 (Rule 10(h)); `open_dir` MUST NOT traverse a symlink that leaves
    the receiver's subtree. `read_into`/`write_all` need `fs.read` /
    `fs.write` respectively (ch04 Rule 1), and holding a `Dir` grants
    neither by itself. `Entries` is NOT an `Iterator`: its item would have
    to borrow a name buffer (Rule 10(d)), so it takes one.
42. **S0042** — The comptime file read. `fn read_to_string(let path: Str)
    -> Str` in `std.fs` is a COMPTIME-ONLY function, enforced by THIS rule
    and not by a declaration modifier — ch07 has no `comptime fn`, only a
    `comptime` block — so a call to it outside a `comptime` block MUST be a
    compile error naming this rule. It is legal only
    inside a `comptime` block, its `path` MUST be a comptime constant that
    the enclosing module's `inputs { ... };` clause lists (ch04 Rule 13),
    and it takes NO capability value — it reads the build graph, not the
    running process's file system. It is TOTAL: a missing or unreadable
    input is a BUILD error (ch04 Rule 13), not an error value, which is why
    the corpus writes `let data: Str = fs.read_to_string(".config");`
    with no `?`. Calling it outside `comptime` MUST be a compile error, and
    no run-time function of `std.fs` may be reached from `comptime` (ch04
    Rule 12).
43. **S0043** — `net`.

    ```fors-sig
    pub struct Net { }          // root capability, opaque; capability `net`
    impl Net {
        pub fn resolve_into(let self: Self, let host: Str, inout into: Slice[Addr]) -> usize raises Error;
        pub fn connect(let self: Self, let a: Addr) -> Conn raises Error;
        pub fn listen(let self: Self, let a: Addr) -> Listener raises Error;
    }
    pub struct Addr { }         // Copyable
    impl Addr {
        pub fn from_v4(let octets: Array[u8, 4], let port: u16) -> Addr;
        pub fn from_v6(let octets: Array[u8, 16], let port: u16) -> Addr;
        pub fn port_number(let self: Self) -> u16;
    }
    pub struct Conn { }         // linear
    impl Conn {
        pub fn read_into(inout self: Self, inout into: Slice[u8]) -> usize raises Error;
        pub fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error;
        pub fn wait_until(inout self: Self, let deadline: time.Instant) raises TimeoutError;
        pub fn shutdown(sink self: Self) raises Error;
    }
    impl Reader for Conn { }
    impl Writer for Conn { }
    pub struct Listener { }     // linear
    impl Listener {
        pub fn accept(inout self: Self) -> Conn raises Error;
        pub fn close(sink self: Self);
    }
    pub enum Error { refused, unreachable, reset, closed, in_use, invalid_address, would_block, interrupted, other }
    pub enum TimeoutError { timed_out }
    ```

    `net.TimeoutError` exists as its own type because ch02's example
    converts it (`impl ErrorFrom[net.TimeoutError] for app.Error`) and
    because `wait_until`'s only failure IS the deadline (Rule 6b): a
    deadline is not a socket error. `Conn` carries no buffering and no
    timeout state; a read that would block raises `Error.would_block`.
    v0.1 has no TLS, no HTTP and no `net.Client` (Rule 10(i)).
44. **S0044** — `proc`.

    ```fors-sig
    pub struct Exec { }         // root capability, opaque; capability `exec`
    impl Exec {
        pub fn run(let self: Self, let prog: Str, let args: Slice[Str]) -> Child raises Error;
    }
    pub struct Child { }        // linear: wait is the only release
    impl Child {
        pub fn pid(let self: Self) -> u64;
        pub fn wait(sink self: Self) -> i32 raises Error;
    }
    pub enum Error { not_found, permission, invalid_program, no_resources, other }
    pub fn hardware_threads() -> usize;       // Rule 50; no capability
    ```

    `run` passes `args` verbatim with no shell, no `PATH` search and no
    environment inheritance decision of its own: the child's environment is
    the process's, and a program that wants to choose one needs a v0.2
    surface. There are no pipes, no signals and no `fork` in v0.1 (Rule
    10(m)); `prog` is resolved by the operating system exactly as given.
45. **S0045** — `time`. Every operation is TOTAL (Rule 7: `time` has no
    error type).

    ```fors-sig
    pub struct Clock { }        // root capability, opaque; capability `clock`
    impl Clock {
        pub fn now(let self: Self) -> Instant;          // MONOTONIC
        pub fn wall(let self: Self) -> Wall;            // wall clock, may jump
        pub fn sleep(let self: Self, let d: Duration);
    }
    pub struct Instant { pub nanos: u64 }               // monotonic, opaque origin
    pub struct Wall { pub unix_nanos: i64 }             // UTC, no time zone
    pub struct Duration { pub nanos: u64 }
    impl Instant { pub fn since(let self: Self, let earlier: Instant) -> Duration; }
    ```

    `now` is monotonic: it never decreases within a process, is unaffected
    by wall-clock adjustments, and its origin is unspecified, so an
    `Instant` is meaningful only in a difference — which is why the corpus's
    `c.now()` is the timing primitive. `wall` is the only clock that may
    jump backwards, and `Wall` is UTC nanoseconds since the Unix epoch with
    NO time zone, no calendar and no formatting (Rule 10(g)). `since`
    carries `pre earlier.nanos <= self.nanos` and so traps (kind
    `contract`) iff `earlier` is later, because that is a monotonicity
    bug, not a condition.
46. **S0046** — `env`. Every read takes the capability value; nothing is
    ambient.

    ```fors-sig
    pub struct Env { }          // root capability; capability `env`
    impl Env {
        pub fn has(let self: Self, let name: Str) -> bool;
        pub fn get_into(let self: Self, let name: Str, inout into: Slice[u8])
            -> Option[usize] raises Error;
    }
    pub struct Args { }         // root capability; capability `env`
    impl Args {
        pub fn len(let self: Self) -> usize;
        pub fn at(let self: Self, let i: usize) -> Option[Str];
    }
    pub enum Error { too_large, invalid_utf8, other }
    ```

    `get_into` is the caller-buffer form because a growing variant would
    need an allocator and the name would then have two meanings;
    `Option[usize]` distinguishes "not set" (a fact, Rule 6c) from
    `Error.too_large` (the buffer was too small, a cause). Argument and
    variable bytes are validated as UTF-8 (`Error.invalid_utf8`);
    `Args.at(0)` is the program name as the operating system gave it. There
    is no environment mutation (Rule 10(l)) and no locale of any kind
    (Rule 56).
47. **S0047** — `rand`. The entropy source and the deterministic generator
    are DIFFERENT types, and only the first is authority:

    ```fors-sig
    pub struct Rng { }          // root capability, opaque; capability `rng`
    impl Rng {
        pub fn fill(inout self: Self, inout into: Slice[u8]);        // total
        pub fn u64(inout self: Self) -> u64;                         // total
    }
    pub struct Pcg { }          // Copyable; NO capability; reproducible
    impl Pcg {
        pub fn seeded(let seed: u64) -> Pcg;
        pub fn u64(inout self: Self) -> u64;
        pub fn bounded(inout self: Self, let n: u64) -> u64;         // unbiased; pre n > 0 (traps, contract)
        pub fn fill(inout self: Self, inout into: Slice[u8]);
    }
    ```

    **Provenance**: every unpredictable byte in a program traces to a
    `rand.Rng` value, which traces to a `main` parameter and the `rng`
    capability (ch04 Rules 8, 21). `Rng`'s operations are total: the
    runtime entry shim obtains a working entropy source before `main`, or
    the process never starts, so there is no "entropy failed" error value
    to handle. `Pcg` is a pure value with a fixed, documented algorithm and
    no capability: given the same seed it produces the same sequence on
    every target and build mode (ch03's D1), which makes it the generator
    for tests, simulations and property runs. `Pcg` MUST NOT be seeded
    implicitly from entropy, from the clock or from an address; a
    cryptographic program uses `Rng` directly, and std ships NO CSPRNG
    (`Pcg` is documented as non-cryptographic). Writing entropy into a
    `secret`-qualified slice is legal and carries the taint (ch05).
48. **S0048** — `gpu`. v0.1 exposes the device as a capability and nothing
    more: `pub struct Device { }` (capability `gpu`) with
    `fn info(let self: Self) -> Info`, total, and
    `fn sync(inout self: Self) raises Error`;
    `pub struct Info { pub compute_units: u32, pub lanes: u32, pub shared_bytes: usize }`.
    Kernel launch, device allocation and transfers are NOT a std surface in
    v0.1 (Rule 10(n)): the language owns `@device` and the reserved
    `kernel`/`spmd` forms (ch07), and `mem`'s allocators are host
    allocators — a device allocator would need a second brand universe.
49. **S0049** — `ffi`. `std.ffi` is the permitted holder of the sealed
    `ffi` capability (ch04 Rules 2-2b, 9), so it declares `needs { ffi };`
    and is marked `unguaranteed`, and **every module that imports it
    inherits that mark in the audit ledger** (ch04 Rule 9) — importing
    `std.ffi` is a decision a build records, not a convenience. Its shape
    is deliberately tiny:
    `pub struct CStr { }` with
    `fn len(let self: Self) -> usize` (bytes before the NUL),
    `fn to_str(let self: Self) -> scoped(self) Str raises Utf8Error`, and
    `fn from_bytes(let b: Slice[u8]) -> scoped(b) CStr raises Error`
    (the bytes MUST contain a NUL);
    `pub enum Error { not_terminated, interior_nul, other }`.
    Std declares no `extern "c"` function and provides no marshalling: an
    `extern "c"` declaration is the calling module's, its `raises` ban is
    ch02 Rule 13's, and the error mapping is a future chapter's.

### Concurrency and determinism

50. **S0050** — `spawn`, `parallel`, `parallel for`, `simd for` and
    `reduce` are LANGUAGE forms (ch01 Rule 13, ch03 Rules 11-13); std adds
    no scheduler, no task type and no thread handle. What std adds is one
    query — `fn proc.hardware_threads() -> usize`, a hint with no
    capability, the single carve-out from Rule 3, admitted because the
    language's own `parallel` already depends on the runtime knowing it, it
    reveals nothing about the environment beyond the machine's width, and
    it cannot affect anything outside the process — and the deterministic
    reduction surface, which is exactly ch03's `reduce` and its three named
    siblings (`reduce.serial`, `reduce.fast`, `reduce.exact`): std MUST NOT
    wrap them, rename them or provide a parallel `fold`. **v0.1 provides no
    locks, no channels, no condition variables, no thread handles, no
    `join`, no atomics beyond ch01's `atomic[T]`, and no blocking
    primitive** (Rule 10(c)). The reason is plain: structured `spawn` with
    ch01 Rule 13's sendability rule covers the work v0.1 targets without
    any of them; a lock or a channel needs a blocking contract and a
    cancellation story that ch02's no-unwinder, trap-is-abort model has not
    settled; and a channel would need the `iso` handoff to be a library
    type that outlives its block, which ch01 Rule 15 forbids for anything
    brand-mentioning.
51. **S0051** — Which std types are `Shared` (ch01 Rules 21-21d): `Str`,
    `Slice[T]` where `T` is `Shared`, `Layout`, `time.Instant`,
    `time.Wall`, `time.Duration`, `net.Addr`, `rand.Pcg` and every std
    error type — all of them field-wise conforming because they contain no
    interior mutability. **No std container is `Shared`**: `Buffer`, `Vec`,
    `Map`, `String`, `Own[T, A]`, `Block[A]`, every allocator, every
    root-capability type and every type that is linear (ch01 Rules 22, 22a)
    do NOT implement it. Sharing
    one across a task boundary therefore goes through ch01 Rule 13 —
    `imm`, `iso` by `move`, or a structured-`spawn` capture — and never
    through a std wrapper. Std ships no `@unsafe` `Shared` impl (ch01 Rule
    21c).
52. **S0052** — Allocation inside a parallel region. An allocator is not
    `Shared` (Rule 51) and cannot be copied or stored (ch01 Rule 15a), so
    two tasks cannot hold one allocator value: a `parallel` block that
    allocates gives each task its OWN allocator — typically a
    `mem.Fixed[N]` or a `mem.Bump` opened inside the task — or allocates
    before the block and hands each task a disjoint `Slice` (ch01 Rule
    19b's `split_at`). A concurrent, shared-by-many-tasks allocator is not
    in v0.1 (Rule 10(a) and 10(c) between them), and an `inout` capture of
    an enclosing allocator by a structured `spawn` is an exclusivity
    conflict under ch01 Rules 6-7 whenever two tasks do it — which is the
    check that keeps this honest with no new rule.

### The rules std itself obeys

53. **S0053** — No ambient authority, and where the syscalls go. A std
    module's own `needs` is EMPTY unless it is one of the holders this rule
    lists: `std.io`, `std.fs`, `std.net`, `std.proc`, `std.time`,
    `std.rand`, `std.env`, `std.gpu` and `std.mem` declare
    `needs { syscall };`, and `std.ffi` declares `needs { ffi };`. Both are
    SEALED (ch04 Rules 2-2b), so the capability stops at the holder and no
    importer of std inherits it; `std` is a permitted holder package by
    default (ch04 Rule 2b). `std.mem` is in that list because
    `PageAllocator`, `mem.Bump` and `mem.Heap` map pages — and this is
    exactly why allocation is not authority at the USER level: the sealed
    `syscall` capability is spent inside `std.mem`, and a program that
    allocates declares nothing (Rule 17). Every other std module, and every
    submodule of Rule 1 that holds only pure code (`std.mem.vec`,
    `std.mem.hashmap`, `std.mem.text`, `std.mem.seq`, `std.mem.alloc`), declares
    `needs { };`.
54. **S0054** — No hidden allocation. A std function that does not take an
    allocator value (or a receiver that is one) MUST NOT allocate, at any
    depth, ever — including on an error path, for a diagnostic, or to grow
    an internal cache. Std has no lazily initialised global, no interned
    string table, no per-thread scratch buffer and no memoisation. A
    signature is therefore a complete statement of a function's memory
    behaviour: no allocator parameter means no heap traffic.
55. **S0055** — No trap for an expected condition (ch02 Rule 7). Std MUST
    NOT introduce a trap of its own; the only traps reachable through a std
    operation are ch02 Rule 15's, at these sites and no others: `bounds`
    from an out-of-range index — `Buffer`/`Vec` past `len`, `Map` at an
    absent key, `Str.at` (Rules 23-26); `contract` from a `pre` std
    declares — `copy_from`'s unequal lengths and `split_at`'s `mid` (Rule
    28), `Counting.assert_empty` (Rule 21), `Vec.swap_remove`'s index
    (Rule 24), `Str.slice`'s endpoints and `push_scalar`'s headroom (Rule
    26), `Instant.since`'s reversed arguments (Rule 45), `Pcg.bounded(0)`
    (Rule 47), and `clear`/`deinit` of a non-empty container of a linear
    element type (Rule 11c); `arena-generation` from a stale `Ref` (ch01
    Rule 17); `empty-reduce` from `reduce` (ch03 Rule 11a). Every one of
    these is a bug in the caller, and every `contract` trap is a `pre`
    the signature shows. Everything a correct caller can meet —
    a missing file, a closed socket, exhausted memory, invalid UTF-8, a
    deadline — is an error value or an `Option`.
56. **S0056** — No dependence on locale or environment. No std operation's
    result depends on any ambient setting: integer formatting is base 10,
    ASCII digits, no grouping, no locale (Rule 39); text comparison is
    byte-wise, with no case folding, normalisation or collation (Rule 26);
    `Wall` is UTC nanoseconds with no time zone (Rule 45); path handling
    has no current directory (Rule 41); no std function reads an
    environment variable — a program that wants one passes `env.Env`
    (Rule 46). Where an operation genuinely needs ambient information, the
    capability value is the only channel, and this chapter names it in the
    signature.
57. **S0057** — The audit. Every claim above is mechanically checkable and
    MUST be checked by `fors audit` once std is source: no std signature
    outside Rule 38's list mentions a root-capability type it did not
    receive; no std function allocates without an allocator parameter (Rule
    54); no std module declares a capability outside Rule 53's list; every
    `@unsafe` declaration in std appears in the published inventory (ch04
    Rule 9) and Rule 28's slice primitives are the only ones that hand out
    a `Slice` over non-`Array` storage; every fallible std operation raises
    exactly one of Rule 7's types. A std change that breaks one of these is
    a spec change, not an implementation change.

## Examples

```fors
module hello;
needs { io.stdout };
use std.io;

fn main(inout out: io.Stdout) {
    out.write_line("hello");        // total and latching, Rule 39
}
```

```fors
module app.words;
needs { io.stdout };
use std.io, std.mem;

// The heap arrives as a main parameter and names its own brand, Rule 17.
fn main(inout out: io.Stdout, inout heap: mem.Heap) raises AllocError {
    var v: Vec[i32, heap] = Vec.new();      // allocates nothing yet, Rule 24
    defer v.deinit(&heap);                  // linear: consumed on EVERY exit
    v.push(&heap, 1)?;                      // including this `?`'s error exit
    v.push(&heap, 2)?;
    for x in v.iter() {                     // copies, Rule 33(a)
        out.write_int(x as i64);
        out.write_line("");
    }
    for i in 0 ..< v.len() {                // the only mutating form, Rule 33(c)
        v[i] = v[i] * 2;
    }
    let total: i32 = reduce(+, v.items());  // ch03's tree, the only parallel one
    out.write_int(total as i64);
}                                           // the defer runs here: Rule 11
```

```fors
module app.chain;
needs { };
use std.mem;

fn double(sink x: i32) -> i32 { return x * 2; }
fn small(let x: i32) -> bool { return x < 10; }

// Adaptors are provided methods of `Iterator`, so a chain is ONE
// expression (Rule 34). `v.iter()` is scoped to `v`, and every adaptor's
// declared result type mentions `Self`, so the whole chain stays scoped to
// `v` (ch01 Rule 19c(a)); `count`'s `usize` mentions nothing, so the
// borrow ends at the statement (ch01 Rule 19c(c)).
fn count_small[A: brand](let v: Vec[i32, A]) -> usize {
    return v.iter().map(double).filter(small).take(3).count();
}

// A stage may still be stored: the adaptor types are writable because no
// closure type appears in a signature (Rule 34(1); ch09 Rule 31).
fn staged[A: brand](let v: Vec[i32, A]) -> usize {
    let m: mem.Mapped[mem.SliceIter[i32], i32] = v.iter().map(double);
    return m.take(3).count();
}

// An `inout` iterator is chained through `by_ref`, because every other
// adaptor takes `sink self` and ch01 Rule 4a(d) forbids moving out of an
// `inout` parameter.
fn first_two[I: Iterator](inout it: I) -> usize {
    return it.by_ref().take(2).count();
}
```

```fors
module app.scratch;
needs { };                                  // no capability: allocation is not authority
use std.mem;

fn sum_of(let xs: Slice[i32]) -> i32 raises AllocError {
    with allocator scratch: mem.Fixed[4096] {     // inline storage, Rule 20
        var v: Vec[i32, scratch] = Vec.new();
        defer v.deinit(&scratch);                  // linear: required, Rule 11
        for x in xs {
            v.push(&scratch, x)?;                  // the defer covers this exit
        }
        var acc: i32 = 0;
        for y in v.iter() {
            acc = acc + y;
        }
        return acc;
    }
}
```

```fors
module app.config;
needs { fs.read };
use std.fs, std.mem;

fn load(let d: fs.Dir) -> usize raises fs.Error {
    var buf: Buffer[u8, 4096] = Buffer.empty();    // inline, no allocator, Rule 23
    let n: usize = d.read_into("config.toml", &buf.data[0 ..< 4096])?;
    return n;
}

fn bad(let d: fs.Dir) -> usize raises fs.Error {
    var buf: Buffer[u8, 64] = Buffer.empty();
    return d.read_into("../secrets", &buf.data[0 ..< 64])?;   // Error.invalid_name, Rule 41
}
```

```fors
module app.text;
needs { };
use std.mem;

// Validation and allocation are two calls, never one, Rule 6b.
fn first_word[A: brand, L: Allocator[A]](inout a: L, let bytes: Slice[u8])
    -> String[A] raises Utf8Error
{
    let s: Str = Str.from_utf8(bytes)?;            // the only validating entry
    match s.find(" ") {
        some(let i) => { let head: Str = s.slice(0, i)?; return keep(&a, head); }
        none => { return keep(&a, s); }
    }
}
```

```fors
module app.seed;
needs { rng };
use std.rand;

fn shuffle_seed(inout r: rand.Rng) -> rand.Pcg {
    let s: u64 = r.u64();                   // entropy: total, traces to main, Rule 47
    return rand.Pcg.seeded(s);              // deterministic from here on
}
```

## Rejected alternatives

- **A default/global allocator with an "allocator" parameter as an
  override** (Rust's shape): the owner closed this in round 5 (D5), and it
  would put an ambient, unbranded allocation path under every container,
  defeating PLAN R2's "cannot free with the wrong allocator".
- **Storing the allocator in the container** (Zig's `ArrayList` after
  0.12, C++'s allocator-aware containers): ch01 Rule 15a forbids an
  allocator value in a field, and it would make every container
  brand-mentioning in a second way, with no gain over a parameter.
- **A `dyn Allocator`** so that containers are not generic over `L`: ch01
  Rule 15(b) forbids converting a brand-mentioning type to an erased form,
  and dynamic dispatch would reintroduce the wrong-allocator free.
- **A joint error type** (`std.Error`) so that operations may both
  allocate and validate: it would hide which mode fired, and one `raises`
  type per operation is achievable by splitting the operation (Rule 6b).
- **`Option[T]` for allocation failure**, or a trapping allocation
  variant: owner decision (3) — a failed allocation is an error value.
- **Fallible `write_line` on the standard streams**: 23 accepted run-ok
  tests call it with no `?`, ch02 Rule 1 requires one on a `raises` call,
  and a trap is forbidden for an expected condition — a latching writer is
  the only shape that satisfies all three.
- **An `iter_mut`** returning borrows: `Iterator.Item` is a plain
  associated type (ch09 Rule 21) with nowhere to put the scope.
- **Adaptors as methods taking `sink self` and holding the source by
  value** (the first draft's shape): unwritable, because `it.map(f)`
  needs a method on the language-known `Iterator` (ch09 Rule 43 has no
  free-function method syntax), and unsound, because storing a scoped
  `v.iter()` in the adaptor's field is exactly what ch01 Rule 19a
  forbids — the borrow of `v` would end while the adaptor lived.
- **`Own.get -> scoped(self) T` and `Map.at -> scoped(self) V`**: a call
  result is a value, not a place, so for a non-`Copyable` payload these
  minted a second owner; the place form `m[k]` and the exchange form
  `replace` are what the frozen language can keep single-owned.
- **A `collect()` that returns a fresh container**: it would have to
  allocate ambiently; `try_collect_into` names its destination.
- **A `Path` type with `..` and absolute paths**: it would let a string
  widen a capability, which is the one thing ch04 Rule 7's downward-only
  narrowing exists to prevent.
- **Locks and channels in v0.1**: see Rule 50's reasons.
- **A `Buffer[T]` with a runtime capacity**: not implementable without an
  allocator, and every corpus site has no allocator in scope.

## Decisions made while drafting

1. **Ten modules, no additions.** The allocator interface, the adaptors,
   the containers and the text types are declared in submodules of
   `std.mem` (`std.mem.alloc`, `std.mem.vec`, `std.mem.hashmap`,
   `std.mem.text`, `std.mem.seq`) and re-exported item-wise, so
   `STD_MODULES` needs no change and no user ever names a submodule. The
   cost is that `String`'s defining module is `std.mem.text` rather than a
   `std.text`; the benefit is that the compiler's synthetic table stays
   exactly as ch08 Rule 17 froze it.
2. **Eight prelude additions, each earned by a corpus site or by symmetry**
   (Rule 2). This settles the type half of ch08 Open question 1: `Buffer`,
   `Vec` and `PageAllocator` go IN the prelude rather than behind `use
   std.mem;`, because every site that uses them today is a module with no
   header imports, and requiring the import would turn accepted tests into
   defects for no gain.
3. **The heap's brand is named by `main`'s parameter** (Rule 17), which
   makes `fn main(inout heap: mem.Heap)` behave exactly like a `with
   allocator heap:` header without making `main` generic. The alternative —
   a brand parameter on `main` — is forbidden by ch04 Rule 8.
4. **`write_line` is total and latching** (Rule 39); the fallible surface
   is `io.Writer`. This is the only place std stores a failure instead of
   returning it, and it is what keeps the 23 run-ok tests valid.
5. **`Buffer` gains a const-generic capacity** (`Buffer[T, N]`, Rule 23).
   No one-parameter form is implementable under D5. Recorded as corpus
   defect D-1 with the exact fixes.
6. **Every allocating operation raises `AllocError`**, including
   `Allocator.create` and `Arena.alloc`. ch01's examples and two
   `parse-ok` tests write `heap.create(n)` and `nodes.alloc(...)` with no
   `?`; that is corpus defect D-2 (a one-character fix per site) rather
   than a reason to make allocation infallible.
7. **Operations are split so that each has ONE failure mode** (Rule 6b):
   `Str.from_utf8` validates, `String.from_str` allocates. This is the
   structural consequence of `raises` taking one type.
8. **Std's slice accessors are `@unsafe` declarations** (Rule 28), the
   shape ch01 Rule 19b already set for `split_at`, rather than a new
   `Slice` constructor. ch03 Rule 24 needs one clause to say so.
9. **No consuming iterator for allocator-backed containers**, because the
   iterator cannot hold the allocator it would need when the loop drops it
   (Rule 10(e)). `Buffer` and `Array` keep `into_iter`.
10. **`mem.Fixed[N]` and `mem.Counting[N]` are const-generic and inline**,
    not "over a caller-owned slice" and not wrappers, because
    `with_stmt` takes a type and no arguments and ch01 Rule 15a forbids
    both a constructor and a stored parent (Rules 20-21).
11. **`fs` names entries, not paths** (Rule 41): a capability that a string
    could widen is not a capability.
12. **`rand` splits entropy from reproducibility** (Rule 47): `Rng` is
    authority and total, `Pcg` is a pure value with no capability.
13. **`time.Clock.now` is monotonic** and `wall` is the separate,
    jump-prone clock (Rule 45), matching the corpus's `c.now()`.
14. **`MEM_MAX_ALIGN` = 16 and `IO_BUF_BYTES` = 8192** until measured
    (ch06 owns measurement); both are named constants of this chapter.
15. **`std.mem` holds the sealed `syscall` capability** (Rule 53). This is
    the mechanism that makes "allocation is not authority" true for user
    code without making it false for the implementation.
16. **Adaptors and consumers are PROVIDED METHODS of `Iterator`** (Rules
    34-35), and the ownership rule that makes them writable is ch01 Rule
    19c. Round 6 (owner decision O3, 2026-09-20) DISPROVED the earlier
    conclusion of this decision — "`Iterator` is language-known and nothing
    in the frozen language lets std put a method on it" — on its stated
    ground: ch09 Rule 43 tier (2) already finds a PROVIDED method of a
    prelude trait for a concrete, a rigid and an adaptor receiver, ch09
    Rule 38(b) already binds `Self` before any argument is visited, and
    each adaptor's `impl Iterator` is struct-headed, so no blanket impl is
    involved. The real obstacle was OWNERSHIP, which the old rule worked
    around rather than named: a `sink self` adaptor stores a SCOPED
    `v.iter()` in a field, and nothing said what the caller may conclude
    about the result. ch01 Rule 19c says it — the result inherits the
    argument's extent iff the declared result type mentions the parameter
    the argument went into — so `v.iter().map(f)` is scoped to `v` and the
    field store inside the generic body is not the caller's concern. The
    free functions `mem.map`, `mem.filter`, `mem.take`, `mem.skip`,
    `mem.enumerate`, `mem.zip`, `mem.count`, `mem.fold`, `mem.for_each`,
    `mem.all`, `mem.any`, `mem.find`, `mem.try_fold` and
    `mem.try_for_each` are DELETED; `mem.iter` and
    `mem.try_collect_into` stay free functions. `by_ref` is added as the
    seventh adaptor and the one remaining raw pointer in `seq`; `chain` is
    still dropped (no type-equality constraint); `zip` now owns both
    sources, and a result with two scoped sources keeps both (ch01 Rule
    19c(d)) — legal as a local, unreturnable by ch01 Rule 19 — instead of
    the signature deciding. The round-6 verification added `U: Droppable`
    to `map`/`Mapped` (ch09 Rules 17, 21) and `T: Droppable` to
    `BufferIter`'s impl (Rule 23).
17. **A non-`Copyable` payload is never returned by value from a view**
    (round-6 verification): `Own.get`/`set` need `T: Copyable`, `Own.replace`
    exchanges, `Allocator.deinit` returns the payload (Rules 12, 22), and
    `Map`'s value access is the place `m[k]` through `Index`/`IndexMut`
    (Rule 25), never an `at` method. `Buffer.push` returns the value when
    full (Rule 23). Each closes a second-owner hole ch01 Rule 4a(c) could
    not see through a call result.
18. **`std.mem` has five submodules and an acyclic import graph** (Rule 1):
    `alloc` (the interface) and `seq` (iteration) are leaves, `vec`,
    `hashmap` and `text` import only them, and `std.mem` imports all five
    and re-exports their items ITEM-WISE — a `pub use std.mem.vec;` would
    re-export the module name, and a submodule that imported `std.mem`
    would close a cycle (ch08 Rules 5, 7). `hashmap` is so named because
    `std.mem.map` would be ambiguous with the re-exported function `map`
    (ch08 Rule 4). Every `use` inside std is absolute (`use std.io;`).
19. **Every std trap is either `bounds` from an index or `contract` from a
    `pre` the signature shows** (Rule 55): `Instant.since`, `Pcg.bounded`,
    `Str.slice` and `push_scalar` carry a `pre`, so their kind is
    `contract`, not `overflow`/`div-zero`/`bounds`; after round 6 the only
    trap left from Rule 11c is `deinit_empty`'s `len() == 0`, the rest
    having become static (ch01 Rule 22b and the `T: Droppable` impl
    blocks).

20. **Linearity is a language rule, not a std promise** (round 6, O1;
    Rule 11). Std declares `impl Linear` for nine types and lists the
    consuming methods; everything else — what an obligation is, what
    discharges it, what happens in a container, a closure, a `spawn` or a
    `with` block, and the diagnostic — is ch01 Rules 22-22i. The knock-on
    surface change is that `clear` and `deinit` DROP elements and therefore
    live in `T: Droppable` impl blocks (Rules 23-26), with `deinit_empty`
    plus a `pre` for the linear-element case. `Vec`, `Map` and `String` are
    linear ALWAYS, not "while cap > 0": linearity is a fact of the
    constructor, and `deinit` on an empty container is total and free.
21. **Cleanup is written with `defer`/`errdefer`** (round 6, O2; ch01
    Rules 23-23f). Every std body that lets a linear value live across a
    `?` uses `errdefer`; every example in this chapter that creates a
    container now attaches its release once, at the creation site. Nothing
    of std's shape depends on the abnormal path, because a trap runs no
    deferred body (Rule 40(b), ch02 Rule 7).
22a. **`Allocator.create` gains `T: Droppable`** (round 6, implementation
    stage; ch01 Rule 22c, ch09 Rule 57). Its provided body holds the `sink
    v: T` payload across `self.alloc(...)?`, so the error exit drops a
    value of rigid type; without the bound the trait's own body would be
    rejected, and no `errdefer` can help, since a rigid `T` has no
    consumer to name. `deinit` keeps no bound: it RETURNS the payload, so a
    linear `Own` is still releasable. An `Own` of a linear payload is
    constructed through `alloc` plus `own_raw` (Rule 28), where the caller
    holds the payload across the fallible step and can consume it on the
    failure path itself.
22b. **The resolver treats a prelude-named declaration inside package
    `std` as the DEFINITION of that name** (round 6, implementation stage;
    Rule 32, ch08 Rule 13's same-entity case). `std.mem.seq` must be able
    to declare `pub trait Iterator`, since the provided methods of Rules
    34-35 live in its body, and outside `std` the same declaration stays
    the ordinary N0013 collision. This is the name-resolution counterpart
    of round 5's package-aware orphan rule, which already let an `impl` of
    a prelude type live in `std`.
22. **`main`'s raised error is ch02 Rule 17** (round 6, O4), and this
    chapter owns only the observable ordering and the exit-status table
    (Rule 40(d)): flush `Stdout`, one `error: ` line on unbuffered stderr,
    status 1; status 2 for a failed final flush or a latched `Stdout`
    error; a trap in neither row. Open question 5 is closed.

## Corpus and spec defects this chapter creates

Every std name found in the corpus and in the other chapters, and whether
this chapter defines it compatibly. A `parse-ok` test asserts nothing about
the checker (tests/conformance/README.md), so a signature change breaks one
only if it changes the file's PARSE.

| Name | Where used | Status |
|---|---|---|
| `io.Stdout`, `io.stdout` | ch04 example; 63 sites, 20 run-ok tests | defined, compatible (Rule 39) |
| `io.Stderr`, `io.Stdin`, `io.Writer`, `io.Reader`, `io.Error` | ch04 R21, 6 sites | defined, compatible |
| `io.Missing` | 08-names `use-std-module-backed-by-source-rejected` | intentionally absent: the test needs a name std does NOT export |
| `write_line` with no `?` | 23 run-ok tests | compatible BY DESIGN (Rule 39) |
| `fs.Dir`, `fs.Error`, `read_into` | ch02 example, ch04 R21, 15 sites | defined, compatible (Rule 41) |
| `fs.read_to_string` | 2 comptime tests | defined, compatible: comptime-only and total (Rule 42) |
| `net.Net`, `net.Error`, `net.TimeoutError` | ch02, ch04 examples | defined, compatible (Rule 43) |
| `net.Client`, `get_into` | ch02 example, ch04 example | **defect D-3**: not in v0.1 (Rule 10(i)); both examples need a `net.Conn` + `read_into` shape. ch04's is fixed by this chapter's own edit; ch02's needs its owner. |
| `time.Clock`, `c.now()` | ch04 R21, 1 test | defined, compatible (Rule 45) |
| `rand.Rng`, `env.Env`, `env.Args`, `proc.Exec`, `gpu.Device` | ch04 R21, 08-names tests | defined, compatible |
| `mem.Allocator` | ch08 R17 text, 2 tests (`check-ok`) | defined, compatible: the tests assert resolution only |
| `ffi.CStr` | 08-names test | defined, compatible (Rule 49) |
| `Own[T, A]`, `Ref[T, A]`, `Arena[T, A]` | ch01, 50+ sites | surfaced, semantics unchanged (Rules 19, 22) |
| `PageAllocator` | ch01 example, 2 tests | defined, compatible (Rule 18) |
| `heap.create(n)` / `nodes.alloc(v)` with no `?` | ch01 examples, 2 `parse-ok` tests | **defect D-2**: allocation raises (Rule 6d); add `?` and a `raises AllocError` to the enclosing signature. Parse is unaffected; `with-allocator-brand-mismatch-rejected` (`check-error`) gains a second diagnostic until fixed. |
| `Buffer[u8]`, `Buffer[i64]`, `Buffer.fixed(n)` | ch02 example, ch04 example, 5 tests | **defect D-1**: `Buffer[T, N]` (Rule 23). Fixes: `Buffer[u8, 4096]`/`Buffer[i64, 4]` and `Buffer.empty()`. `02-failure/trap-bounds.fors` also needs `buf[10] = 1` for `buf.slice[10] = 1` (a `Slice` field is impossible, ch01 R19a); it is a `trap` test, so this one is load-bearing. |
| `self.data[i]`, `self.len` | ch02 example | compatible: both are `pub` fields (Rule 23) |
| `Vec[i32]`, `Map[i32, i32]` | 2 `parse-ok` tests | compatible: `Vec[T, A]`/`Map[K, V, A]` change no parse, and neither test is checked |
| `Str`, `s.slice(0, n)` with `else \|e\|` | ch02 example, 47 sites | defined, compatible (Rule 26): `slice` raises `Utf8Error` |
| `Slice[T]`, `split_at` | ch01, ch03, 103 sites | compatible (Rule 28) |
| `Option`, `some`, `none` | 123 sites | unchanged (Rule 27) |
| `SVec[T]` | ch03 R20, 3 tests | untouched: reserved, not a std type |

## Edits this chapter makes elsewhere

- `docs/spec/04-authority.md` Rule 21: `mem.Heap` added to the
  root-capability list with NO capability, the count "eleven" becomes
  "twelve" (Rules 7, 8, 21 and the Definitions line), the reserved
  paragraph replaced by a pointer to Rule 17 here; the `hello` example's
  `write_line` loses its `?` and the `fetch` example takes
  `Buffer[u8, 4096]` and `net.Conn.read_into` (defect D-3).
- `docs/spec/08-names.md` Rule 17: the eight prelude additions of Rule 2,
  and Open question 1 closed.
- `docs/spec/README.md`: chapter 10 in the chapter list and the fact table,
  the root-capability count, and the round-5 D5 line marked implemented.
- Round 6 (2026-09-20): `docs/spec/01-ownership.md` gains Rules 19c and
  22-22i (linearity, which Rule 11 here now only lists) and 23-23f
  (`defer`/`errdefer`); `docs/spec/07-grammar.md` gains the two
  productions and reserves both words; `docs/spec/02-failure.md` gains
  Rule 16 (error exit) and Rule 17 (`main`'s raised error), which Rule
  40(d) here cites; `docs/spec/04-authority.md` Rule 8 gains one sentence
  pointing at ch02 Rule 17; `docs/spec/09-types.md` amends Rules 10(c),
  11, 21, 23, 24, 31, 33, 43, 50 and 57. The corpus stage migrates the
  files listed under "What round 6 forbids" in ch01 and the `*-accepted`
  tests named below; the std stage rewrites `std/mem/seq.fors` to Rules
  32-35, `std/mem/vec.fors` and `std/mem/hashmap.fors` to Rules 23-26,
  `std/mem/alloc.fors` with `impl Linear for Block[A] {}`, and
  `std/fs`, `std/net`, `std/proc` with their `impl Linear` declarations
  and an `errdefer` on every body that holds a linear value across a `?`.

## Open questions for the owner

1. **`Buffer`'s shape** (Rule 23, defect D-1). Recommendation: the
   const-generic inline form `Buffer[T, N]`. The alternative,
   `Buffer[T, A]` backed by an allocator, costs the same five corpus sites
   AND forces an allocator into `needs { };` modules that have none. No
   one-parameter form exists under D5.
2. **Two one-clause edits this chapter needs in frozen chapters.**
   (a) ch01 Rule 15/15a: an allocator value also originates as a `main`
   parameter of type `mem.Heap`, whose binding names a fresh brand (Rule
   17). (b) ch03 Rule 24: "no other constructor for `Slice[T]`" excepting
   ch10 Rule 28's `@unsafe` std primitives, as ch01 Rule 19b already
   words it. Recommendation: make both, as editorial clarifications.
   ~~A third, larger one: ch01 needs the linearity rule of Rule 11.~~
   CLOSED by owner decision 2026-09-20, round 6 (O1): ch01 Rules 22-22i
   are that rule, with `Linear` and `Droppable` as prelude markers and no
   new keyword; Rule 11 here is now the list of std's nine `impl Linear`
   types and their consuming methods.
3. **Should `with_stmt` take arguments in v0.2** (`with allocator f:
   mem.Fixed(&storage) { }`)? It would give a fixed-buffer allocator over
   caller-owned memory and a counting allocator that really wraps a
   parent. Recommendation: not in v0.1 (the grammar is frozen); revisit
   with a v0.2 grammar round.
4. **No dereference operator and no reference type** (Rule 22). A
   `Copyable` payload of `Own[T, A]` is copied by `get`/`set`; any other
   is reached only by `replace` or `deinit`, because a method cannot
   return a view of a non-`Copyable` value without creating a second
   owner. Recommendation: keep this for v0.1 rather than adding `*`, an
   `Index[()]` hack or a reference type; revisit if `Own` of a
   non-`Copyable` payload becomes common in the corpus.
5. ~~**`main`'s result and `raises`.** What does the runtime do with a
   raised error — exit code, message, and on which stream?~~ CLOSED by
   owner decision 2026-09-20, round 6 (O4), exactly as recommended: ch02
   Rule 17 owns the semantics and the line format (`error: ` +
   `render(e)`, one line, unbuffered stderr, status 1, a failed stderr
   write ignored, `SIGPIPE` ignored by the entry shim), ch04 Rule 8 carries
   one pointing sentence, and Rule 40(d) here carries the exit-status
   table.
6. **Which capability does `mem.Heap` need in `needs`?** This chapter says
   none (D5). Confirm that `fors audit` should still REPORT heap arrival,
   so a reviewer can see which programs allocate, even though it is not
   authority. Recommendation: yes, report, do not require.
7. **`Map`'s default seed** (Rule 25). A fixed seed is deterministic and
   hash-floodable; a random one needs entropy the map cannot obtain.
   Recommendation: fixed by default, `seeded` for the programs that face
   untrusted keys, and a documented warning.
8. **`proc.hardware_threads` as the one ambient read** (Rule 50).
   Recommendation: accept; the alternative is to hang it off `proc.Exec`
   and make a thread count cost the `exec` capability.
9. **Formatting.** v0.1 has integer formatting on the streams and nothing
   else — no floats, no padding, no width, no dynamic format strings
   (Rule 10(f)). Recommendation: confirm for v0.1; a typed `fmt` surface
   is a v0.2 chapter.
10. **Freestanding std.** `mem.Fixed[N]` and the pure submodules need no
    syscall, so a subset of std works with no operating system.
    Recommendation: name that subset in v0.2 and let the manifest select
    it; do not split std now.

## Conformance tests

All in `tests/conformance/10-std/`; each cites its rule as `10.Sk`. A
`detail` starts with the expected code (`S00nn`), an `N00nn` (ch08) or
`T00nn` (ch09) where another chapter's rule decides; text after ` -- ` is
comment.

R1 `std-submodule-not-importable-rejected`, `std-unknown-module-rejected`;
R2 `prelude-vec-without-import-accepted`, `prelude-buffer-without-import-accepted`,
`prelude-page-allocator-without-import-accepted`,
`prelude-alloc-error-without-import-accepted`,
`prelude-name-and-mem-path-same-entity-accepted`,
`item-named-as-std-prelude-addition-rejected`;
R3 `std-fn-without-capability-value-rejected`;
R4 `sink-self-deinit-implicit-move-accepted`, `deinit-then-use-rejected`,
`set-self-in-std-rejected`;
R5 `into-form-allocates-nothing-accepted`;
R6 `alloc-failure-is-error-value-accepted`, `alloc-failure-not-trap-run-ok`,
`alloc-without-question-rejected`,
`option-not-used-for-failure-rejected`,
`two-failure-modes-in-one-call-rejected`;
R7 `error-enum-is-copyable-accepted`, `std-ships-no-error-from-rejected`;
R8 `raises-callable-to-pure-adaptor-rejected`, `try-fold-propagates-accepted`;
R9 `std-type-layout-not-guaranteed-rejected`;
R10 `result-type-absent-rejected`, `iter-mut-absent-rejected`,
`vec-into-iter-absent-rejected`, `lock-absent-rejected`,
`path-type-absent-rejected`, `char-literal-absent-rejected`;
R11 `own-dropped-without-deinit-rejected`, `vec-dropped-without-deinit-rejected`,
`file-dropped-without-close-rejected`, `discard-linear-rejected`,
`linear-moved-to-caller-accepted`, `linear-element-container-deinit-trap`;
R12 `allocator-trait-impl-complete-accepted`,
`allocator-as-dyn-rejected`, `allocator-stored-in-field-rejected`;
R13 `layout-align-not-power-of-two-rejected`,
`layout-array-overflow-raises-run-ok`, `alloc-zeroed-is-zero-run-ok`;
R14 `grow-invalidates-slice-rejected`, `grow-failure-keeps-block-accepted`;
R15 `block-not-copyable-rejected`, `block-bytes-raw-is-unsafe-accepted`;
R16 `free-wrong-brand-rejected`, `free-brand-laundering-rejected`,
`free-is-total-accepted`, `double-free-rejected`;
R17 `main-heap-parameter-accepted`, `main-heap-needs-entry-rejected`,
`heap-brand-named-by-parameter-accepted`, `heap-brand-mismatch-rejected`,
`heap-stored-in-field-rejected`, `main-heap-twice-rejected`;
R18 `with-page-allocator-no-capability-accepted`;
R19 `bump-reset-kills-blocks-rejected`, `arena-ref-versus-bump-accepted`;
R20 `fixed-allocator-exhausted-raises-run-ok`,
`fixed-allocator-in-needs-empty-module-accepted`;
R21 `counting-assert-empty-trap`, `counting-bytes-live-run-ok`;
R22 `own-get-scoped-escape-rejected`;
R23 `buffer-one-type-argument-rejected`, `buffer-index-past-len-trap`,
`buffer-fields-public-accepted`, `buffer-into-iter-accepted`,
`buffer-in-module-without-allocator-accepted`;
R24 `vec-push-wrong-brand-allocator-rejected`, `vec-new-in-synth-position-rejected`,
`vec-items-is-unsafe-accepted`, `vec-growth-schedule-run-ok`;
R25 `map-get-non-copyable-value-rejected`, `map-at-absent-trap`,
`map-insert-returns-old-run-ok`, `map-fixed-seed-deterministic-run-ok`;
R26 `str-slice-non-boundary-raises-run-ok`, `str-slice-out-of-range-trap`,
`str-index-is-bytes-run-ok`, `string-from-utf8-split-accepted`,
`str-literal-not-scoped-accepted`, `str-from-string-scoped-rejected`;
R27 `option-unwrap-absent-rejected`;
R28 `slice-from-vec-needs-unsafe-rejected`, `slice-copy-from-length-trap`,
`slice-fill-accepted`;
R29 `hash-for-float-rejected`;
R30 `allocator-not-copyable-rejected`, `buffer-copyable-iff-element-accepted`;
R31 `sort-is-deterministic-run-ok`, `try-sort-by-propagates-accepted`;
R32 `iterator-next-raises-rejected`;
R33 `iter-yields-copies-accepted`, `iter-while-mutating-rejected`,
`iter-mut-not-provided-rejected`, `index-loop-mutates-accepted`;
R34 `adaptor-chain-accepted`, `adaptor-with-raising-closure-rejected`,
`adaptor-does-not-allocate-accepted`;
R35 `try-for-each-error-propagates-run-ok`,
`try-collect-into-needs-allocator-rejected`;
R36 `for-over-items-accepted`, `for-over-iter-accepted`,
`for-moves-named-iterator-rejected`;
R37 `fold-is-left-to-right-run-ok`, `reduce-is-the-only-parallel-accepted`;
R38 `capability-value-required-rejected`, `needs-and-use-both-required-rejected`;
R39 `write-line-without-question-accepted-run-ok`,
`writer-flush-requires-question-rejected`, `stdout-check-surfaces-error-accepted`,
`write-int-base-ten-run-ok`;
R40 `stderr-unbuffered-before-trap-run-ok`, `stdout-lost-on-trap-trap`,
`flush-after-main-run-ok`;
R41 `fs-name-with-slash-rejected-run-ok`, `fs-name-dotdot-invalid-run-ok`,
`fs-open-dir-downward-only-accepted`, `fs-file-not-closed-rejected`,
`fs-entries-not-iterator-accepted`, `fs-read-needs-capability-rejected`;
R42 `fs-read-to-string-outside-comptime-rejected`,
`fs-read-to-string-undeclared-input-rejected`;
R43 `net-conn-not-shutdown-rejected`, `net-timeout-error-from-accepted`,
`net-client-absent-rejected`;
R44 `proc-child-not-waited-rejected`, `proc-run-needs-exec-rejected`;
R45 `time-now-is-monotonic-run-ok`, `time-since-reversed-trap`,
`time-wall-has-no-zone-accepted`;
R46 `env-get-into-not-set-run-ok`, `env-get-into-too-small-run-ok`,
`env-mutation-absent-rejected`;
R47 `rand-pcg-reproducible-run-ok`, `rand-pcg-needs-no-capability-accepted`,
`rand-rng-needs-capability-rejected`, `rand-bounded-zero-trap`,
`rand-fill-into-secret-accepted`;
R48 `gpu-info-total-accepted`, `gpu-kernel-launch-absent-rejected`;
R49 `ffi-import-taints-module-rejected`, `ffi-cstr-to-str-raises-accepted`;
R50 `hardware-threads-no-capability-accepted`, `channel-absent-rejected`,
`parallel-fold-absent-rejected`;
R51 `vec-not-shared-rejected`, `str-shared-accepted`,
`allocator-not-shared-rejected`, `own-sent-to-unstructured-task-rejected`;
R52 `two-tasks-one-allocator-rejected`, `per-task-fixed-allocator-accepted`;
R53 `std-module-syscall-sealed-accepted`, `importer-of-std-mem-has-no-syscall-accepted`;
R54 `std-fn-without-allocator-allocates-rejected`;
R55 `std-introduces-no-new-trap-kind-rejected`;
R56 `formatting-has-no-locale-run-ok`, `text-compare-is-bytewise-run-ok`;
R57 `audit-finds-unlisted-unsafe-slice-rejected`.

Round 6 additions (2026-09-20), all in `tests/conformance/10-std/`:

R11 `vec-dropped-without-deinit-rejected` (ch01 R22h; the `detail` names
`Vec.deinit`), `vec-dropped-at-question-rejected`,
`vec-consumed-by-defer-accepted`, `vec-consumed-by-errdefer-then-returned-accepted`,
`vec-errdefer-normal-exit-unconsumed-rejected`,
`own-dropped-without-deinit-rejected`, `string-dropped-rejected`,
`file-not-closed-rejected`, `entries-not-closed-rejected`,
`conn-not-shutdown-at-question-rejected`, `child-not-waited-at-question-rejected`,
`linear-discard-rejected` (ch01 R22d), `linear-in-user-struct-inherits-rejected`.
R11c `linear-buffer-element-rejected` (ch09 R11),
`linear-array-field-in-buffer-rejected`,
`vec-clear-linear-element-rejected` (no `clear` in the unbounded block),
`vec-deinit-linear-element-rejected`,
`map-deinit-linear-value-rejected`,
`vec-deinit-empty-nonempty-trap` (`contract`),
`vec-linear-element-pop-then-deinit-empty-accepted`,
`vec-linear-always-empty-deinit-accepted`.
R32 `iterator-impl-linear-self-rejected`, `iterator-impl-linear-item-rejected`,
`std-iterator-inherent-name-clash-rejected` (an inherent `take` on a std
iterator type), `iterator-next-not-raises-rejected`.
R33 `container-of-linear-not-iterated-by-value-rejected`,
`scoped-iter-chain-keeps-borrow-rejected` (mutating `v` while a chain
derived from `v.iter()` is live).
R34 `adaptor-chain-method-accepted` (three stages, fn items),
`adaptor-chain-closure-accepted`, `adaptor-chain-rigid-receiver-accepted`,
`adaptor-annotated-binding-accepted`
(`mem.Taken[mem.Mapped[mem.SliceIter[i32], i32]]`),
`adaptor-stored-then-chained-accepted`,
`adaptor-on-inout-receiver-rejected` (ch01 R4a(d)),
`adaptor-by-ref-on-inout-accepted`,
`adaptor-on-field-receiver-rejected` (ch01 R4a(c)),
`adaptor-by-ref-on-field-accepted`,
`adaptor-chain-across-question-accepted`,
`adaptor-chain-as-for-iterable-accepted`,
`adaptor-by-ref-for-then-reuse-accepted`,
`zip-two-scoped-sources-rejected` (ch01 R19c(d), R19: returned under `scoped(v)`),
`zip-two-scoped-sources-local-accepted` (ch01 R19c(d)),
`zip-scoped-and-owned-accepted`,
`free-function-adaptor-absent-rejected` (`mem.map` is gone),
`adaptor-with-raising-closure-rejected`,
`chain-adaptor-absent-rejected`.
R35 `consumer-count-method-accepted`, `consumer-fold-method-accepted`,
`try-fold-method-accepted`, `try-for-each-method-accepted`,
`free-function-consumer-absent-rejected` (`mem.count` is gone),
`consumer-count-drops-items-accepted` (a non-`Copyable`, non-linear
`Item`), `try-collect-into-is-free-function-accepted`.
R40 `main-raises-exit-status-one-run-error` (ch02 R17),
`main-returns-latched-stdout-exit-2`,
`defer-not-run-on-trap` (`trap`; the marker goes to `Stderr`),
`sigpipe-ignored-write-latches-run-ok`.

Count: **57 rules (S0001-S0057, with sub-rules S0006a-d and S0011c), 159 test names from rounds 1-5 plus 55 from round 6, of which 82 have files (`tests/conformance/10-std/README.md` splits present from pending).**
