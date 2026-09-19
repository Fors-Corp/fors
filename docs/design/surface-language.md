# Fors design: surface-language

> **Status: design-panel draft, 2026-09-19.** Produced by one subsystem architect working alone. Where this conflicts with `docs/PLAN.md` (section 4, Resolutions), PLAN.md wins. Cross-design conflicts are catalogued in `reviews.md`.

## Summary

Fors is a braces-and-keywords, statically-typed systems language whose entire surface is engineered around one hard constraint: the grammar must be parseable to a complete CST with no symbol table, no backtracking and no type information, so parsing is embarrassingly parallel per file and error recovery is line-local. Generic parameters are declared in `[...]` and applied in `[...]`; in expression position `expr[args]` is a single `Bracket` node that the checker resolves to index-or-instantiate, which removes the `<` ambiguity and the turbofish at once. The type system is definition-site-checked traits plus shape-based lowering, with `@specialize` as the explicit monomorphization opt-in — the honest cost is an indirect call on hot generic kernels, which is why numeric combinators in std are specialized by hand. Aliasing is expressed by parameter conventions (`let`/`inout`/`sink`/`set`) with visible call-site markers (`&x`, `move x`, `&out x`), giving noalias-grade facts from a local check and no lifetime annotations. The reference-capability lattice is collapsed from Pony's six to exactly three type qualifiers — `iso`, `imm`, `secret` — because conventions already cover exclusive-mutable and read-only; this is the largest ergonomic win in the design. There is no function overloading, no user-defined operators and no implicit numeric conversion; operator resolution is a single lookup keyed on the left operand's type, which is what makes the near-linear type-checker bound defensible. Errors are values (`raises E`, postfix `?`) returned through a documented two-register failure ABI with no unwinding and no landing pads; panics abort. Authority is declared per module (`needs { ... }`) and narrowed by capability values obtained only from `World` at `main`; the manifest is inert Fors data literals with per-dependency capability assertions that fail the build on a silent capability gain in a patch release. Deliberately absent: classes, exceptions, GC, macros, async/await coloring, lifetimes, variance, and safe stored references — heap edges are `Own[T]` or arena handles, and that hole is named, not hidden.

## Decisions

| Decision | Choice | Rationale | Risk |
|---|---|---|---|
| Syntax family and parse-time context-freedom | Braces + keyword-led declarations + postfix `name: Type`; mandatory `;` statement terminators; no significant indentation; nesting block comments; Zig-style `\\`-prefixed line-oriented multiline strings (no here-docs); `module`/`needs`/`use` header must precede all declarations, which may then appear in any order. | Every choice buys a specific compiler property. Mandatory semicolons plus braces give two unambiguous resync tokens for error recovery and make a token-level brace-counting prepass sufficient to find top-level declaration boundaries without parsing bodies — that prepass is what makes parallel parsing and per-declaration hashing possible. Line-oriented raw strings guarantee no token sequence can hide unbalanced braces from the prepass; here-docs would break it. Header-first gives the module-graph edges from the first ~3 lines of each file, so the dependency DAG is built before any body is parsed. | Semicolons are a small ergonomic tax and will attract bikeshedding; the formatter inserts them, and the token-prepass guarantee is a written spec clause that future syntax additions must not violate. |
| Generic syntax without the `<` ambiguity | Declaration: `fn sort[T: Ord](inout s: SliceMut[T])`, `struct Array[T: type, N: usize]`. Type position: `Slice[u8]` is always generic application. Expression position: `expr[args]` parses to one `Bracket` node that the checker resolves to index or instantiate using the already-synthesized receiver type. Rejected Carbon/Zig-style `Vector(i32)`. | `[...]` is context-free in both positions (type grammar has no indexing; expression grammar has one production), so no turbofish, no symbol table, no backtracking. Parens-for-generics was rejected because it pushes toward Zig's 'generic = comptime fn returning type', which forces whole-program monomorphization and kills separate compilation — directly hostile to G3. | The index-or-instantiate disambiguation is a checker responsibility; it is O(1) because synthesis is bottom-up, but it must be specified carefully for the `Bracket` node on a value of trait-object type. |
| Generics and traits under shape-based lowering | Definition-site-checked traits with an orphan rule (impl lives in the trait's module or the type's module), no overlapping impls, no negative bounds, no specialization-dependent semantics. Default lowering is shape-based: one body per shape (size, align, pointerness, qualifier, deinit-ness) with a witness table carrying size/align/copy/move/deinit plus methods. `dyn T` has the identical representation, so there is no perf cliff between generic and dynamic dispatch. `@specialize` on a declaration or a call site forces monomorphization within the module, content-addressed. | Shape-based keeps compile time and binary size linear in source and preserves separate compilation, which is the precondition for parallel module compilation. Definition-site checking is what makes shape-based possible at all (duck-typed instantiation cannot be compiled once). | This is the largest G1 exposure in my subsystem: an indirect call inside a hot inner loop (comparator in sort, lane op in a reduction) costs real percent. Mitigations: auto-specialize generic bodies under N IR instructions within their module, hand-`@specialize` every numeric/SIMD combinator in std, PGO-driven specialization later. If bench data shows this is worse than modelled, the fallback is 'auto-specialize all scalar-shape instantiations', which raises compile time — a knob, not a redesign. |
| Type inference: exactly two modes, no solver | Signatures are fully annotated (all parameter types, return type, `raises`, conventions). Bodies use only `synth(e) -> T` and `check(e, T)`. No inference variables outlive one expression; no backtracking; no return-type-directed resolution; no function overloading; a fixed 5-entry coercion list applied only at checking boundaries. Generic call inference binds each type parameter at the leftmost argument position mentioning it and *checks* all later positions against that binding. | Swift's 42-seconds-to-fail-on-12-lines is the counterexample; expressiveness here trades directly against the one goal that is outright winnable. Banning overloading removes candidate sets entirely, which is what lets the checker be provably near-linear and CI-enforceable. | Callback-last becomes mandatory for inference to work (enforced by a lint); users coming from Rust will miss `collect()`-style return-type inference and must write `let v: List[u8] = ...`. Accepted and documented as a rule, not a wart. |
| Operator policy | No user-defined operator symbols, no precedence declarations, no general overloading. A closed set of compiler-known operator traits (`Add`, `Sub`, `Mul[R]`, `Div`, `Neg`, `Eq`, `Ord`, `Index`, `IndexMut`). `a + b` desugars to `typeof(a).add(a, b)` — one lookup keyed on the left type only; `b` must match exactly or be a comptime literal. Logical ops are `and`/`or`/`not`; bitwise are `&`/`\|`/`^`/`<<`/`>>` with flat non-associative precedence that requires parentheses when mixed with comparison. Prefix `&` (inout marker) and infix `&` (bitwise and) are distinguished by parser position, not by types. | Vec3/Complex/SIMD ergonomics are non-negotiable for an HPC language, but overload sets are where inference blows up. Left-type-only resolution gives 95% of the ergonomics at O(1). Fixing C's `&`-vs-`==` precedence bug is free at design time and is a security win. | No `Mul` with the scalar on the left (`2.0 * v`) unless std impls `Mul[Vec3] for f64`; std will do exactly that for the scalar×vector cases, and the asymmetry must be documented. |
| Reference capabilities collapsed to three type qualifiers | `iso` (isolated, uniquely-owned, sendable graph), `imm` (deeply immutable, freely shareable), `secret` (side-channel-confined). Everything Pony expresses with `ref`/`val`/`box`/`tag` is instead carried by parameter conventions at function granularity. Sendability rule: a value crosses a `spawn` boundary iff it is `imm`, or `iso` and moved, or a value type containing no interior references. | Pony's six-capability lattice is the single most-cited reason people bounce off Pony. Conventions already give exclusive-mutable (`inout`) and read-only (`let`); what conventions cannot give is 'sendable' and 'shareable', which is exactly `iso` and `imm`. Three qualifiers erase to zero runtime representation and form a small checkable lattice. | Two qualifiers may be too few for shared-mutable-with-atomics; that case is handled by an explicit `Shared[T]` library type with atomic-only API rather than a fourth qualifier. If real programs need a fourth, adding one to a lattice is backwards-compatible; removing one is not. |
| Parameter conventions with visible call-site markers | `let` (default, read-only borrow), `inout`, `sink`, `set`. Call sites must mark non-default conventions: `f(&v)` for inout, `f(move b)` for sink, `f(&out y)` for set. No safe first-class reference type in v1. | Call-site markers make aliasing and move points visible in diffs and greppable, and they let the parser know an argument's convention without a symbol table (useful for error recovery and for LSP inlay hints). Omitting a safe reference type is the single biggest complexity saving: it is what removes lifetimes, variance and region inference from v1. | Graph-shaped data (doubly-linked lists, back-pointers, observer webs) must use arena `Handle[T]` indices or `unsafe Ptr[T]`. This is a real expressiveness hole and I am naming it rather than papering over it; opt-in regions are the planned post-1.0 answer. |
| Error handling model and failure ABI | Errors are values: `fn read(...) -> Bytes raises io.Error`. Propagation is postfix `?` (with implicit conversion through a compiler-known single-lookup `ErrorFrom` impl); explicit handling via `else \|e\| { ... }` or `match`. Lowering: the error travels in a second return register (aarch64 x1 / x8-sret + flag) — no unwinding, no landing pads, no DWARF unwind tables required for correctness. `panic` (contract violation, overflow trap, bounds trap) aborts the process, or the isolation domain at a `spawn` boundary. `defer` / `errdefer` for cleanup; `deinit` runs deterministically at last use. | An explicit failure ABI is the gap nobody in the surveys addressed, and it is load-bearing: no unwinder means the two backends have far less to agree on, FFI is trivial, binaries are smaller, and the safe subset stays UB-free. `raises` costs one branch. | No catchable panics means a long-running host process cannot survive a library bug the way a Rust server can with `catch_unwind`. Acceptable for HPC-first; the domain-abort escape at `spawn` boundaries is the partial answer and must be specified precisely. |
| Capability surface | Per-module `needs { fs.read, io.stdout, clock }` clause in the header, checked over the acyclic module graph at build and again at link. Capability *values* (`io.Writer`, `fs.Dir` rooted at a path, `Clock`, `Rng`, `gpu.Device`) exist only where authority narrows, and the only root is the `sink World` parameter of `main`. `ffi` is itself a capability that marks its subtree unguaranteed and taints the module's guarantee level in the audit ledger. The manifest is inert Fors data literals with no evaluation. | Module-level declaration avoids the viral-signature tax of full capability-value threading while keeping 'this dependency is statically incapable of network access' a checkable fact. Values at narrowing points are where the real security value is (a `Dir` rooted at ./data is stronger than a `fs` flag). | Dynamic linking / dlopen / plugins defeat a static module-graph check. v1 answer: capability-confined builds are guaranteed for statically linked artifacts only; `dyn.load` is a distinct capability that marks the process unguaranteed. Stated as a limitation in the spec, not hidden. |
| Numeric and float semantics in the surface | Fixed-width integers only, trap on overflow in all modes, explicit `wrap_add`/`sat_add`/`unchecked_add` (last requires `unsafe`). No implicit conversions whatsoever; `as` is checked-and-trapping, with keyword operators `wrap_as` / `sat_as` / `trunc_as` for explicit lossy conversion. Strict IEEE-754 by default; `fastmath(reassoc, fma, no_nan) { ... }` is a lexically scoped block with named flags. No `i128`/`u128` in v1. `comptime_int`/`comptime_float` are arbitrary-precision and comptime-only. | Named fast-math flags rather than a compiler switch means the reproducibility story is per-region and reviewable, and the reference interpreter can model each flag. Killing implicit conversion removes a large class of security bugs and a large chunk of inference cost at once. | Strict-IEEE default measurably costs vectorization on reduction loops; the design pays it and makes the opt-in one line. HPC users will need `fastmath` in most inner loops, which is the intended, visible trade. |
| Parallel / SIMD / GPU surface | `parallel { spawn f(...); spawn g(...); }` with implicit sync at block end; `parallel for i in 0 ..< n grain 1024 { }`; reductions declared with an order policy — `reduce(+, order: tree)` is the default and is bit-reproducible for a given (n, grain), `order: any` opts out. SPMD: `simd for x in 0 ..< w { }` with `uniform` for lane-invariant bindings and predicated control flow inside (no divergence UB). SIMD types `Vec[4, f32]` fixed-width plus `SVec[f32]` scalable, the latter legal only inside a `simd` block. GPU: `kernel fn` with a restricted subset (no allocation, no capabilities, no `raises`, no recursion, gpu-safe types only) plus host-side `gpu.launch`. | Deterministic-by-default reductions answer the parallel-determinism gap that the surveys conflated with race freedom: race-free is not reproducible, and a fixed tree shape keyed on (n, grain) makes it reproducible across core counts at modest cost. Scoping `SVec` to `simd` blocks is how scalable vectors enter the type system without infecting general struct layout. | Proving index-disjointness for `parallel for` bodies is the hardest checker in the design. v1 restricts safe mutation to disjoint-by-construction projections (`chunk_mut`, `split_at`) rather than general index analysis; anything else requires `iso` partitioning or `unsafe`. This will feel restrictive and is the most likely place to need a v1.1 extension. |
| Layout and SoA | `@layout(c\|packed\|native)`, `@align(64)`, and `soa struct Body { ... }` which makes `Soa[Body]` a distinct compiler-known container with `bodies.pos[i]` field-array access and `AoSoA[Body, W]` for tiled layouts. AoS and SoA are different types; conversion is explicit. Rejected Odin's `#soa` pointer-marker approach. | Making SoA a distinct type rather than a transparent marker means the checker and the optimizer both know the layout structurally, and accidental AoS/SoA mixing is a type error instead of a silent perf cliff. | `Soa[T]` needs a lot of compiler-known machinery (field projection, slicing, contracts over field arrays) and will be a recurring source of special cases. Budgeted as a first-class feature, not a library. |

## Design

## 1. Syntax family

Braces, keyword-led declarations, postfix `name: Type`, mandatory `;`. Every top-level form starts with one of `module needs use fn struct enum union trait impl const type kernel ghost`. File shape is fixed: `module a.b;` → `needs { ... };` → `use ...;` → declarations in any order.

Three parse-time guarantees are **spec clauses**, not implementation details: (P1) a token-level brace count with no context finds every top-level declaration boundary (hence nesting block comments and line-oriented `\\` raw strings — no here-docs); (P2) no production requires type or name information (hence `[...]` generics, no overloading, no user operators); (P3) `;` and `}` are recovery anchors, so a malformed body never desynchronises the next declaration. Formatter additionally puts the closing `}` of a top-level declaration at column 0, which the parser uses as a *hint* for parallel chunking.

## 2. Core types

Scalars `i8..i64 isize u8..u64 usize f16 f32 f64 bool char never type comptime_int comptime_float`. No `i128` in v1. Aggregates: `struct`, `enum` (tagged, payloads named, optional explicit tag type), `union` (unsafe/FFI only), tuples `(A, B)`, fixed arrays `[N]T` / `[_]T`, `Slice[T]` / `SliceMut[T]` (pointer + *trusted* length — the structural basis for bounds-check elimination), `Vec[N, T]`, `SVec[T]`, `Soa[T]`, `AoSoA[T, W]`. Heap edges: `Own[T]` (affine, one pointer, allocator passed to `deinit`), `Handle[T]` (arena index), `Ptr[T]` (unsafe). **No safe stored reference type in v1** — this is what buys the absence of lifetimes.

Qualifiers (prefix, erased at runtime): `iso`, `imm`, `secret`. `secret` bans branching on, indexing by, and variable-latency ops over secret values; `declassify` is a capability-gated intrinsic.

## 3. Inference rules (normative)

1. Signatures are fully explicit: parameters (type + convention), return type, `raises`, `where` bounds. No inferred signatures anywhere, including closures that escape.
2. Two judgements only: `synth(e) → T` (bottom-up) and `check(e, T)`. No inference variable survives past one expression; no backtracking; no unification queue.
3. `let x = e` / `var x = e` use `synth`. `var x: T = e` uses `check`.
4. Any expression beginning with `.` (`.{...}` struct/tuple, `.[...]` array, `.case(...)` enum) is **legal only in checking position**. `T.{...}` is the synthesis form.
5. Bare integer literal in synthesis position is `i64`, float is `f64`; in checking position against numeric `T` it is `T` (error if it does not fit). Empty `.[]` / `.{}` requires annotation.
6. Generic call: scan parameters left to right; the first position mentioning type parameter `X` *binds* `X` by structural match; every later position is *checked* against the binding. Return type never contributes. Consequence: callbacks go last (lint-enforced).
7. `e.m(...)`: `synth(e)` → `T`; look `m` up in `T`'s inherent members, then in the impls of traits named in the enclosing `where` clause / in-scope impls. One table lookup. No autoref/autoderef chains; exactly one level of explicit `Ptr` deref via `p.*`.
8. Coercions are a closed list of five, applied only at a checking boundary, never searched: `[N]T → Slice[T]`; uniquely-owned `T → imm T`; comptime literal → numeric; concrete → `dyn Tr` at an explicit `dyn` annotation; `iso T → T` (consuming isolation).
9. `expr[args]` resolves to instantiate if `synth(expr)` is a generic function/type value, else index. O(1).
10. CI gate: a pathology corpus (deep nesting, 500-link method chains, 10-deep generic instantiation) with hard wall-clock ceilings; any superlinear regression fails the build.

## 4. Traits, generics, conventions

```fors
trait Ord: Eq { fn cmp(let self: Self, let other: Self) -> Order; }
trait Mul[R: type] { type Out; fn mul(let self: Self, let r: R) -> Self.Out; }

fn sort[T: Ord](inout s: SliceMut[T]) { ... }   // shape-based
@specialize fn sort_f64(inout s: SliceMut[f64]) { sort(&s); }
```

Orphan rule, no overlap, no negative bounds. Witness = {size, align, copy, move, deinit, methods}; `dyn Tr` is the same pair, so generic and dynamic dispatch cost the same — stated as a design property. `@specialize` monomorphizes within a module, content-addressed.

Conventions: `let` (default), `inout`, `sink`, `set`; call-site markers `&x`, `move x`, `&out y`. Move semantics are affine: after `move x`, `x` is dead (flow-sensitive, intraprocedural, no annotations). Types with `deinit` must be consumed or deinit'd before scope end — a compile error otherwise, which is how "forgot to pass the allocator" is caught statically.

## 5. Errors, contracts, comptime

```fors
fn load(let d: fs.Dir, let name: Str, let a: Allocator) -> Own[Slice[u8]] raises fs.Error
    pre  name.len > 0
    post result.len <= MAX
{
    var f = fs.open(d, name)?;
    errdefer f.close();
    ...
}

struct Ring[T: type] {
    buf: Own[Slice[T]], head: usize, len: usize,
    invariant len <= buf.len and head < buf.len,
}
```

`pre`/`post`/`invariant`/`ghost fn`/`old(x)`/`result`, with `forall i in a ..< b : P` as the only quantifier form. Runtime-checked by default; `@static` attempts external-SMT discharge, cached by content hash, timeout → runtime check + warning (hard error under `--verify=strict`). Invariants are checked on entry/exit of every `pub` method taking `inout self`.

`comptime` params and blocks run on the pure budgeted VM; callees must be `pure` (inferred in-package, declared on exports). Filesystem access at comptime only via `@embed("path")` with paths whitelisted in the manifest.

## 6. Five programs

**(1) hello, capability-passed stdout**
```fors
module hello;
needs { io.stdout };
use std.io;

fn main(sink w: World) raises io.Error {
    var out: io.Writer = move w.stdout;   // authority moves in; w.stdout is dead
    io.print(&out, "Hello, Fors!\n")?;
}
```

**(2) n-body kernel**
```fors
module nbody;
use std.math;

@layout(native) struct Vec3 { x: f64, y: f64, z: f64 }
impl Add for Vec3 { fn add(let a: Self, let b: Self) -> Self {
    return .{ x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }; } }
impl Sub for Vec3 { ... }
impl Mul[f64] for Vec3 { type Out = Vec3;
    fn mul(let a: Self, let s: f64) -> Vec3 { return .{ x: a.x*s, y: a.y*s, z: a.z*s }; } }

soa struct Body { pos: Vec3, vel: Vec3, mass: f64 }
const SOFT: f64 = 1.0e-9;

fn advance(inout b: Soa[Body], let dt: f64)
    pre dt > 0.0 and b.len > 0
    post forall i in 0 ..< b.len : math.is_finite(b.mass[i])
{
    let n = b.len;                          // trusted length ⇒ no bounds checks
    for i in 0 ..< n {
        var acc: Vec3 = .{ x: 0.0, y: 0.0, z: 0.0 };
        fastmath(reassoc, fma) {
            for j in 0 ..< n {
                if i == j { continue; }
                let d   = b.pos[j] - b.pos[i];
                let r2  = d.x*d.x + d.y*d.y + d.z*d.z + SOFT;
                let inv = math.rsqrt(r2);
                acc = acc + d * (b.mass[j] * inv * inv * inv);
            }
        }
        b.vel[i] = b.vel[i] + acc * dt;
    }
    for i in 0 ..< n { b.pos[i] = b.pos[i] + b.vel[i] * dt; }
}
```

**(3) parallel mandelbrot, SPMD inner loop**
```fors
module mandel;
use std.parallel;

fn row(let y: usize, let w: usize, let h: usize, let max: u32, inout out: SliceMut[u8])
    pre out.len == w
{
    uniform let cy    = 2.0 * (y as f64) / (h as f64) - 1.0;
    uniform let scale = 3.0 / (w as f64);
    simd for x in 0 ..< w {                      // lanes = target width
        let cx = (x as f64) * scale - 2.0;
        var zx = 0.0; var zy = 0.0; var it: u32 = 0;
        while zx*zx + zy*zy <= 4.0 and it < max {   // predicated per lane
            let t = zx*zx - zy*zy + cx;
            zy = 2.0*zx*zy + cy; zx = t;
            it = it.wrap_add(1);
        }
        out[x] = it trunc_as u8;
    }
}

fn render(inout img: SliceMut[u8], let w: usize, let h: usize, let max: u32) {
    parallel for y in 0 ..< h grain 8 {
        var band = img.chunk_mut(y * w, w);       // disjoint by construction
        row(y, w, h, max, &band);
    }
}
```

**(4) GPU kernel + host launch**
```fors
module saxpy;
needs { gpu };
use std.gpu;

kernel fn saxpy(let a: f32, let x: gpu.Buf[f32], inout y: gpu.BufMut[f32])
    pre x.len == y.len
{
    let i = gpu.gid.x;
    if i < y.len { y[i] = a.fma(x[i], y[i]); }
}

fn run(let dev: gpu.Device, let a: f32, let x: Slice[f32], inout y: SliceMut[f32])
    raises gpu.Error
{
    var dx = gpu.upload(dev, x)?;          errdefer dx.deinit(dev);
    var dy = gpu.upload_mut(dev, y)?;      errdefer dy.deinit(dev);
    gpu.launch(dev, saxpy, grid: .{ x: y.len }, block: .{ x: 256 },
               args: .{ a, dx.view(), &dy })?;
    gpu.download(dev, &dy, &out y)?;
    dy.deinit(dev); dx.deinit(dev);
}
```

**(5) `fors.pkg` manifest (inert data literals, same lexer, zero evaluation)**
```fors
package .{
  name: "nbody-bench", version: "0.3.1", fors: "1.0", license: "Apache-2.0",
  targets: .{
    .{ kind: .bin, name: "nbody", root: "src/main.fors",
       capabilities: .{ io.stdout, clock, fs.read: .{ roots: .{ "./data" } } } },
    .{ kind: .lib, name: "nbody_core", root: "src/lib.fors",
       capabilities: .{ } },                       // statically incapable of I/O
  },
  deps: .{
    std:      .{ version: "1.0",  hash: "b3:9f21c4…" },
    fast_csv: .{ version: "^0.4", hash: "b3:71ade0…",
                 capabilities: .{ },               // assertion: build FAILS if it gains one
                 audit: .{ reviewed_by: "marcfors", date: "2026-08-02" } },
  },
  policy: .{ deny: .{ exec, net, ffi, dyn.load },
             comptime: .{ steps: 100_000_000, bytes: "64MiB",
                          embed: .{ "data/table.bin" } },
             overflow: .trap, float: .strict, reproducible: true },
}
```

## 7. Modules, strings, patterns

One module per file; `module a.b.c;` must match the path. `use std.math as m;` and `use std.math.{sqrt, abs};`; **no glob imports**. Cycles are an error. Visibility: default module-private, `pub` = package-visible, `export` = visible to dependents.

`Str` = `imm Slice[u8]`, guaranteed UTF-8, no code-point indexing; `.bytes()`, `.chars()`, `.graphemes()` (tables in `std.unicode`, not core). No `+` on strings — concatenation allocates, so it takes an allocator: `str.concat(a, x, y)`. Source is UTF-8; **identifiers are ASCII-only in v1** (kills confusable-identifier supply-chain attacks); literals take `\u{...}`. No normalization in core.

`match` with mandatory exhaustiveness, guards, one level of or-patterns, range patterns, slice patterns with one `..rest`; `match &x` gives `inout` bindings, `match move x` gives `sink` bindings.

## 8. Stdlib scope

**v0.1 (no capability required):** `core` (prelude, operator traits, `Order`, `Option`, `Result`-shaped errors), `mem` (`Allocator` trait, `Arena`, `FixedBuf`, `Page`, `Libc`), `slice`, `array`, `list`, `map` (open addressing), `str`, `math` (own portable `sqrt/rsqrt/exp/log/sin/cos` with documented accuracy bounds — libm accuracy varies per platform and that breaks reproducibility), `simd`, `sort`, `hash`, `fmt`, `atomic`, `parallel` (spawn/sync, parallel-for, reductions), `contract`, `test`, `bench`.
**v1.0 adds:** `io`, `fs`, `net`, `process`, `env`, `time`, `rand`, `unicode`, `json`, `encode`, `crypto` (constant-time, built on `secret`), `gpu`, `npu`, `dist`, `profile`, `path`. No regex in v1.

## 9. Spec, tooling, naming, exclusions

**Spec:** one document, hard ceiling 120 pages, every paragraph has a stable ID (`§7.3.2`). Contents: lexical structure; a single machine-readable LL(1)/PEG grammar file the parser is *checked against* in CI; static semantics as typing rules; dynamic semantics *is* the reference interpreter (executable, authoritative); core library signatures; diagnostics with stable codes (`F0001`…). Conformance suite: `tests/conformance/**.fors`, each citing paragraph IDs and asserting output or exact diagnostic code; CI reports uncovered paragraphs and fails below threshold. Diagnostics are part of the spec.

**Formatter:** canonical, zero options, CST→text over a lossless trivia-preserving CST, line-local by grammar design; `fors fmt --check` in CI from week one.

**LSP:** `fors lsp` is a mode of the same binary over the same query DAG. Day one: diagnostics, hover, go-to-def, completion, rename, format, document symbols, plus inlay hints for inferred types and for convention markers.

**Naming:** types `UpperCamel`; fns/vars/fields `snake_case`; consts `SCREAMING_SNAKE`; modules lowercase `snake_case`; enum cases `snake_case`; capabilities dotted lowercase. Lints with codes, errors under `--pedantic`.

**Deliberately left out (complexity budget):** classes/inheritance, exceptions/unwinding, GC, function overloading, user-defined operators, implicit conversions, syntactic macros, runtime reflection, variadics (comptime tuple expansion instead), default parameter values, subtyping/variance, lifetimes, regions (v1), higher-kinded types, variadic generics, effect polymorphism, `async`/`await` (no coloring: OS threads + structured fork/join for compute, explicit completion-queue IO APIs — an honest gap for server workloads, acceptable for an HPC-first v1), and safe stored references.

## Interfaces other subsystems must honor

- Frontend/compiler architect: the three parse-time guarantees (P1 token-level brace counting locates top-level declaration boundaries with zero context; P2 no production consults names or types; P3 `;` and `}` are recovery anchors) are normative spec clauses. Any future syntax proposal that violates one is rejected by construction. The header-first rule means the module DAG is extractable from the first three lines of each file before any body is parsed.
- Frontend architect: the type checker must implement exactly two judgements (`synth`, `check`) with no inference variable outliving one expression and a closed 5-entry coercion table. The CI pathology corpus with wall-clock ceilings is my subsystem's acceptance gate on yours.
- Frontend architect: `expr[args]` produces a single CST `Bracket` node; index-vs-instantiate is resolved in the checker from the already-synthesized receiver type, never in the parser.
- Backend architect: the failure ABI is mine to specify and yours to implement — `raises E` returns the error in a second return register (aarch64 x1, or the sret+flag form for large payloads). No unwinder, no landing pads, no .eh_frame needed for correctness. Panic = abort (or domain abort at a spawn boundary).
- Backend architect: shape-based generic calls need a witness record layout {size, align, copy, move, deinit, method slots} that is identical to the `dyn Tr` fat-pointer layout. `@specialize` needs a content-addressed instantiation cache keyed on (declaration hash, argument type hashes).
- Backend architect: `fastmath(reassoc, fma, no_nan)` is a lexically scoped set of *named* flags carried structurally on IR regions, not dropped metadata; the reference interpreter must model each flag so differential testing stays meaningful.
- Backend architect: `secret`-qualified operations must lower only to a documented constant-time instruction subset; a `secret` value reaching a branch, an index, or a variable-latency divide is a frontend error, but you own the guarantee that the chosen instructions are actually CT on aarch64 and x86_64.
- Parallel/runtime architect: `parallel`/`spawn`/`sync` map to Tapir-style first-class IR instructions. `reduce(+, order: tree)` is the default and must be bit-reproducible for a given (n, grain) independent of core count and of work-stealing decisions; `order: any` is the opt-out. `simd for` needs lane-predicated control flow with no divergence UB, and `SVec[T]` is legal only inside a `simd` region.
- Parallel/runtime architect: v1 safe mutation inside `parallel for` is restricted to disjoint-by-construction projections. `SliceMut[T].split_at` and `.chunk_mut` are the keystone primitives; their signatures and disjointness guarantee belong to the spec, and the checker rule is 'projection provenance', not general index analysis.
- Security/build architect: `needs { ... }` is the per-module declaration site; `World` (a `sink` parameter of `main`) is the only root of authority; capability values are ordinary types with no ambient constructor. The manifest is Fors data literals parsed by the same lexer with zero evaluation. Per-dependency `capabilities: .{ ... }` is an assertion that fails the build when a resolved version needs more — including a patch bump. `ffi` and `dyn.load` taint their subtree's guarantee level in the audit ledger.
- Security/build architect: comptime purity, declared inputs, `@embed` path whitelisting and step/alloc budgets are surfaced in `policy.comptime` in the manifest; the compiler enforces, the manifest declares.
- Benchmark-harness (M0) owner: I will freeze a 'Bench Subset' of the language — the minimum surface needed to write the M0 kernels (n-body, mandelbrot, spectral-norm, binary-trees/arena, matmul, histogram, sha256, JSON-ish parse). Each C/Rust/Zig kernel in M0 must be written so that its Fors translation needs nothing outside that subset, so Fors can join kernel-by-kernel the week the frontend lands. Harness metrics must include a Fors-specific column for `fastmath` on/off, since strict-IEEE-by-default is a deliberate perf cost that must be visible in the numbers.

## Milestones (this architect's own estimate)

| Milestone | Deliverable | Exit criteria | Effort |
|---|---|---|---|
| M1 — Bench Subset freeze | A written 15-page subset spec (scalars, structs, fixed arrays, slices, `fn` with conventions, `for`/`while`, operator traits, `fastmath`, `parallel for`, `simd for`, `main(sink World)`) plus hand-written Fors source for all eight M0 kernels, reviewed for expressiveness but not yet compilable. | Every M0 kernel has a Fors translation that a C/Rust programmer reads without explanation, and no kernel needs a feature outside the subset. The subset's grammar is a strict sublanguage of the full grammar file. | 3 weeks |
| M2 — Grammar file + formatter + lexical spec | `spec/grammar/fors.ebnf` (machine-readable, LL(1) modulo Pratt expression levels), the lexical spec, the operator precedence table, and a CST-based canonical formatter with zero options. A grammar-conformance CI job that fuzzes the grammar against the hand-written parser. | Parser and grammar file agree on 100% of a 500-file corpus including 200 deliberately malformed files; formatter is idempotent and round-trips all comments; the three parse-time guarantees (P1–P3) are proven by a property test that finds declaration boundaries with a brace-counter alone. | 5 weeks |
| M3 — Type system spec + conformance suite v0.1 | Normative typing rules for the two-judgement inference, the 5-entry coercion table, traits with the orphan rule, shape-based lowering obligations, `@specialize`, parameter conventions and the affine move checker. ~400 conformance tests citing paragraph IDs, plus the type-checker pathology corpus with wall-clock ceilings. | Every inference rule has at least one positive and one negative conformance test; the pathology corpus passes with linear scaling measured across 4 input sizes; no rule in the spec requires a solver, a worklist, or backtracking. | 8 weeks |
| M4 — Safety surface spec | `needs` clauses and the capability catalogue; `World` and capability-value narrowing; the `fors.pkg` data-literal schema with per-dependency capability assertions; the `iso`/`imm`/`secret` lattice and sendability rule; `raises`/`?`/`else \|e\|`/`defer`/`errdefer` with the documented two-register failure ABI; contracts (`pre`/`post`/`invariant`/`ghost`/`old`/bounded `forall`). | An adversarial dependency suite (10 packages attempting network egress, file exfiltration, exec, comptime file reads, FFI escape, capability-gain-on-patch-bump) is 100% rejected at build time by rules stated in the spec alone. Every `secret` misuse in a 30-case corpus is a compile error with a stable diagnostic code. | 7 weeks |
| M5 — Parallel / SIMD / GPU surface spec | `parallel`/`spawn`/`sync`, `parallel for ... grain`, `reduce` with order policies, `simd for` with `uniform` and predication semantics, `Vec[N,T]`/`SVec[T]`, `soa struct` and `Soa[T]`/`AoSoA[T,W]`, `kernel fn` restriction list and `gpu.launch` host API shape. | Reduction determinism is specified precisely enough that the reference interpreter and both backends produce bit-identical results for a fixed (n, grain) across 1/2/6/8 threads. The `kernel fn` restriction list is mechanically checkable and every violation has a diagnostic code. | 7 weeks |
| M6 — Spec 1.0 freeze and semantics lock | The consolidated ≤120-page spec with stable paragraph IDs, the full diagnostics catalogue, the executable reference interpreter as the normative dynamic semantics, ~2000 conformance tests with paragraph coverage reporting, and the day-one LSP feature set. | Paragraph coverage ≥95%; the reference interpreter passes 100% of conformance; the spec has been read end-to-end in one sitting by one person; no open semantic questions remain. This is the gate that unlocks self-hosting. | 12 weeks (overlapping M3–M5, not sequential) |

## Top risks

- Shape-based lowering is the single biggest G1 risk in the surface design: an indirect call in a hot inner loop (sort comparator, reduction lane op) can cost tens of percent versus monomorphized Rust. Mitigation is a stack of increasingly ugly fallbacks (auto-specialize small bodies in-module, hand-`@specialize` every std numeric combinator, PGO-driven specialization). If M0 benchmarks show the gap is large on the kernels that matter, the plan is a knob (specialize all scalar-shape instantiations, paying compile time), not a redesign — but that knob eats directly into the G3 margin, so G1 and G3 are genuinely coupled here.
- Proving index-disjointness for `parallel for` bodies is the hardest checker in my subsystem, and the v1 answer (projection-provenance only: `split_at`, `chunk_mut`) will be visibly restrictive. Real HPC code does strided, blocked and halo-exchange access patterns that this rule rejects, forcing `iso` partitioning or `unsafe`. Expect this to be the top user complaint and the first v1.1 extension request.
- No safe stored reference type means graph-shaped data has no ergonomic safe encoding. Arena handles and `Own[T]` cover trees and pools; doubly-linked structures, back-pointers, observer graphs and intrusive lists need `unsafe` or index indirection. This is a real expressiveness hole in a language that claims memory safety, and the honest answer — 'opt-in regions, post-1.0' — is a promise with no design behind it yet.
- Strict-IEEE-by-default plus trap-on-overflow-in-release will show up as a measurable deficit against `clang -O3 -ffast-math` on exactly the kernels the benchmark harness highlights. The design's answer is `fastmath(...)` blocks and trusted-length slices, which means Fors's competitive numbers require the programmer to opt in. The marketing risk is that naive Fors looks slow; the mitigation is that the harness reports both columns from day one so nobody is surprised.
- Three qualifiers (`iso`/`imm`/`secret`) may be one short. Shared-mutable-with-atomics is pushed into a library `Shared[T]`, which works only if every such pattern can be expressed with an atomic-only API. If a fourth qualifier is needed, adding it to the lattice is source-compatible; but discovering the need after the stdlib is written means reworking std signatures.
- No `async`/`await` and no catchable panics make Fors a poor fit for long-lived server processes: no `catch_unwind`-style resilience, and IO concurrency needs explicit completion-queue APIs. This is defensible for an HPC-first v1 and indefensible for the general-purpose positioning the project may later want. The decision should be revisited only at a major version, because adding coloring later is a breaking change to every signature.
- The 120-page spec ceiling collides with 'everything in v1'. Capabilities, contracts, `secret`, `iso`/`imm`, SPMD, scalable vectors, GPU kernels, SoA containers and the conformance-test discipline are each 8–15 pages done properly. Honest estimate: the full surface is 180–220 pages, and the 120-page target is only reachable by splitting into a normative core spec plus separate normative annexes — which weakens the 'fits in one head' claim that is the project's main defence against the Carbon/Vale failure modes.
- Identifiers restricted to ASCII is a genuine security win and a genuine adoption cost. Non-English-speaking contributors will read it as exclusionary, and the decision is hard to reverse later without reintroducing the confusable-identifier attack surface. Worth making, worth documenting the reasoning for prominently, and worth expecting to defend repeatedly.

## Decision points for Marc to code personally

- `spec/grammar/fors.ebnf`, the `statement` production — decide mandatory `;` versus Go-style automatic insertion. Trade-off: semicolons give two unambiguous error-recovery anchors and a trivially correct formatter; ASI gives nicer ergonomics but adds a newline-sensitivity rule that every future syntax addition must be checked against. 6 lines of EBNF, and it is the decision the whole recovery strategy rests on.
- `compiler/src/parse/precedence.rs`, `fn binding_power(tok: Tok) -> (u8, u8)` — write the operator precedence table. Trade-off: copy C's precedence for familiarity, or fix C's mistake by giving `&`/`|`/`^` flat non-associative precedence that forces parentheses when mixed with comparison. Also decide whether comparison chaining (`a < b < c`) is a parse error. ~10 lines, permanently visible in every program.
- `compiler/src/check/coerce.rs`, `fn coerce(from: Ty, to: Ty) -> Option<Coercion>` — write the 5-entry coercion match arm-for-arm. Trade-off: every entry added costs inference predictability and one more surprise in error messages; every entry omitted costs an explicit conversion at a call site. This function is the guardrail on inference complexity, and it should be small enough to read in one screen.
- `compiler/src/check/literal.rs`, `fn default_numeric_ty(lit: Lit) -> Ty` — decide the synthesis-position default for a bare integer literal: `i32` (C/Rust familiarity, cheaper arithmetic), `i64` (fewer surprise traps on 64-bit indexing), or hard error requiring annotation (most explicit, most annoying). 5 lines that shape how every `let n = 0;` in the language behaves.
- `stdlib/core/src/slice.fors`, `fn split_at(inout self: SliceMut[T], let mid: usize) -> (SliceMut[T], SliceMut[T]) pre mid <= self.len` — write this signature and its contract. Trade-off: whether the disjointness guarantee is expressed as a contract the checker trusts, or as a compiler-known intrinsic. This is the keystone of all safe parallel mutation in the language; everything in `std.parallel` is built on it.
- `spec/diagnostics.md` plus `compiler/src/diag/codes.rs` — write the exact wording for the five diagnostics users will hit most: missing `move` on a `sink` argument, missing `&` on an `inout` argument, use-after-move, capability not declared in `needs`, and `secret` value used in a branch condition. Trade-off per message: terse-and-precise versus teaching-with-a-suggested-fix. These five strings are the language's actual user interface and deserve a human author, not a generated template.
- `spec/ch07-parallel.md`, the reduction-determinism clause — write the ~8 lines that define the default reduction tree shape as a function of (n, grain). Trade-off: a shape that is reproducible across core counts costs some scheduling freedom and may lose a few percent versus a free-for-all work-stealing reduction. This clause is the project's answer to the parallel-determinism gap that all five surveys missed, and its exact wording binds both backends and the reference interpreter.
- `compiler/src/lex/keywords.rs`, the reserved-word table — fix the final keyword set. Trade-off: more keywords (`wrap_as`, `sat_as`, `trunc_as`, `uniform`, `grain`, `ghost`, `kernel`, `needs`) give better error messages and stronger parallel-parse anchors but steal identifiers from users and are impossible to remove later; contextual keywords avoid the theft but violate the no-context parsing guarantee. Decide which of the marginal ones earn full reservation.
