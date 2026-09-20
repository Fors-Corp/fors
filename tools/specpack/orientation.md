Fors is a systems language with explicit ownership conventions, capability-based
authority, and a single-pass type checker (no solver, no implicit conversions,
no overloading). It looks nearest to Rust/Zig/Swift on the surface but differs
in the ways below; every quote is a real, contiguous span of an ACCEPTED file
under `tests/conformance/`, never invented. `fors check` is the arbiter, not this pack.

**Semicolons are mandatory; there is no ASI.** `let`/`var`, assignment, expression,
`return`, `raise`, `break`, `continue`, `discard`, `consume` and `spawn` statements each end in `;`.
A statement whose body is a block — `if`, `match`, `for`, `while`, `with`, `parallel`, a bare block,
`defer { }`/`errdefer { }` — takes NO `;`, and writing one is a parse error.
<!-- from: tests/conformance/01-ownership/conv-move-present-accepted.fors -->
```fors
fn consume_box(sink b: Box) {
    discard b;
}
```
**A pattern binds a name only via `let name`; a bare name in a pattern is always a reference, not a binding.** `some(let v)` binds `v`; `none` below is the prelude value, referenced (and may repeat across arms).
<!-- from: tests/conformance/08-names/pattern-prelude-value-reference-accepted.fors -->
```fors
    match a {
        none => 0,
        some(let v) => match b {
```
**Every function parameter declares a convention — `let`, `inout`, `sink`, `set` — and a call site marks a non-`let` argument to match: `&x` (inout), `move x` (sink), `&out x` (set); a method receiver alone never carries a marker.**
<!-- from: tests/conformance/01-ownership/conv-move-present-accepted.fors -->
```fors
fn use_it(sink b: Box) {
    consume_box(move b);
}
```
**Generic parameters go in `[...]`, never `<...>`.**
<!-- from: tests/conformance/07-grammar/bracket-roles-accept-2.fors -->
```fors
struct A[T] { v: T }
```
**A std module needs an explicit `use std.<name>;`; the prelude holds only types, values and traits, never a module** — `io.Stdout` is unreachable without importing `std.io` first.
<!-- from: tests/conformance/04-authority/needs-declared-accepted-run-ok.fors -->
```fors
needs { io.stdout };
use std.io;
```
**Heap-allocating std types take an explicit allocator value — there is no ambient allocator — and the root heap arrives as a parameter of `main`.**
<!-- from: tests/conformance/10-std/main-heap-parameter-accepted.fors -->
```fors
fn main(inout heap: mem.Heap) raises AllocError {
    var b: Own[i64, heap] = heap.create(7)?;
    heap.deinit(move b);
}
```
**Authority (`io`, `fs`, `net`, ...) enters ONLY as typed parameters of `main`, never an ambient "world" value; a module using a capability declares it in `needs { ... };`.**
<!-- from: tests/conformance/04-authority/main-signature-correct-accepted-run-ok.fors -->
```fors
needs { io.stdout };
use std.io;

fn main(inout out: io.Stdout) {
```
**No shadowing, anywhere — except a function-local binding may shadow a prelude name.** A local named `none` is legal and denotes the local, not the prelude value, inside its scope.
<!-- from: tests/conformance/08-names/local-shadows-prelude-value-accepted.fors -->
```fors
fn f() -> i32 {
    let none: i32 = 7;
    return none;
}
```
**An unsuffixed integer literal defaults to `i32`; indexing (Bracket, range, `Slice`) is `usize`-only regardless of that default.**
<!-- from: tests/conformance/03-numerics/slice-range-index-accepted.fors -->
```fors
    let s: Slice[i64] = data[0 ..< 3];
```
**Operators are homogeneous: `Add`/`Sub`/... take and return the SAME type, with no `Output` associated type and no mixed-type arithmetic.**
<!-- from: tests/conformance/09-types/operator-via-impl-accepted.fors -->
```fors
fn f(let a: V2, let b: V2) -> V2 { return a + b; }
```
**Bitwise `&`/`|`/`^` sit on their own flat tier: mixing one with arithmetic, comparison, or a DIFFERENT bitwise operator needs explicit `( )`** (a same-operator chain like `a | b | c` needs none).
<!-- from: tests/conformance/07-grammar/bitwise-accept-parenthesized.fors -->
```fors
    let r1 = (a + b) & c;
    let r2 = a | b | c;
    let r3 = (a & m) != 0;
```
**Failure is `raises T` on the signature, postfix `?` to propagate, and `raise expr;` to throw — no exception type, no `try`/`catch`. A trap aborts the whole process; nothing catches it.**
<!-- from: tests/conformance/10-std/main-raises-exit-status-one-run-error.fors -->
```fors
fn main() raises Error {
    raise Error.boom;
}
```
**A `Linear` value MUST be consumed on every path out of its scope — moved, or cleaned up, commonly via `defer`/`errdefer`, which run in reverse order at scope exit (`errdefer` only on an error exit).**
<!-- from: tests/conformance/01-ownership/defer-runs-on-return-run-ok.fors -->
```fors
    defer out.write_line("cleanup");
    out.write_line("body");
    return 1;
```
**Iterator adaptors and consumers are ordinary PROVIDED METHODS of `Iterator`, so they chain like `it.map(f).take(3)`; there is no free-function `map`/`filter`/`take`.**
<!-- from: tests/conformance/10-std/adaptor-chain-accepted.fors -->
```fors
fn f[A: brand](let v: Vec[i32, A]) -> usize {
    return v.iter().map(double).filter(small).take(3).count();
}
```
**`x.finish()` on a `sink self` method moves the named receiver `x` with no marker — the one call site that never writes `move`.**
<!-- from: tests/conformance/09-types/implicit-receiver-move-accepted.fors -->
```fors
fn f(sink b: Builder) -> i64 { return b.finish(); }
```
