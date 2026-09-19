# `std` — source tree (stubs, M0.5)

This is the source root of package `std`. File-to-module mapping is ch08
Rule 1, so `mem.fors` is module `std.mem` and `mem/vec.fors` is module
`std.mem.vec`. The `module` header is omitted everywhere: the mapping
decides, and an omitted header can never disagree with it.

**These files are STUBS.** Every signature here is normative and comes from
`docs/spec/10-std.md` — that chapter, not this tree, is the specification.
Bodies are placeholders marked `// STUB`: they parse, they are not
implementations, and they are not expected to run. A signature that
disagrees with ch10 is a defect in this tree.

## Layout

| File | Module | Contents (ch10 rule) |
|---|---|---|
| `mem.fors` | `std.mem` | the concrete allocators, `Buffer`, `Own`'s and `Option`'s surface, slice primitives, sorting, `MEM_MAX_ALIGN`, item-wise re-exports of the five submodules (R17-23, R27-31) |
| `mem/alloc.fors` | `std.mem.alloc` | `AllocError`, `Layout`, `Block`, `Allocator` (with the provided `create`/`deinit`), `own_raw`/`disown_raw` (R7, R12-16); a leaf |
| `mem/vec.fors` | `std.mem.vec` | `Vec[T, A]`, `try_collect_into` (R24, R35) |
| `mem/hashmap.fors` | `std.mem.hashmap` | `Map[K, V, A]`, `Hash` and its std impls (R25, R29) |
| `mem/text.fors` | `std.mem.text` | `String[A]`, `Str`'s surface, `Scalars`, `Utf8Error` (R26) |
| `mem/seq.fors` | `std.mem.seq` | `SliceIter`, `mem.iter`, the adaptors and consumers (R28, R33-35); a leaf |
| `io.fors` | `std.io` | `Writer`, `Reader`, `Stdout`, `Stderr`, `Stdin`, `Error` (R39-40) |
| `fs.fors` | `std.fs` | `Dir`, `File`, `Entries`, `Meta`, `Error`, the comptime read (R41-42) |
| `net.fors` | `std.net` | `Net`, `Addr`, `Conn`, `Listener`, `Error`, `TimeoutError` (R43) |
| `proc.fors` | `std.proc` | `Exec`, `Child`, `hardware_threads` (R44, R50) |
| `time.fors` | `std.time` | `Clock`, `Instant`, `Wall`, `Duration` (R45) |
| `rand.fors` | `std.rand` | `Rng` (entropy, authority), `Pcg` (deterministic) (R47) |
| `env.fors` | `std.env` | `Env`, `Args`, `Error` (R46) |
| `gpu.fors` | `std.gpu` | `Device`, `Info`, `Error` (R48) |
| `ffi.fors` | `std.ffi` | `CStr`, `Error`; holds the sealed `ffi` capability (R49) |

## The two invariants of this tree

1. **No ambient authority, no ambient allocation** (ch10 R3, R54). A
   function that takes neither a capability value nor an allocator value
   does neither.
3. **The import graph is acyclic and every `use` is absolute** (ch08 R3,
   R7): `std.mem` imports its five submodules, `vec`/`hashmap`/`text`
   import only the leaves `alloc` and `seq`, no submodule imports
   `std.mem`, and a std file writes `use std.io;` exactly as a user does.
2. **The capability words a std module declares are Rule 53's and no
   others**: `needs { syscall };` in `io fs net proc time rand env gpu mem`,
   `needs { ffi };` in `ffi`, `needs { };` everywhere else. Both are sealed
   (ch04 R2-2b), so no importer of std inherits them.
