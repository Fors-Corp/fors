# Fors design: the M2 dev backend (`fors-oir`, `fors-codegen-dev`, `fors-abi`, `fors-obj`, `fors-link`, `fors-dwarf`)

> **Status: implementation design, 2026-10-04, base `main` 1d858b8 (compiler 0.22.0).** An
> implementation CONTRACT in the genre of `docs/design/type-checker.md` and
> `docs/design/fmir-interpreter.md`: crates, data, a rule-to-code table, numbered increments each
> gated on NAMED tests or measurements, a per-phase time budget, ranked risks with the measurement
> that retires each, and the owner questions that genuinely need Marc. Normative inputs:
> `docs/PLAN.md` §4.1, §4.2 (R4, R5, R7, R9, R10, R13), §4.3 (rounds 4, 9, 11) and §5's M2 row;
> `docs/spec/02-failure.md`, `03-numerics-determinism.md`, `05-ir-contract.md`, `06-measurement.md`,
> `10-std.md` R40; `docs/design/compiler-architecture.md` §1, §2, §4, §6, §7, §9;
> `docs/design/fmir-interpreter.md` §3, §5, §7. Where this conflicts with a spec chapter the chapter
> wins; where it conflicts with PLAN §4 the plan wins. Owner decisions this design takes as FINAL:
> no LLVM in the dev tier, ever (Cranelift is the pre-registered M5a release fallback, not M2 — relayed
> as PLAN round 10; that round is not yet written into `docs/PLAN.md` at 1d858b8, see §13); **std is
> always in the build**; **`IndexMut::at_mut` is inlined by lowering as a place computation, FMIR stays
> value-only**; the Iterator-identity change is deferred until after this design.

Contents: §1 facts verified · §2 architecture · §3 the ABI · §4 Mach-O, signing, incremental link,
DWARF · §5 differential testing · §6 the 50 ms budget and the compile-speed protocol · §7 the matmul
checkpoint · §8 `secret` / `ct_region` · §9 rule-to-code table · §10 increments M2-0 … M2-12 ·
§11 risks · §12 owner questions · §13 engineering calls made here.

---

## 1. Facts this design rests on (checked against the tree at 1d858b8)

- **`crates/fors-asm`** (4.2k lines, zero deps) encodes every instruction M2 needs for integers,
  scalar floats, loads/stores (GP and FP, all addressing modes), branches (`b`, `bl`, `b.cond`,
  `cbz`, `tbz`, `ret`, `blr`), `adr`/`adrp`, `csel` family, `smulh`/`umulh`, `sdiv`/`udiv`/`msub`,
  `brk`/`svc`/`udf`. It is verified byte-for-byte against the system assembler (`tests/oracle.rs`,
  macOS) and replayed from golden files on Linux. **Missing:** `MRS`/`MSR` (needed for `FPCR.DN` and
  `PSTATE.DIT`) and every Advanced-SIMD vector form. Both are small additions to an existing shape.
- **`spikes/aarch64-macho`** (2.2k lines) wrote a signed `MH_EXECUTE` that macOS runs with an empty
  `PATH`: `LC_MAIN`, `LC_LOAD_DYLIB libSystem` with **no imports**, an empty chained-fixups blob, a
  minimal exports trie, an ad-hoc `linker-signed` CodeDirectory v0x20400. Its pitfalls are recorded
  (section_64's third reserved field; page-0 fields must be final before hashing). Its runtime used
  raw `svc #0x80` from a pre-assembled blob, and its UUID was SHA-256 of `__text` only.
- **`spikes/macho-resign`**: clone to a NEW inode + patch + rehash dirty CodeDirectory slots + rename
  is correct 31/31; patching the same inode after it executed is SIGKILLed **non-deterministically**
  (~60%). CodeDirectory page size is **4096** (log2 field 12), not the 16 KiB VM page. Cost
  0.54/1.00 ms (median/p95) for a 1 MB image, 1.25/1.93 ms for 50 MB — in Python.
- **`crates/fors-fmir`**: SoA `DeclFmir`; `ValRow { ty, flags (SECRET|…), ct, def }` with `SECRET`
  and `ct` non-optional (ch05 R6); 71 opcodes (`op.rs`), `ArithMode {Trap, Wrap, Sat, Unchecked}`,
  `TrapKind` with exactly eight discriminants `Bounds=0 … EmptyReduce=7`; `AliasSeed` carries the five
  ch05 R5 sources; a verifier; a textual dump **and parser** (so FMIR fixtures can be written by hand).
- **`crates/fors-interp`** is the oracle. `arith.rs` is the executable definition of every integer
  and float op (`trap_*`, `wrap_*`, `sat_*`, `conv_*`, `fcmp`, in-crate exact `frem`); a trap prints
  `trap: <kind> at <file>:<L>:<C>` and exits by `raise(SIGTRAP)`; `OracleRecord` is exit + stdout +
  stderr bytes. The generator's output intrinsics are the named rows `stdout_write_uint` and
  `stdout_write_line`.
- **`crates/fors-oracle`**: the FMIR generator (`generate(seed)`, UB-free and trap-free by
  construction; ints `i64 u64 i32 u32 i16 u16 u8`; `ConstInt`, all arith ops in `Trap`/`Wrap`/`Sat`
  with masked operands, `And/Or/Xor/Not`, `Icmp`, `ConvWrap/ConvSat/ConvChecked`, `CopyFrom`/`Init`
  on scalar local places, `CondBr`/`Br`, bounded loops, `CallDirect` to lower-numbered helpers, and
  the two output intrinsics); the differential runner (`diff.rs`, today interp-vs-replay); the
  three-stage reducer (`reduce.rs`). 10⁵ programs ran clean in 36 s at F10.
- **`crates/fors-query`**: the content-hash engine (`QueryKey`, `ValueHash = u128`, red-green with
  early cutoff). The Fors query set lives in `fors-check/src/queries` with kinds 0–23
  (`SOURCE_TEXT` … `CHECK_BODY = 22`, `LOOSE_DIAGS = 23`). **Lowering is not a query yet**, and I9
  shipped resolve and the signature phase as **whole-build** nodes with the note "M2 makes them
  per-module".
- **Measured frontend cost:** a 105k-line corpus checks clean cold through the DAG in **~0.3 s**
  (CHANGELOG, I9); 110k lines parse in ~21 ms; index+resolve 43–44 ms at I0.
- **`bench/compile-speed/`**: `compile_speed.py` (flat many-function corpus, `--sizes 100000`) and
  `incremental.py` (M modules × F functions, the five edit classes E1–E5 of ch06, adapters for C,
  Rust, Go, Zig, Java). **Neither has a Fors adapter.** `crates/fors-check/tests/scale.rs` has a
  105k-line Fors corpus, but it is checker-only: no runnable `main`, no checksum.
- **`bench/kernels/matmul-blocked`** exists (BLOCK = 64, i-k-j inside tiles, N = 1800 bench / 64
  check, threads [1,2,4,6,8], prints sum and trace as integers). The C baselines are `-O3` only;
  there are no `-O0`/`-O1` rows in `bench/langs/`.
- **`std/env.fors`**: `Args.len`/`Args.at` are stubs. There is no unchecked index anywhere in the
  spec or std, and the spec says nothing about stack exhaustion.
- **CI is Linux only.** Nothing that executes an aarch64 Mach-O can run there.

---

## 2. Architecture

### 2.1 The pipeline, level by level

```
FMIR (fors-fmir, per declaration / instantiation, content-hashed)
  │  fors-oir::from_fmir         linear, no optimisation, no mem2reg
  ▼
OIR  (fors-oir)                  CFG; FMIR values stay SSA values; places become frame slots;
  │                              every memory row carries an alias class (R4/R5);
  │                              every value row carries secret + ct (R6)
  │  fors-codegen-dev::select    one OIR row -> one stencil instance (no allocation)
  ▼
LIR-dev (fors-codegen-dev::lir)  SoA rows: (stencil id, holes, secret mask, ct)
  │  fors-codegen-dev::emit      memcpy pre-encoded stencil words, patch holes
  ▼
Atom (code + cold trap tail + literal pool + trap table, relocs list)
  │  fors-link::plan / place     atom slots, call-stub table, pc-relative patching
  ▼
Image (fors-obj)                 MH_EXECUTE, chained fixups, exports trie, ad-hoc signature
  │  fors-link::relink           clonefile -> patch dirty pages -> rehash slots -> rename (new inode)
  ▼
<exe>  +  <exe>.dSYM (fors-dwarf, unsigned sidecar)
```

**Why OIR is not skipped.** ch05 R1 is a MUST: "exactly tokens → AST → FIR → FMIR → OIR → LIR →
atoms; no pass MUST touch a level out of order". R4 (alias class on every OIR memory op) and R6
(secret + ct on every OIR/LIR value) are verifier obligations on those levels. Skipping OIR in the
dev tier would need a spec amendment and would leave R4/R6 with no home until M5. The cost of
honouring R1 is small because FMIR already has SSA-shaped values (`ValRow.def`, phis in
`operands`) and keeps mutable state in places: `from_fmir` is one linear pass that copies value
rows, turns each place root into a frame slot and each `CopyFrom`/`Init`/`MoveFrom` into
`slot_load`/`slot_store`, and attaches an alias class derived from the FMIR `AliasSeed`. **What OIR
adds over FMIR:** explicit frame slots, alias-class operands, low types (`i8..i64`, `f32`, `f64`,
`ptr`), lowered aggregates (field/index become address arithmetic over `fors-layout` offsets), the
ABI-visible shape of calls (from `fors-abi`). **What OIR removes:** the scope tree, `DeferPool`,
`try_br`'s structured meaning (it becomes a tag test on `x9`, §3), conventions (already discharged),
everything the interpreter needs for Miri-class detection (`init` bits, provenance). Budget: ≤ 0.4 µs
per FMIR instruction (≈ 2 ms at the 5k-instruction worst edit, §6.2). Optimisation passes over OIR
are M5's; the dev tier runs **none**.

**What "copy-and-patch" means here.** Xu & Kjolstad's stencils are compiled by clang at build time;
with no LLVM and no executable build steps we cannot do that. We keep the mechanism and drop the
generator: a **stencil** is a short instruction sequence written once in Rust with `fors-asm`
constructors, encoded once (lazily, into a `static` table) with placeholder field values, and
described by a list of **holes** (`SlotOff12 @ word 0 bits 10..21`, `Imm16 @ word 2`, `Branch19 @
word 3 -> trap tail`, …). Instantiation is `copy_from_slice` of the words plus a bit-field insert per
hole. A golden property test (`stencils_match_fors_asm`) proves every stencil instantiation equals
`fors_asm::encode` of the same sequence with the same field values, so the encoder stays the single
source of truth and the fast path cannot drift from it.

**Code model, stage A (M2-0 … M2-10): stack-slot templates.** Every OIR value owns an 8-byte frame
slot; a stencil loads its operands into fixed scratch registers, computes, and stores its result —
`-O0`-class code, simple, obviously correct, and fast to emit. **Stage B (M2-11): a block-local value
cache** (Liftoff-style): within one basic block a value stays in its scratch register until evicted
(LRU) or the block ends; every value live out of the block is in its slot at the terminator. No
global allocation, no cross-block state, so the emitter stays linear and the stencils stay
position-free. Stage B is required for the matmul checkpoint (§7) and for nothing else in M2.

### 2.2 Crates

All new crates: edition 2024, **zero external dependencies**, workspace-only path deps,
`#![deny(unsafe_code)]` except the single FFI declaration named below.

| Crate | Owns | Depends on | Est. size |
|---|---|---|---|
| **`fors-abi`** (new) | the aarch64-apple Fors calling convention as data: argument/result register tables, the ch02 R4 failure classifier (`FAILURE_INLINE_MAX = 24`, `FAILURE_TAG_REG = 9`), frame rules, `TRAP_BRK_BASE`; register numbers as `u8` (no `fors-asm` dep, so it stays target data) | `fors-layout` | ~500 |
| **`fors-oir`** (new) | OIR data model (SoA like FMIR), `from_fmir`, the OIR verifier (R4, R5, R6, R12 `tile.*` absent), text dump | `fors-fmir`, `fors-fir`, `fors-layout`, `fors-abi` | ~1.8k |
| **`fors-codegen-dev`** (new) | stencils, `select` (OIR → LIR-dev), `emit` (LIR-dev → atom), frame layout incl. the secret slot class, the block-local value cache (M2-11), the dev-tier CT check (M2-10), the runtime atoms (`rt/`: entry shim, trap handler, write routines) built with `fors-asm` | `fors-oir`, `fors-abi`, `fors-asm`, `fors-fir`, `fors-layout` (dev-dep: `fors-interp` for `arith.rs` edge tables only) | ~4k by M2 exit |
| **`fors-obj`** (new) | Mach-O writer: header, load commands, segments/sections, chained fixups (binds + rebases), exports trie, function starts, minimal symtab, ad-hoc CodeDirectory, in-house SHA-256 (ARMv8 SHA2 via `std::arch` on aarch64, portable fallback), MH_DSYM container for the sidecar | — | ~2k |
| **`fors-link`** (new) | atom placement, call-stub table, pc-relative patching, the image directory, the incremental relink (clonefile → patch → rehash → UUID → rename → inode assert), clonefile fallback reporting. The one `unsafe` block: `extern "C" { fn clonefile(...) }` from libSystem (no crate) | `fors-obj`, `fors-asm` | ~1.2k |
| **`fors-dwarf`** (new) | DWARF 5 sidecar: `.debug_info/.debug_abbrev/.debug_line/.debug_str/.debug_line_str/.debug_addr`, per-module CU blobs cached by content | — (written into `fors-obj`'s MH_DSYM by `fors-link`) | ~1.2k |
| **`fors-driver`** (new, M2-8) | the resident build daemon (unix socket, same `Db` as `fors build`), `--no-daemon` | `fors-check`, `fors-lower`, `fors-codegen-dev`, `fors-link`, `fors-dwarf`, `fors-query` | ~800 |
| `fors-oracle` (extend) | `native.rs`: compile → image → spawn → `NativeRecord`; native predicate for the reducer; generator `Profile` | + `fors-codegen-dev`, `fors-link` | +~800 |
| `fors-lower` (extend) | `at_mut` inlined as a place computation (owner decision); render function synthesis for `main`'s error type (M2-5); new intrinsic rows `args_len`/`args_at` | unchanged | +~600 |
| `fors-cli` (extend) | `fors build` → native executable; `fors run --native`; `--timings=json` phases of §6.2 | + the new crates | +~400 |

Layering invariants, each a CI grep test like the FMIR ones: `fors-codegen-dev`, `fors-oir`,
`fors-link`, `fors-obj` mention neither `fors_check` nor `fors_syntax` nor `fors_interp` in `src/`
(the backend must not see the oracle or the source); no `HashMap`/`HashSet`/`RandomState` in any
backend `src/` (determinism, as in `fors-interp`); `svc` is emitted by no crate after M2-3
(`image_contains_no_svc`, PLAN R9's syscall scan).

`compiler-architecture.md` §9 lists `fors-lir` and `fors-target-aarch64` as separate crates. The dev
tier's LIR (stencil instances) and the release tier's LIR (vregs, regalloc) share nothing but the
name, so M2 keeps LIR-dev as a module of `fors-codegen-dev` and leaves `fors-lir` to M5. Engineering
call E3 (§13).

### 2.3 Query-engine integration

New query kinds appended after `LOOSE_DIAGS = 23` in `fors-check/src/queries/mod.rs` (they live there
because the query set does; the computations call into the new crates):

| Kind | Key | Value (`ValueHash`) | Reads | Re-executes on |
|---|---|---|---|---|
| `LOWER_BODY = 24` | decl / instantiation | `fmir_hash` | `CHECK_BODY`, `SIGNATURE_OF` of callees | any body or callee-signature change |
| `FMIR_CODE_KEY = 25` | same | hash of the FMIR with `SitePool` spans **excluded** | `LOWER_BODY` | code-affecting changes only |
| `OIR_OF = 26` | same | OIR hash | `FMIR_CODE_KEY`, callee ABI shapes | as above |
| `ATOM_CODE = 27` | same | hash of atom bytes + relocs | `OIR_OF`, `target_hash` | as above |
| `ATOM_SITES = 28` | same | hash of the atom's trap-site rows (`kind`, line relative to the declaration, col) | `LOWER_BODY` spans | any span move inside the body |
| `DECL_LINE = 29` | decl | the declaration's first line | `DECL_KEYS` | a line shift above the declaration |
| `IMAGE_PLAN = 30` | unit | hash of the sorted atom set (key, size class) | all `ATOM_CODE` sizes | atom added/removed/outgrew its slot |

The **link is not a query** (queries are side-effect free): after `demand(IMAGE_PLAN)` the driver
asks `Db::executed_of_kind(ATOM_CODE | ATOM_SITES | DECL_LINE)` for this revision and hands exactly
those atoms and table rows to `fors-link::relink`. Consequences, each a set-equality gate in M2-8:

- **body edit** → re-executes `PARSE(file)`, `DECL_KEYS`, `CHECK_BODY(d)`, `LOWER_BODY(d)`,
  `FMIR_CODE_KEY(d)`, `OIR_OF(d)`, `ATOM_CODE(d)`, `ATOM_SITES(d)`; relink patches one atom slot (or
  moves it and rewrites one stub) — **one function re-emitted, one image patched**;
- **comment/whitespace edit** → `FMIR_CODE_KEY` is unchanged, so **zero** `OIR_OF`/`ATOM_CODE`
  executions; `DECL_LINE` changes for declarations below the edit in that file, and `ATOM_SITES` only
  for the declaration containing the edit — the trap tables are deliberately split so a comment edit
  dirties one or two signed pages, not every function below it (§4.3);
- **private signature edit** → the declaration plus its in-module callers;
- **public signature edit** → the declaration plus every caller across modules (E4 leaf, E5 core).

Call targets are reached through a **stub table** (§4.3), so `ATOM_CODE(d)` never depends on any
other atom's address: that is what makes a body edit re-emit exactly one function. Callee
*signatures* (ABI shape) are dependencies; callee *bodies* are not.

---

## 3. The ABI the dev backend implements

Every choice is traced to a rule, or marked **[open → rec]** with the recommendation taken.

| Item | Choice | Source |
|---|---|---|
| Integer/pointer arguments | `x0..x7`, in order; further arguments on the stack at `[sp, #8k]` of the caller's outgoing area | AAPCS64; `compiler-architecture.md` §7 |
| Float arguments | `d0..d7` / `s0..s7`; further on the stack | AAPCS64 |
| Narrow integers in registers and slots | **canonical extended form**: sign-extended to 64 bits for signed types, zero-extended for unsigned, at every call boundary and in every slot | **[open → rec]** stronger than Apple's 32-bit caller extension, so a Fors value is always a valid C argument; makes 64-bit `cmp` correct for every width and makes the narrow overflow check one `cmp x, w, sxt{b,h,w}` (E5, §13) |
| Non-raising return | scalar in `x0`/`d0`; aggregates ≤ 24 B in `x0..x2`; larger via caller-allocated `sret` in `x8` | **[open → rec]** use ch02 R4's threshold for every Fors-internal return so raising and non-raising functions share one classifier; `extern "c"` uses Apple AAPCS64 (≤ 16 B in `x0/x1`) unchanged |
| Raising return (`raises E`) | `payload = max(size_of T, size_of E)`; ≤ `FAILURE_INLINE_MAX` (24): payload in `x0..x2`, else `sret` in `x8`; tag in **`x9`**, `0` = success | ch02 R4 (normative), PLAN R4 |
| `try_br` / `?` | after `bl`: `cbnz x9, Lerr` (one instruction); `Lerr` is the FMIR `err` edge with its inlined `errdefer` blocks | ch02 R4, R16; fmir-interpreter §3.6 |
| Scratch registers | GPR `x10..x15`, FP `d16..d31`; `x9` is the failure tag and is clobbered freely except between a callee's `ret` and the caller's tag test | **[open → rec]** `compiler-architecture.md` decision point `fors-codegen-dev/src/regs.rs` names this constant as Marc's; recommendation keeps `x9` out of the scratch set so the tag can never be overwritten by a template |
| Reserved | `x16/x17` (IP0/IP1) belong to `fors-link`'s stubs; **`x18` is never touched** (Apple platform register); `x19..x28` unused by the dev tier (no callee-saved spills needed) | Apple arm64 ABI |
| Frame | `stp x29, x30, [sp, #-16]!; mov x29, sp; sub sp, sp, #F` with `F` a multiple of 16; slots at `[sp, #8k]` (`k < 4096`; larger frames add one `add x17, sp, #hi, lsl #12` per access, refused in M2-0); epilogue `mov sp, x29; ldp x29, x30, [sp], #16; ret` | AAPCS64 16-byte alignment; **x29 chain always valid** (`compiler-architecture.md` decision "Backtraces and frame pointers") |
| Red zone | **not used** (Apple permits 128 B below `sp`) | engineering call E6: the secret-slot zeroisation (§8) must cover every byte a secret can occupy, and a red-zone byte is outside the frame |
| Unwinding | **none**: no `__eh_frame`, no `__unwind_info`, no personality, no landing pad, no LSDA | ch02 R7, R14 |
| Trap | the check branches to a per-site `brk #(TRAP_BRK_BASE + kind)` in the function's cold tail, `TRAP_BRK_BASE = 0x4600`, `kind` = `fors_fmir::TrapKind` discriminant (0..7); the site also gets one trap-table row (§4.3). One instruction per site, no call, no allocation | ch02 R6, R15 |
| Trap reporting | the runtime's `SIGTRAP` handler (installed by the entry shim) reads `uc_mcontext.__ss.__pc`, finds the atom by binary search in the image directory, finds the site in the atom's table, writes **exactly** the interpreter's line `trap: <kind> at <file>:<L>:<C>\n` to fd 2 with one `write`, restores `SIG_DFL`, and returns; the `brk` re-executes and the process dies by `SIGTRAP` | ch02 R7; ch10 R40(b),(d); fmir-interpreter §5.3, §7.2a (the trap line is part of R17's byte comparison) |
| Backtrace | only with `FORS_BACKTRACE=1`, walking `x29`; never in the differential corpus | round 11 Q7 |
| Floating-point environment | entry shim sets `FPCR`: RN rounding, `FZ = 0`, **`DN = 1`** (aarch64's default NaN is sign 0, quiet, payload 0 — exactly Q2's canonical NaN); no FMA is ever emitted | ch03 R7; round 11 Q2; PLAN §4.3(1) |
| Entry | `LC_MAIN` → runtime `_main` (not Fors source): FPCR, `SIGPIPE → SIG_IGN`, `SIGTRAP` handler, terminal detection for fd 1, root capabilities by type, call Fors `main`, then ch10 R40(a)/(d) or ch02 R17's error path, return the status to dyld | ch04 R7; ch02 R17; ch10 R40 |
| Stack exhaustion | **[open — owner Q5]** today: guard-page `SIGSEGV`/`SIGBUS`, undefined by the spec; the interpreter refuses at 1024 frames | spec silent |

---

## 4. The Mach-O story

### 4.1 Image layout (cold build)

| Segment | Prot | Sections | Contents |
|---|---|---|---|
| `__PAGEZERO` | — | — | 4 GiB |
| `__TEXT` | r-x | `__text` | `[stub table][runtime atoms][Fors atoms, one slot each, grouped by module, modules in module-graph order, declarations in `DeclKeyId` order]` |
| | | `__fors_dir` | image directory: `(atom start, atom len, decl_line_row)` sorted by address, 16 B/atom |
| | | `__fors_lines` | per-declaration first lines + file-name table, grouped by file |
| `__DATA_CONST` | rw→ro | `__got` | imported symbols (chained-fixup binds), from M2-3 |
| `__DATA` | rw | `__data` | only if a program needs mutable statics (none in v0.1's corpus; witness/closure tables go to `__DATA_CONST` with rebases) |
| `__LINKEDIT` | r | — | chained fixups, exports trie (`__mh_execute_header`, `_main`), function starts, a minimal symtab (exports only; full names live in the sidecar), code signature (last) |

**An atom** is `[code][cold trap tail: one brk per site][literal pool: string and float constants]
[trap table: (pc offset u32, site ordinal u16, kind u8, col u16, line relative to declaration u32)]`,
padded to its slot (`round_up(1.25 × len + 64, 16)`). Constants are reached with `adr`/`ldr
(literal)`, so **an atom is position-independent** except for its `bl stub[k]` calls, which `place`
re-patches when an atom moves. Stubs are `b atom` (one word each) in a table of fixed capacity at
the start of `__text`; outgrowing the capacity is a full relayout, counted in `--timings`.

**Load commands** (spike-proven set): `LC_SEGMENT_64` ×4–5, `LC_DYLD_CHAINED_FIXUPS`,
`LC_DYLD_EXPORTS_TRIE`, `LC_SYMTAB`, `LC_DYSYMTAB`, `LC_LOAD_DYLINKER`, `LC_UUID`,
`LC_BUILD_VERSION` (platform macOS, `minos = MACOS_MIN = 14.0`, sdk 0, no tools), `LC_SOURCE_VERSION
0`, `LC_MAIN`, `LC_LOAD_DYLIB /usr/lib/libSystem.B.dylib` (timestamp field fixed at 2, as ld64
writes), `LC_FUNCTION_STARTS`, `LC_CODE_SIGNATURE`. Flags `MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL |
MH_PIE`. Chained-fixup format `DYLD_CHAINED_PTR_64_OFFSET` (6), imports `DYLD_CHAINED_IMPORT`.

### 4.2 Signature and reproducibility

- **Ad-hoc, linker-signed**: CodeDirectory v0x20400, flags `0x20002` (adhoc | linker-signed), SHA-256,
  page size 4096, `execSeg` base 0 / limit = `__TEXT` filesize / `CS_EXECSEG_MAIN_BINARY`, no special
  slots, identifier = the output's file stem (documented: renaming the output changes the bytes).
- **No timestamps anywhere**; no host path in the signed image (file names in trap rows are the
  package-relative paths the interpreter prints); zero padding; every table sorted.
- **UUID derived from content, in O(pages):** `UUID = SHA-256( H(page₀ with the UUID field zeroed and
  the signature fields final) ‖ H(page₁) ‖ … ‖ H(pageₙ) )[0..16]` with the RFC 4122 version nibble set
  to 8 ("custom"). The page hashes are exactly the CodeDirectory slots, which the relink already has,
  so the UUID never needs a pass over the whole file; page 0 is rehashed last.
- **Scope of bit-identity**: a cold `fors build` is a pure function of (sources, std, target,
  compiler version) — `--check-repro` builds twice into different directories and compares bytes.
  An incrementally relinked image is deterministic given (previous image, edit) and semantically
  equal to the cold image, but **not** byte-equal (atom moves). Owner Q4 asks whether that is
  acceptable; it is the recommendation.

### 4.3 The incremental relink

Per edit, after the query demand (§2.3):

1. `plan`: for each re-emitted atom, keep its slot if it fits, else append a new slot at the end of
   `__text` (old slot becomes a dead gap, zero-filled) and mark its stub dirty; rewrite changed
   `__fors_dir` / `__fors_lines` rows. If `__text` must grow past its segment's reserved virtual
   size, fall back to a full relayout (reported).
2. `clonefile(prev, tmp)` — O(1) on APFS. On failure (non-APFS) copy and report
   `link.clone = fallback-copy` in `--timings`; never silently.
3. Patch the dirty byte ranges in `tmp`; the dirty **4 KiB** page set is derived from the actual
   ranges written (the spike's caveat: never from a guess).
4. Rehash only those CodeDirectory slots (all CDs present; ad-hoc only — any other signature refuses
   incremental relink and re-signs fully), recompute the UUID (§4.2), patch `LC_UUID`, rehash page 0.
5. `rename(tmp, out)`; then `stat(out).ino != ino_before` is **asserted** — an unchanged inode is a
   hard error, never success (`macho-resign` REPORT: in-place patching of an executed inode is
   SIGKILLed non-deterministically).
6. The sidecar (§4.4) is updated after step 5 and before the next edit is accepted; it is not on the
   build-done critical path because nothing in the image depends on it.

`fors-link::rehash_dirty_pages()` is a PLAN §5 learning-mode contribution point (owner Q7).

### 4.4 DWARF sidecar (ch05 R18, PLAN R13)

- Written to `<exe>.dSYM/Contents/Resources/DWARF/<exe>` (an `MH_DSYM` Mach-O with the same
  `LC_UUID`, a full `LC_SYMTAB`, and a `__DWARF` segment) plus `Info.plist`. lldb discovers an
  adjacent dSYM and matches it by UUID without `dsymutil`. **Unsigned**, so no debug edit can touch a
  CodeDirectory.
- One CU per module, cached as a content-addressed blob; addresses go through `.debug_addr`
  (`DW_FORM_addrx`) so an atom move rewrites one 8-byte entry, and line-program sequences start with
  `DW_LNE_set_address` whose operand offsets are recorded and patched in place.
- Frame base `DW_OP_breg29`; locals are frame slots (`DW_OP_fbreg`) — every stage-A value has a home,
  which is what makes `frame variable` work in a dev build.
- `comp_dir` is `.`; no absolute paths — the sidecar is reproducible too.
- What a debug-info-only edit is: renaming a local, or any edit that changes names but not
  `FMIR_CODE_KEY` **and** moves no trap site. A comment edit above a trap site is NOT debug-only:
  the trap line number is program-observable (it is in the oracle's stderr bytes), so it dirties
  `__fors_lines` — by design, one or two pages.

---

## 5. Differential testing from instruction one

**The comparison.** `fors-oracle::native::run(&Candidate) -> NativeRecord { exit: Status(u8) |
Signal(i32) | Timeout, stdout, stderr }`, compared with the interpreter's `OracleRecord`: exit
(`Normal(n)` ↔ `Status(n)`, `Trap{kind}` ↔ `Signal(SIGTRAP)` with the last stderr line equal byte for
byte), stdout bytes, stderr bytes. `steps` and `heap_digest` are never compared (no native
counterpart). Children run with an empty environment, stdin `/dev/null`, a 10 s timeout, in a
per-run scratch directory.

**The corpora, in the order they come online.**

| Corpus | From | Size at M2 exit |
|---|---|---|
| `arith` edge tables: one program per (type, op, mode), all pairs of `interesting()` values, every result printed | M2-0 | 7 int types × ~40 (op, mode) + float rows from M2-6 |
| generator, `Profile::STRAIGHT_LINE` (no branches, loops or calls) | M2-0 | 10⁴ seeds per CI run on macOS, 10⁵ on the pinned box |
| generator, full profile (today's `generate(seed)`, unchanged) | M2-2 | 10⁵ seeds, the F10 count |
| generator, aggregates/memory profile (arrays, structs, enums, slices, `at_mut` places) | M2-4 | 10⁵ |
| generator, float profile (strict ops, conversions, NaN-producing ops) | M2-6 | 10⁵ |
| hand-written FMIR fixtures (`.fmir` text, parsed by `fors-fmir`) for every trap kind | M2-2 → M2-5 | 8 kinds × ≥ 2 sites |
| the 64 runtime conformance tests through `fors build` | M2-5 | 64 (the 5 pinned stay pinned with their assertion) |
| `tests/conformance/05-ir/` backend-observable files | M2-4, M2-9, M2-10 | `ir-verify-*`, `backend-bitforbit-agreement`, `dwarf-companion-unsigned`, `ct-denylist-rejected` |

**`Profile`.** `generate(seed)` stays byte-for-byte what it is today (existing seeded tests are the
gate); a new `generate_with(seed, &Profile)` takes switches (`branches`, `loops`, `helpers`,
`aggregates`, `floats`, `ops: OpSet`). The full profile **is** `generate`.

**The reducer.** `reduce_fmir`/`reduce_values` already take a predicate. The native predicate is
`|c| record(interp, c) != record(native, c)`, both under `REDUCE_STEP_CAP` / the timeout. A candidate
costs ~1 ms compile+link+sign in-process plus ~2–4 ms spawn+dyld, so a 1,000-candidate reduction is
seconds. Gate: a test-only cargo feature `inject-miscompile` (refused by a `compile_error!` outside
`cfg(test)`, the F10 pattern) seeds stencil bugs; each must reduce to **< 30 FMIR instructions**.

**Throughput.** Spawn dominates: ~4 ms/program → 10⁵ programs ≈ 7 min on one core, ≈ 1 min on 8
workers. Results are tallied by seed, so the tally is independent of worker count.

**Determinism, checked four ways.** (1) `codegen_is_deterministic`: compile the same candidate twice
in-process and in two processes — identical image bytes; (2) `--check-repro`: two cold builds into
different directories — identical bytes; (3) every native run twice — identical records; (4)
incremental-vs-cold: after every step of an edit script, the relinked image's record equals the cold
image's record and the interpreter's.

**Where the native runs happen.** Only macOS/aarch64 can execute the images. Every native test is
`#[cfg(all(target_os = "macos", target_arch = "aarch64"))]`; Linux CI still runs everything that does
not execute (OIR verifier, stencil goldens, byte-golden images, determinism of bytes). Owner Q3 asks
for a GitHub `macos-14` (Apple-silicon) job so the differential becomes a merge gate.

**Spec holes the differential will hit** (resolve before the generator emits them natively): unsigned
`neg` in `Trap`/`Sat` mode (the interpreter wraps; F10 flagged it — owner Q6); stack exhaustion (owner
Q5; the generator has no recursion, so it is reached only by hand-written tests).

---

## 6. The 50 ms p95 budget and the compile-speed protocol

### 6.1 The fixture

There is **no** runnable 100k-line Fors fixture today (§1). M2-12 adds a `fors` adapter to
`bench/compile-speed/incremental.py` (the comparator: identical call graph in C, Rust, Go, Zig, Java,
Fors; checksum verified against the script's pure-Python reference) and to `compile_speed.py` +
`bench/langs/fors.toml`. The project shape is a pure function of `(seed, M, F)` through the script's
own minstd stream; `M = 200` modules and `F` chosen so that the **Fors** source is ≥ 100,000 lines
(the adapter prints the exact count into the results JSON; every language uses the same `M, F`).
std is part of every Fors build (owner decision), so the corpus exercises std's natively compiled
`io` too.

### 6.2 Per-phase allowances (daemon row, pinned M1 Pro, one edit)

The plan's p95 is over the **mixture** of the five edit classes; with equal weights each class is 20%
of the samples, so the pooled p95 is roughly the 75th percentile of the slowest class (E5). The budget
is therefore set per class, and E5 must fit.

| Phase (`--timings=json` name) | E1 comment | E2 body | E3 private sig | E4 public sig leaf | E5 public sig core |
|---|---:|---:|---:|---:|---:|
| `rpc` client→daemon, revision bump, read file | 1.0 | 1.0 | 1.0 | 1.0 | 1.0 |
| `parse` lex + parse the changed file (≤ 2k lines; 110k lines = 21 ms measured) | 0.5 | 0.5 | 0.5 | 0.5 | 0.5 |
| `keys` declaration index, keys, early cutoff | 0.5 | 0.5 | 0.5 | 0.5 | 0.5 |
| `resolve` (**per-module**, M2-8) | 0.2 | 0.5 | 0.5 | 1.5 | 4.0 |
| `check` signatures + affected bodies | 0 | 1.0 | 2.0 | 4.0 | 10.0 |
| `lower` FMIR + verify | 0 | 0.5 | 1.0 | 2.0 | 5.0 |
| `oir` build + verify | 0 | 0.2 | 0.3 | 0.6 | 2.0 |
| `codegen` select + emit | 0 | 0.2 | 0.3 | 0.6 | 2.0 |
| `plan` atoms, stubs, tables | 0.3 | 0.3 | 0.3 | 0.5 | 1.0 |
| `relink` clone, patch, rehash, UUID, rename, inode check | 2.0 | 2.5 | 2.5 | 3.0 | 4.0 |
| **sum** | **4.5** | **7.2** | **8.9** | **14.2** | **30.0** |
| slack to 50 | 45.5 | 42.8 | 41.1 | 35.8 | 20.0 |
| `dwarf` sidecar (after build-done, reported separately) | 1 | 2 | 2 | 3 | 10 |

The `relink` row is the spike's Python numbers (0.54/1.00 ms at 1 MB, 1.25/1.93 ms at 50 MB) plus
Rust SHA-256 over ≤ 8 dirty pages; it is the one row already measured. Every other row is an
estimate from data size and must be replaced by measurement in M2-8 before the gate run.

**Where the plan's number looks unattainable, and what would show it.** (a) **The `--no-daemon`
row cannot meet 50 ms in M2**: without the daemon there is no warm `Db`, and no on-disk query cache
exists, so a no-daemon "incremental" build is a cold build (~0.5 s at 100k lines by §6.4). ch06 R13
requires that row to be published; owner Q1 asks which row the gate binds. (b) **E5 depends on fan-out
I have not measured**: if a core signature edit re-checks more than ~2,000 declarations the `check`
row alone exceeds 20 ms. The retiring measurement is M2-8's per-class counter test (re-executed
`CHECK_BODY` count per edit class at 100k lines) taken *before* the timing run. (c) Today resolve and
the signature phase are whole-build nodes: index+resolve alone measured 43–44 ms at I0, so **the
gate is unreachable until M2-8 makes them per-module** — that is why it is an increment, not a
footnote.

### 6.3 Measurement protocol

Pinned M1 Pro, on AC, idle, nothing concurrent (ch06 R20), thermal canary interleaved (R21), noise
floor measured with no-op rebuilds and published (R19). For each language: one cold build (variant
stated, §6.4), three discarded warm-up edits, then ≥ 20 edits **per class**, classes interleaved in a
seeded round-robin, each timed wall-clock from the edit's write to the executable being in place
(link and, for Fors, rename included — ch06 R10). Then the program runs and its checksum is verified;
**edit-to-test-result** latency = build + run-to-verified-checksum, reported beside raw build time
(R14). Report p50/p95 per class and pooled (R12), daemon and `--no-daemon` rows side by side with
daemon RSS and first-build-after-start (R13). Named comparator rows: **Go `gc`** (`go build`, the G3
baseline) and **Zig** (self-hosted debug backend, `zig build-exe`), both already adapters in
`incremental.py`.

### 6.4 The cold gate (≥ 3× Go under all three ch06 variants)

| Variant (ch06 §Definitions) | Fors | Go | Expectation |
|---|---|---|---|
| (a) everything-from-source | std + project from source, empty cache | `go build -a` with an empty `GOCACHE` (std rebuilt) | Fors should win large: Fors std is 2,311 lines today, while `go build -a` recompiles every std package the program imports (unmeasured here — M2-1(a) records it) |
| (b) stdlib-prebuilt-project-cold | **identical to (a)** — std is always in the build, there is no prebuilt std; stated in the results file | warm std cache, empty project cache | **the at-risk row**: Fors today is ~0.3 s for check alone at 105k lines, single-threaded; lowering + codegen + link add an estimated 0.1–0.2 s. If Go's (b) at the same shape is under ~1.5 s, 3× needs the parallel frontend `compiler-architecture.md` §2 promises |
| (c) warm-incremental | the daemon row of §6.2 | Go's incremental rebuild of the same edit | Fors wins large if §6.2 holds |

The measurement that settles (b) costs nothing to build: run `incremental.py`'s existing Go and Zig
adapters at the §6.1 shape and record their cold numbers (M2-1). If Go (b) < 1.5 s, M2-8 must
include parallel `check_body` (type-checker §13 already describes it as "a flag flip plus a
deterministic diagnostic merge").

---

## 7. The matmul checkpoint (PLAN round 9)

**What must exist for it to compile and run:** f64 arithmetic (M2-6); heap allocation through the
explicit root allocator and `Vec[f64]`/`Slice[f64]` with `at`/`at_mut` places (M2-4); counted loops,
`if`, calls (M2-2); integer print of the sum and trace (std `io`, M2-5); **reading `N` and the thread
count from the command line** — `env.Args` is a stub today, so M2-5 adds the intrinsic rows `args_len`
and `args_at` to the closed table in **both** engines; and a decimal parser in Fors (std or the kernel).
The kernel is **single-threaded** (no runtime parallelism before M3/M6): it reads and ignores the
thread argument and is compared only at `threads = 1`.

**SIMD: none in M2.** `vector[T, N]` is out of the FMIR surface until M3/M7 and `fors-asm` has no
Advanced-SIMD encodings. clang `-O1` does not vectorise either, so the comparison is scalar against
scalar.

**The bar.** New rows `bench/langs/c-O0.toml` and `c-O1.toml` (naive `matmul/c/main.c`, strict FP,
the rule-6 flags copied verbatim), a `fors` column for `matmul-blocked` (hand-scheduled: BLOCK = 64
tiles, i-k-j inside, row slices hoisted by the programmer so the inner loop indexes one slice by `j`),
N = 1800, threads = 1, harness `check` passes the checksum, `bench` gives median of ≥ 10 runs.

**Honest forecast.** The naive i-k-j loop at `-O0` is instruction-bound, not memory-bound (≈ 20
instructions and a store-to-load chain per element: ~7 cycles × 5.8·10⁹ iterations ≈ 13 s, while
streaming B needs only ~47 GB ≈ 1 s), so tiling buys the dev tier little; the instruction count per
element decides. Stage-A stack-slot code with two bounds checks per element is *more* instructions
than clang `-O0` and will **lose** to it by an estimated 1.2–1.5×. Stage B (block-local value cache,
§2.1) removes most slot traffic in the one-block inner loop: estimate 12–15 instructions, ~3–4
cycles per element — **beats `-O0` by ~2×, loses to `-O1` (~1.5–2 cycles) by ~2×**, and no dev-tier
pass may delete a bounds check (ch02 R11 makes the OIR range pass the only authority). Beating `-O1`
would need an unchecked index (none exists in the spec) or check elimination (M5). **The measurement
that settles it before any of M2-4…M2-6 is built:** M2-1(b) hand-assembles the predicted inner loop
in its stage-A and stage-B forms with `fors-asm`, links it with M2-0's writer, and times it against
`c-O0`/`c-O1` at N = 1800. Owner Q2 asks which bar is the gate.

---

## 8. `secret` and `ct_region` in the dev tier (PLAN R10, ch05 R6–R8, R15)

| Level | Carrier | Rule |
|---|---|---|
| FMIR | `ValRow.flags.SECRET`, `ValRow.ct` (exist) | R6, R6a, R6b (FMIR verifier, exists) |
| OIR | `secret: bool`, `ct: u16` columns on every value row, **copied, never recomputed**; non-optional (fixed-width columns) | R6; `oir_verify_requires_secret_and_ct` |
| LIR-dev | per stencil instance: `secret_mask: u8` (which operands / result are secret), `ct: u16` | R6 at LIR; `lir_verify_requires_secret_and_ct` |
| Frame | **two slot classes**: `Plain` and `Secret`. Secret slots form one contiguous region, are never shared or reused, are written through even by the stage-B cache (exempt from any store elision), and are **zeroised in the epilogue** (`stp xzr, xzr` over the region) | R7 (dedicated spill class), R8 (no DSE / store-forwarding, zeroised before epilogue) |
| Registers | a function that touches any secret value zeroises `x10..x15`, `d16..d31` and the secret-carrying argument registers before `ret` | R8 in spirit; R20a(b) for asm blocks |
| Stencils | each stencil carries `ct_safe: bool`; the dev-tier CT check rejects (compile error naming the site, never a miscompile) a secret operand reaching a stencil that branches on it, forms an address from it, or is on the denylist (`sdiv`/`udiv`, any trapping stencil) | the dev-tier half of R15; FMIR R6b already rejects the source-level forms, this is the backstop after selection |
| Timing mode | **[rec]** emit `msr DIT, #1` at the first instruction of a `ct_region` and restore the caller's DIT at its exit (FEAT_DIT, present on Apple M1) | engineering call E9; needs `MSR (immediate)` in `fors-asm` |

M2-0 refuses any secret-flagged value (`Refusal::Secret`) rather than emit code without the spill
class; the classes and the dev-tier CT check land in M2-10. The release tier's post-regalloc CT
verifier is M5, the dudect-style timing tests M12 (PLAN §5).

---

## 9. Rule-to-code table

| Rule | Mechanism | Crate / file | Gate test |
|---|---|---|---|
| ch02 R4 failure ABI | classifier `failure_class(payload_size)`; `x0..x2` / `x8` sret; tag `x9`, 0 = ok | `fors-abi/src/failure.rs` | `failure_class_table_0_to_64`, `raises_roundtrip_every_payload_size_native` (M2-5) |
| ch02 R6 trap = one `brk` + side table | per-site `brk #(0x4600+kind)` in the cold tail; per-atom trap table | `fors-codegen-dev/src/trap.rs`, `fors-link/src/tables.rs` | `trap_sites_have_one_brk_each` (M2-0), `trap_table_covers_every_site` (M2-3) |
| ch02 R7, R14 no unwinder | no unwind sections emitted; image scan | `fors-obj` | `image_has_no_unwind_sections` (M2-0) |
| ch02 R15 eight kinds | `kind` = `TrapKind` discriminant, 0..7 asserted | `fors-abi` | `brk_imm_kinds_are_exactly_eight` (M2-0) |
| ch02 R17 error out of `main` | shim: flush (ignore failure), synthesized `render` line, status 1 | `fors-codegen-dev/src/rt/entry.rs`, `fors-lower` | the five `main-raises-*` run-error tests native (M2-5) |
| ch03 R2/R4 integer semantics | stencils per (op, mode, width), mirroring `fors-interp/src/arith.rs` | `fors-codegen-dev/src/stencil/int.rs` | `edge_table_matches_arith_rs` (M2-0) |
| ch03 R7 strict IEEE, no FMA; Q2 canonical NaN | no fused stencil; `FPCR.DN = 1` in the shim; `frem` is a Fors routine mirroring `arith::frem_*` | `stencil/float.rs`, `rt/entry.rs`, `std` | `float_edge_table_matches_arith_rs`, `nan_bits_are_canonical_native` (M2-6) |
| ch04 R7 shim is not Fors source | runtime atoms in Rust via `fors-asm` | `fors-codegen-dev/src/rt/` | `root_capabilities_built_only_by_shim` (M2-5) |
| PLAN R9 syscall scan | no `svc` in any emitted atom | `fors-link` | `image_contains_no_svc` (M2-3) |
| ch05 R1 level order | FMIR → OIR → LIR-dev → atoms, no shortcut | crate deps | `codegen_dev_consumes_only_oir` (CI grep, M2-0) |
| ch05 R4/R5 alias classes | class from `AliasSeed` on every slot/memory row; verifier | `fors-oir/src/alias.rs`, `verify.rs` | `oir_verify_requires_alias_class` (M2-0), `ir_verify_alias_missing_rejected`, `ir_verify_alias_source_five_only` (M2-4) |
| ch05 R6 secret + ct on every value | non-optional columns at OIR and LIR | `fors-oir`, `fors-codegen-dev/src/lir.rs` | `oir_verify_requires_secret_and_ct` (M2-0), `ir_verify_secret_fields` at LIR (M2-10) |
| ch05 R7/R8 secret spill class, zeroise | `SlotClass::Secret`, epilogue zeroise | `fors-codegen-dev/src/frame.rs` | `secret_slots_zeroised_in_epilogue` (M2-10) |
| ch05 R12 `tile.*` FMIR-only | OIR verifier rejects | `fors-oir/src/verify.rs` | `oir_rejects_tile_op` (M2-0) |
| ch05 R15 CT verifier (dev half) | stencil `ct_safe` + post-selection check | `fors-codegen-dev/src/ct.rs` | `ct_denylist_rejected` (M2-10) |
| ch05 R17 bit-for-bit agreement | native differential | `fors-oracle/src/native.rs` | `backend_bitforbit_agreement` = the generator/conformance runs (M2-0 → M2-6) |
| ch05 R18 / PLAN R13 DWARF unsigned | dSYM sidecar | `fors-dwarf`, `fors-link` | `debug_info_only_edit_keeps_cd_hash` (M2-9) |
| ch06 R10–R14 compile-speed reporting | `incremental.py` Fors adapter | `bench/compile-speed/incremental.py` | the M2-12 results JSON |
| ch10 R40 buffering, exit table, SIGPIPE | shim + std Fors code compiled natively | `rt/entry.rs`, `std/io.fors` | `sigpipe-ignored-write-latches` (status 2) and every `run-*` test native (M2-5) |

---

## 10. Increments M2-0 … M2-12

Model tier per Marc's rules: **opus** for correctness-critical codegen semantics, the linker/signing
path and anything security-shaped; **sonnet** where a deterministic oracle (the interpreter, the
kernel's signature check, the assembler, lldb) judges the work completely; **haiku** for mechanical
runs. Every increment gets an independent verifier (Fable when quota allows, else opus) that attacks
the gate's *vacuity* (does the native runner really execute native code; do mutations get caught)
rather than re-deriving the code. "Parallel with" means the two share no files.

### M2-0 — the straight-line native slice (opus; ~3.5k lines incl. tests) — HAND THIS OVER TONIGHT

**Goal.** One FMIR function → OIR → LIR-dev → atom → signed `MH_EXECUTE` → **runs** on this machine →
its stdout and exit equal the interpreter's, over a generated corpus, deterministically. The smallest
slice that exercises emit, link, sign, run and differential together.

**FMIR surface covered** (everything else is refused, §"Refusals"):

- Types: `i8 i16 i32 i64 u8 u16 u32 u64`, `bool`, `()`. (Not `usize`/`isize`, not floats.)
- Constants: `ConstInt`, `ConstBool`, `ConstUnit`; `ConstStr` **only** as the argument of
  `stdout_write_line` (bytes go to the atom's literal pool).
- Arithmetic: `Add Sub Mul Div Rem Shl Shr` in modes `Trap`, `Wrap`, `Sat`; `Neg` in `Wrap` on
  every type, in `Trap` and `Sat` on **signed** types only (owner Q6; `Profile::STRAIGHT_LINE.ops`
  excludes unsigned `Sat` `Neg` until Q6 is answered); `And Or Xor Not`.
- `Icmp` (all six predicates; result `bool` as 0/1).
- Conversions: `ConvChecked`, `ConvWrap`, `ConvSat` between integer types.
- Places: `CopyFrom` and `Init` on a **scalar root place with an empty projection** (locals and
  parameters' places) — each root is one frame slot.
- `Intrinsic` with callee `stdout_write_uint` or `stdout_write_line` only.
- Terminators: `Ret` (unit), `Trap` (explicit).
- Exactly **one function, `main`, with one basic block** and no parameters.

**Semantics are `fors-interp/src/arith.rs`**, not this document: every stencil mirrors the
corresponding `trap_*`/`wrap_*`/`sat_*`/`conv_*` function, including which conditions trap and with
which kind (Q4: `MIN / -1` and `MIN % -1` trap `overflow` in `Trap` mode; the shift trap condition is
exactly `count >= width`). The producer reads `arith.rs` first and writes the edge-table test before
any stencil.

**Pieces.**

1. `crates/fors-abi/` — `lib.rs`, `regs.rs` (scratch `x10..x15`, `TRAP_BRK_BASE = 0x4600`, the
   reserved list), `failure.rs` (constants only in M2-0: `FAILURE_INLINE_MAX = 24`,
   `FAILURE_TAG_REG = 9`).
2. `crates/fors-oir/` — `lib.rs`, `ir.rs` (SoA: values with `ty, secret, ct`; rows with `op, a, b,
   ty, mode, alias, site`), `from_fmir.rs` (the subset above; every other op returns
   `Refusal { decl, inst, op, reason }`), `alias.rs` (a local/param root's class is
   `AliasClass::Root{root, source: Convention | Affine}` from the FMIR `AliasSeed`), `verify.rs`
   (secret+ct present on every value; alias class present and traceable on every slot row; `tile.*`
   absent), `dump.rs`.
3. `crates/fors-codegen-dev/` — `lib.rs`, `stencil.rs` (the hole model and the static table),
   `stencil/int.rs` (per op × mode × width class: 32-bit-and-narrower vs 64-bit), `select.rs`,
   `frame.rs` (one 8-byte slot per OIR value and per place root, sp-relative, frame ≤ 32 KiB else
   refuse), `trap.rs` (cold tail, one `brk` per site, per-atom trap rows), `emit.rs`, `rt/mod.rs`,
   `rt/write.rs` (`_fors_rt_write(fd, ptr, len)` looping on short writes via `svc #0x80` /
   `SYS_write = 4` — temporary, see below; `_fors_rt_write_uint(u64)` decimal into a 24-byte stack
   buffer; `_fors_rt_write_line(ptr, len)` bytes then `\n`), `rt/entry.rs` (`_main`: frame, `bl` Fors
   main, `mov w0, #0`, return to dyld — `LC_MAIN` turns the return value into `exit`). The intrinsic
   semantics must equal the interpreter's rows of the same names byte for byte.
4. `crates/fors-obj/` — port `spikes/aarch64-macho/src/exec.rs` + `sha256.rs` into a tested crate:
   `macho.rs` (header, segments, load commands of §4.1 minus `__DATA*`), `fixups.rs` (empty chained
   fixups, as the spike), `trie.rs`, `sign.rs` (§4.2), `uuid.rs` (§4.2's page-hash construction),
   `sha256.rs`, `write.rs` (temp file in the target directory, `0o755`, `rename`). Keep the spike's
   two recorded pitfalls as named tests.
5. `crates/fors-link/` — M2-0 needs only `link_once(atoms, runtime) -> Image`: place runtime atoms
   then `main`'s atom, resolve the `bl`s to runtime routines (direct, no stub table yet), build the
   image directory. No incremental path yet.
6. `crates/fors-oracle/` — `generate.rs`: add `Profile` and `generate_with(seed, &Profile)` with
   `Profile::STRAIGHT_LINE` (no `if`, no loops, no helpers; everything else as today);
   `generate(seed)` must be **unchanged**. `native.rs`: compile → link → write to a scratch dir →
   spawn (empty env, stdin null, 10 s timeout) → `NativeRecord`; `native_diff.rs`: `run_seeds(range,
   &Profile) -> Tally` with classes `ok / mismatch / refused / compile-panic / spawn-fail / signal /
   timeout`, every class counted, none dropped.

**Refusals (precise, never a miscompile).** `from_fmir` and `select` return
`Refusal { decl, inst, op, reason }` for: any op not listed; `Unchecked` mode; `Neg` in `Trap` or `Sat` mode
on an unsigned type (owner Q6); any type not listed; any secret-flagged value (`reason: "secret values
need the spill class (M2-10)"`); a place with a projection; more than one block; any parameter; a
frame over 32 KiB; an intrinsic other than the two. The CLI is not touched in M2-0.

**Why `svc` is acceptable for one increment.** It is what the spike proved works and it avoids
chained-fixup binds in the first slice. It is confined to `rt/write.rs`, listed in a
`RUNTIME_SYSCALL_ATOMS` allowlist, and M2-3 deletes it and turns `image_contains_no_svc` strict.

**Gates (all must pass; native ones on macOS/aarch64).**

| Test | Crate | Asserts |
|---|---|---|
| `generate_default_profile_is_unchanged` + every existing `fors-oracle` test | oracle | `generate(seed)` bytes identical for seeds 0..1000 to the pre-change commit (fingerprints checked in) |
| `oir_from_fmir_subset_counts` | oir | one OIR row per FMIR row for the subset; refusals name the op |
| `oir_verify_requires_secret_and_ct`, `oir_verify_requires_alias_class`, `oir_rejects_tile_op` | oir | each mutation is rejected by name |
| `stencils_match_fors_asm` | codegen-dev | every stencil, 1,000 random hole fillings each, equals `fors_asm::encode` of the same sequence |
| `refuses_out_of_subset_by_name` | codegen-dev | one case per refusal row above |
| `trap_sites_have_one_brk_each`, `brk_imm_kinds_are_exactly_eight` | codegen-dev | R6, R15 |
| `codegen_is_deterministic` | codegen-dev | two compiles → identical atom bytes; a CI grep for hash containers in backend `src/` |
| `macho_minimal_image_golden` | obj | byte-golden of a fixed two-instruction program (runs on Linux) |
| `section64_has_three_reserved_fields`, `page0_fields_final_before_hashing` | obj | the spike's two pitfalls |
| `uuid_is_content_derived` | obj | identical inputs → identical UUID; one code byte changed → different UUID |
| `image_has_no_unwind_sections`, `image_has_no_host_paths_or_times` | obj | scan of the image |
| `codesign_verify_accepts_image` | obj (macOS) | `codesign --verify` exit 0 (test-time tool only; the compiler never calls it) and the negative control: one patched byte → rejected |
| `native_empty_main_exits_zero` | oracle (macOS) | status 0, empty stdout |
| `native_write_uint_edges` | oracle (macOS) | `0 1 9 10 99 100 2^32 u64::MAX` printed byte-identical to the interpreter |
| `edge_table_matches_arith_rs` | oracle (macOS) | for each (type, op, mode) one generated straight-line program over all pairs of the generator's `interesting()` values whose `arith.rs` result is not a trap; stdout equals both `arith.rs` and the interpreter |
| `native_trap_exits_by_sigtrap_per_kind` | oracle (macOS) | hand-written `.fmir` fixtures tripping `overflow`, `div-zero`, `shift`, `checked-conversion`: native status is signal `SIGTRAP`, interpreter record is `Trap{kind}` (the stderr line arrives in M2-3) |
| `straight_line_native_diff_200` | oracle (macOS) | seeds 0..200 of `Profile::STRAIGHT_LINE`: all `ok`, zero in every other class |
| `straight_line_native_diff_10k` (`#[ignore]`, run and reported) | oracle (macOS) | seeds 0..10⁴: zero mismatches, refusals, panics; wall time recorded |
| `native_build_and_run_twice_identical` | oracle (macOS) | image SHA-256 and record identical across two builds and two runs |

**Report (not gated):** per-phase microseconds for the largest seed (`oir`, `select`, `emit`,
`link`, `sign`, `write`), image size, and native-vs-interpreter wall time for 10⁴ programs.

**Escape hatch if over budget:** the producer may refuse `Sat` and `Div`/`Rem` by name and exclude
them through `Profile::STRAIGHT_LINE.ops`; they then move to M2-2. Nothing else may be cut.

**Parallel with:** nothing (it creates the crates). Files: the new crates above, `fors-oracle/src/
{generate,native,native_diff}.rs`, `fors-oracle/Cargo.toml`, `fors-oracle/tests/native*.rs`,
workspace nothing (members are `crates/*`).

### M2-1 — risk probes (haiku for (a); sonnet for (b); ~300 lines + two results files)

(a) Run `incremental.py`'s Go and Zig adapters at the §6.1 shape (`M = 200`, `F` to be fixed so a
Fors rendering would be ≥ 100k lines; use `F = 100` for now): cold (all three variants), no-op, and
20 reps of E1–E5; commit the results JSON. (b) `crates/fors-codegen-dev/examples/matmul_probe.rs`:
the predicted inner loop of the tiled kernel in stage-A form and stage-B form, built with `fors-asm`,
linked by M2-0's `fors-obj` writer with a scalar driver, timed at N = 1800 against new rows
`bench/langs/c-O0.toml`, `c-O1.toml` (naive `matmul/c`). **Gate:** both results files committed with
the numbers that answer owner Q2 and risk R1. **Parallel with:** M2-2, M2-3 (files disjoint).

### M2-2 — control flow, calls, the full generator (opus; ~2k lines)

Scope: multiple blocks, `Br`, `CondBr` (`cbnz` on the bool slot), loops (back edges), `CallDirect`
with parameters and scalar returns per §3, the stub table (`fors-link`), the native reducer predicate.
Crates/files: `fors-oir/src/{from_fmir,ir}.rs`, `fors-codegen-dev/src/{select,frame,emit}.rs`,
`stencil/ctrl.rs`, `fors-link/src/{place,stubs}.rs`, `fors-oracle/src/{native_diff,reduce}.rs`.
**Gates:** `generator_native_diff_100k` (`generate(seed)`, seeds 0..10⁵, zero mismatches/refusals/
panics — with unsigned `Sat` `Neg` either resolved by Q6 or excluded through a `Profile` that is
`generate`'s profile minus that one form, the excluded count reported); `reducer_shrinks_injected_native_miscompile` (≥ 5 seeded stencil bugs via
`inject-miscompile`, each to < 30 FMIR instructions); `call_args_8_plus_stack`;
`narrow_args_are_canonical_at_call` (a callee observing the full 64-bit register through a
`ConvWrap` identity). **Parallel with:** M2-1, M2-3 (if M2-3 keeps to its files).

### M2-3 — runtime, imports, the trap handler (opus; ~1.5k lines)

Scope: chained-fixup **binds** to libSystem (`write`, `sigaction`, `sigemptyset` or the struct by
hand, `isatty`, `malloc`/`free` for M2-4, `clock_gettime_nsec_np`, `getentropy`), `__DATA_CONST,__got`;
`svc` deleted; `MRS`/`MSR` added to `fors-asm` (with oracle cases) and `FPCR` set in the shim;
`SIGPIPE → SIG_IGN`; the `SIGTRAP` handler of §3; `__fors_dir`, `__fors_lines` and per-atom trap
tables; `FORS_BACKTRACE=1`. Files: `fors-obj/src/fixups.rs`, `fors-codegen-dev/src/rt/*`,
`fors-link/src/tables.rs`, `fors-asm/src/{inst,encode}.rs` + golden. **Gates:**
`image_contains_no_svc` (strict); `trap_line_bytes_match_interp` for the four arithmetic kinds on
`.fmir` fixtures (stderr last line byte-equal, status `SIGTRAP`); `stdout_lost_on_trap_like_interp`;
`fpcr_dn_set_at_entry`; `codesign_verify_accepts_image_with_imports`. **Parallel with:** M2-1, M2-2.

### M2-4 — memory, aggregates, alias classes (opus; ~2.5k lines)

Scope: places with projections (`Field`, `Index` with `bounds` trap, `Deref`), `Borrow*` as slot
addresses, `AggNew/Field/VariantNew/Discr/Payload/TupleNew/SwitchDiscr` over `fors-layout`,
`SliceRange`, `Alloc/Free/@memcpy/@memset` through libSystem, `ArenaAlloc/ArenaDeref/ArenaReset` with
the generation trap, `ConstStr` in literal pools, `usize`/`isize`; **`at_mut` inlined as a place
computation in `fors-lower`** (owner decision); OIR alias classes from all five `AliasSeed` sources
with the verifier. Generator: `Profile::aggregates`. **Gates:** `generator_aggregates_native_diff_100k`;
`ir_verify_alias_missing_rejected`, `ir_verify_alias_source_five_only` (05-ir, now live at OIR);
`at_mut_lowers_to_place_no_call` (FMIR of `a[i] = x` has no `call_*`); `bounds_and_arena_trap_lines_match`.
**Parallel with:** M2-6, M2-7.

### M2-5 — failure ABI, contracts, `reduce`, std natively, the conformance runner (opus; ~2k lines)

Scope: `fors-abi::failure_class` (owner Q7 contribution point), `raise`/`try_br` with `x9`, `sret`,
the `main` error exit (ch02 R17: flush ignoring failure, one synthesized `render` line, status 1),
`CheckPre/Post/Inv` → `contract` trap, `ReduceTree` (the normative expansion of fmir-interpreter
§3.9 as emitted code), entry-shim root capabilities, `args_len`/`args_at` intrinsic rows in both
engines, `fors build` producing the native executable. **Gates:** `conformance_runtime_native` — all
64 runtime tests through `fors build` + run, record-equal to the interpreter (the 5 pinned keep their
exact assertion); `failure_class_table_0_to_64`; `raises_roundtrip_every_payload_size_native`
(payload 0..40 bytes); `empty_reduce_and_contract_trap_lines_match`. **Parallel with:** M2-7.

### M2-6 — floats (sonnet producer, oracle-judged; ~1.2k lines)

Scope: `Fadd…Fneg`, `Fcmp`, float↔int and float↔float conversions bit-exact with `arith.rs`, `frem`
as a std Fors routine porting `arith::frem_*`'s algorithm (so it is compiled code, not a libm call),
`@fastmath` ignored (strict always). Generator: `Profile::floats`. **Gates:**
`float_edge_table_matches_arith_rs` (±0, subnormals, ±inf, NaN, MIN/MAX, every conversion boundary);
`nan_bits_are_canonical_native`; `float_default_no_fma_run_ok` native; `generator_floats_native_diff_100k`.
**Parallel with:** M2-4, M2-7.

### M2-7 — incremental link and re-sign (opus; ~1.2k lines)

Scope: atom slots with slack, the full stub table, `relink` per §4.3, clonefile fallback reporting,
inode assertion, non-ad-hoc refusal, UUID recomputation. Files: `fors-link/src/{relink,clone,plan}.rs`,
`fors-obj/src/sign.rs` (incremental slot rewrite). **Gates:** `incremental_edit_script_200` — 200
random body edits over generated programs, after each: native record = interpreter record = cold
image record, `codesign --verify` accepts, inode changed; `body_edit_dirties_at_most_4_pages`
(+ page 0); `never_patches_in_place` (a test hook that forces rename failure must surface as an
error); `relink_p95_under_5ms_10mb` (pinned box, recorded). **Parallel with:** M2-4, M2-5, M2-6.

### M2-8 — query integration, per-module frontend, the daemon (opus; ~2.5k lines)

Scope: query kinds 24–30 (§2.3); resolve and the signature phase per module (the I9 promise);
the driver loop `demand → executed_of_kind → relink → sidecar`; `fors-driver` daemon over a unix
socket with `--no-daemon`; `--timings=json` phases of §6.2; parallel `check_body` behind a flag if
M2-1(a) says so. **Gates:** set-equality per edit class (§2.3's bullets) at 30/60/120 declarations;
`comment_edit_executes_no_atom_code`; `incremental_build_equals_cold_semantically` over an 8-edit
script incl. a breaking edit and its revert; determinism under file/declaration permutation;
`e5_check_body_count_at_100k` (counter, recorded before any timing). **Parallel with:** M2-9.

### M2-9 — DWARF sidecar (sonnet producer, lldb-judged; ~1.2k lines)

Scope: §4.4. **Gates:** `dwarf_companion_unsigned` / `debug_info_only_edit_keeps_cd_hash` (05-ir
R18: rename a local, CD hashes unchanged, sidecar changed); `lldb_breakpoint_bt_locals` (`lldb
--batch`: breakpoint by `file:line`, `bt` shows Fors frames via the x29 chain, `frame variable`
prints scalar locals); `llvm-dwarfdump --verify` clean if present on the box (test-time only);
`sidecar_is_reproducible`. **Parallel with:** M2-8.

### M2-10 — `secret` / `ct_region` in the dev tier (opus; ~800 lines)

Scope: §8 — secret slot class, epilogue zeroisation, register zeroisation, stencil `ct_safe`, the
dev-tier CT check, DIT at `ct_region` boundaries (`MSR (immediate)` in `fors-asm`). **Gates:**
`ir_verify_secret_fields` at LIR; `ct_denylist_rejected`; `secret_slots_zeroised_in_epilogue`
(a static check of every emitted epilogue, plus a native test whose image links a test-only runtime
atom `_fors_test_peek_dead_frame` that reads the just-returned callee's secret region and prints it:
all zero); `secret_never_shares_a_slot`. **Parallel with:**
M2-8, M2-9.

### M2-11 — the matmul checkpoint (opus for the value cache; sonnet for kernel and bench rows; ~1k lines)

Scope: stage-B block-local value cache (`fors-codegen-dev/src/cache.rs`, scratch set from `regs.rs`);
`bench/kernels/matmul-blocked/fors/main.fors`; `bench/langs/fors.toml`, `c-O0.toml`, `c-O1.toml`.
**Gates:** every differential corpus still clean with the cache on (`generator_*_native_diff_100k`
re-run); harness `run.py check` passes for `fors` on `matmul-blocked`; `run.py bench` at N = 1800,
threads = 1, results JSON committed, `fors` < `c-O0` (and `c-O1` reported — or gated, per owner Q2).

### M2-12 — exit measurement (sonnet for adapters; Fable/opus for the final judgement; ~500 lines)

Scope: the `fors` adapters in `incremental.py` and `compile_speed.py`; the §6.3 protocol on the pinned
box; results JSON for cold (a)/(b)/(c), incremental p50/p95 per class and pooled (daemon and
`--no-daemon`), edit-to-test-result, the matmul row. **Gate:** PLAN §5's M2 row, each number traced to
a committed results file; a miss is reported as a miss with its phase breakdown, never re-scoped
silently.

**Order and parallelism.** M2-0 → {M2-1 ∥ M2-2 ∥ M2-3} → {M2-4 ∥ M2-6 ∥ M2-7} → M2-5 → {M2-8 ∥ M2-9 ∥
M2-10} → M2-11 → M2-12. M2-11's stage-B cache can start after M2-4 + M2-6 if M2-1(b) shows it is
needed (it will).

---

## 11. Risks, ranked, each with the measurement that retires it

| # | Risk | Retiring measurement | When |
|---|---|---|---|
| R1 | **Cold (b) ≥ 3× Go is unattainable single-threaded**: check alone is ~0.3 s at 105k lines | Go/Zig cold numbers at the §6.1 shape (M2-1(a)); Fors cold per phase from M2-8's `--timings` | M2-1, M2-8 |
| R2 | **Matmul vs `-O1` is unattainable in a dev tier that may not delete checks**; even `-O0` needs the stage-B cache | M2-1(b)'s hand-assembled inner loop timed against `c-O0`/`c-O1` | M2-1 |
| R3 | **E5 (core public signature) fan-out blows the p95** once whole-build resolve is gone | `e5_check_body_count_at_100k` counter, then the E5 timing row | M2-8 |
| R4 | dyld / code-signature format change in a macOS point release kills every image | `codesign_verify_accepts_image*` + one native run on every macOS update; a macOS CI job (Q3) | continuous |
| R5 | Interpreter and backend disagree where the spec is silent (unsigned `neg`, stack exhaustion, NaN through `fneg`) and the differential "fixes" the backend to a wrong oracle | every mismatch is triaged against the spec chapter before either engine changes; owner Q5/Q6 | M2-0 → M2-6 |
| R6 | Incremental image diverges from cold in a way only some edit sequences expose | `incremental_edit_script_200` and the M2-8 8-edit script, records compared to cold each step | M2-7, M2-8 |
| R7 | Native differential is not a merge gate (Linux CI cannot run it) and rots | macOS runner (Q3); until then a nightly run on the pinned box with the tally committed | M2-0 |
| R8 | Image hashing/signing scales with image size on cold builds (software SHA-256) | M2-0's per-phase report at the largest seed, then M2-12's cold row; ARMv8 SHA instructions via `std::arch` | M2-0, M2-12 |
| R9 | Trap-table churn on comment edits dirties many signed pages | `comment_edit_executes_no_atom_code` + a dirty-page count for E1 | M2-8 |
| R10 | The stencil fast path drifts from `fors-asm` | `stencils_match_fors_asm` on every stencil, every run | M2-0 on |

---

## 12. Open owner questions (only those that need Marc)

**Q1. Which row does the 50 ms p95 gate bind — daemon or `--no-daemon`?** *Recommendation:* the
daemon row, with `--no-daemon` published beside it as ch06 R13 requires. *Consequence:* M2-8 must
ship `fors-driver`. Binding `--no-daemon` instead requires an mmap-loaded on-disk query cache in M2
(another ~6 weeks) and is unlikely to reach 50 ms at 100k lines anyway (§6.2(a)).

**Q2. What is the matmul bar — beat `-O0`, or beat both `-O0` and `-O1`, and at which thread
count?** *Recommendation:* gate on beating `c-O0` at N = 1800, threads = 1; report `c-O1` beside it
as a recorded finding. This matches round 9's own wording ("the bar is low on purpose … the gate
tests that the pipeline produces a running, measurable program, not that it produces fast code"). *Consequence:* with the recommendation, M2-11 needs only the block-local value
cache. Requiring `-O1` needs either an unchecked index in the language (a spec change) or check
elimination in the dev tier (contradicts ch02 R11 — only the OIR range pass may delete a check), so
it effectively moves the checkpoint to M5. M2-1(b) will put numbers on this before anything depends
on it.

**Q3. Add a GitHub `macos-14` (Apple-silicon) CI job running the native differential as a required
check?** *Recommendation:* yes (the repository is public, so hosted minutes are free).
*Consequence otherwise:* every native gate runs only on the pinned box, the differential is a nightly
report rather than a merge gate, and R7 stays open.

**Q4. Must an incrementally relinked dev image be byte-identical to a cold build?**
*Recommendation:* no — bit-identity is a property of cold and release builds (`--check-repro`);
incremental images are deterministic in (previous image, edit) and differential-equal to cold.
*Consequence of "yes":* atoms must be laid out canonically after every size-changing edit, which
shifts every later atom and rehashes their pages — incompatible with the 50 ms budget on a large
image.

**Q5. Stack exhaustion semantics (spec silent).** *Recommendation:* a stack overflow is a
whole-process abort with one fixed stderr line (`stack overflow`), **not** a trap kind (ch02 R15's
list stays closed), excluded from the differential corpus; the dev tier emits a stack probe for
frames larger than one guard page; the interpreter's 1024-frame refusal stays a refusal.
*Consequence otherwise:* native programs die by `SIGSEGV`/`SIGBUS` with no message, and the behaviour
is undefined text in a language that promises zero UB.

**Q6. Unsigned `neg`.** The interpreter wraps unsigned `neg` in `Trap` mode and `sat_neg` delegates
to wrap (F10 flagged it). *Recommendation:* the FMIR verifier rejects `Neg` on an unsigned type in
`Trap` and `Sat` modes (the surface cannot write it), `wrap_neg` stays two's complement, and the
generator stops emitting the rejected forms. *Consequence otherwise:* the backend must copy a
behaviour the spec does not state, and any later spec text breaks recorded oracle outputs.

**Q7. PLAN §5's learning-mode lines in M2 — `fors-abi::failure_class()`, `classify_aggregate()`,
`fors-link::rehash_dirty_pages()`, and `compiler-architecture.md`'s `fors-codegen-dev/src/regs.rs`
scratch set.** *Recommendation:* producers write the gate tables and a marked implementation
(`// CONTRIBUTION POINT (PLAN §5)`), and Marc rewrites any of them before the increment merges if he
wants to. *Consequence otherwise:* M2-0 (regs), M2-5 (failure_class) and M2-7 (rehash) block on
Marc.

---

## 13. Engineering calls made here (no owner input needed)

- **E1** OIR is built in M2 (ch05 R1), thin and linear; no optimisation pass runs in the dev tier.
- **E2** "Copy-and-patch" = pre-encoded `fors-asm` stencils with holes, no build-time compiler.
- **E3** LIR-dev is a module of `fors-codegen-dev`; `fors-lir` waits for M5's vreg LIR.
- **E4** Calls go through a stub table so atom code is independent of callee placement.
- **E5** Narrow integers are canonical 64-bit sign/zero-extended everywhere.
- **E6** No red zone; `x18` never touched; `x9` not a scratch register.
- **E7** Content UUID from page hashes (O(pages)), version nibble 8.
- **E8** Trap tables split: per-atom site rows with declaration-relative lines + a per-file
  declaration-line table, so comment edits dirty one or two signed pages.
- **E9** `PSTATE.DIT` set at `ct_region` entry (recommendation; enforcement lands with M2-10).
- **E10** M2-0 uses raw `svc` for `write` for one increment, allowlisted and removed in M2-3.
- **E11** `MACOS_MIN = 14.0` in `LC_BUILD_VERSION` (chained fixups need ≥ 12; the box runs 26).
- **E12** PLAN "round 10" (no LLVM in the dev tier; Cranelift as the M5a fallback) is relayed by the
  orchestrator but absent from `docs/PLAN.md` at 1d858b8; this design obeys it, and the round should
  be written into §4.3 by whoever records owner rounds.
