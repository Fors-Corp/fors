# aarch64 Mach-O backend feasibility spike — report

**Highest rung reached: RUNG 3 (own encoder, own MH_OBJECT writer, own
signed MH_EXECUTE writer — no LLVM, no `as`, no `ld`, no `codesign`).**
All four programs (hello, fib, collatz, loops) PASS on all three rungs.

Architecture: rung 1's codegen now emits a small in-memory instruction
IR (`ir::Inst`, ~20 variants) instead of assembly text, consumed by two
back ends: a printer (rung 1) and an encoder (`encode.rs`, rungs 2/3).
No second code generator was written.

## Evidence

| program | rung1 | rung2 | rung3 | codesign --verify |
|---|---|---|---|---|
| hello | PASS | PASS | PASS | accepted (all 3) |
| fib | PASS | PASS | PASS | accepted |
| collatz | PASS | PASS | PASS | accepted |
| loops | PASS | PASS | PASS | accepted |

`./run_tests.sh` reproduces this (12/12 PASS). The encoder was verified
byte-for-byte against the system assembler first: `spike difftest
programs/*.fors` assembles the same IR-derived text with `cc -c` and
diffs `otool`'s __text dump against our own encoding — all four match
exactly, instruction for instruction.

## Timing (median of 20, `spike measure`)

| program | rung1 total | rung2 total | rung3 total | rung1 size | rung3 size |
|---|---|---|---|---|---|
| hello | 62.9ms | 45.4ms | **0.43ms** | 16944B | 16831B |
| fib | 63.4ms | 46.5ms | **0.46ms** | 16960B | 16863B |
| collatz | 64.6ms | 46.2ms | **0.41ms** | 16976B | 16863B |
| loops | 62.1ms | 45.7ms | **0.33ms** | 16944B | 16831B |

Rung 1/2 cost is almost entirely `cc`/`as`/`ld` spawn + toolchain
startup (parse/codegen/encode are all under 0.05ms). Rung 3 replaces
that with ~0.3-0.5ms of in-process work: **~150x faster** — the payoff
of owning the path.

## macOS requirements discovered the hard way

- **`section_64` has THREE reserved fields, not two.** Missing
  `reserved3` shifted every later load command by 4 bytes; `ld` reported
  a garbled cmdsize on the *next* command, not a section error —
  misleading. Found by diffing against a `cc -c` reference object.
- **ADRP/ADD page refs can't be resolved from file offsets alone** the
  way branches can: `b`/`bl`/`b.cond` share a section with their
  target, so byte-offset arithmetic is placement-independent, but
  `adrp`+`add`/PAGEOFF12 cross into `__const`. Rung 2 emits real
  `ARM64_RELOC_PAGE21`/`PAGEOFF12` entries, exactly as `as` does, rather
  than trust an assumption about `ld`'s layout. Rung 3 has no linker,
  so it computes the true page delta itself once addresses are fixed.
- **The CodeDirectory must hash the *final* patched bytes.** Page-0
  fields (LC_CODE_SIGNATURE's datasize, `__LINKEDIT`'s vmsize/filesize)
  must be set *before* hashing, or the signature is self-invalidating —
  `codesign --verify` just says "invalid signature", no detail. All
  three are derivable analytically (identifier length + page count)
  without hashing first, breaking the apparent circularity.
- Chained fixups/exports trie are structurally fixed for this
  no-imports, two-export shape (`__mh_execute_header`, `_main`): an
  empty-fixups, minimal-trie image needs no address-dependent bytes in
  the fixups blob, only in the trie.
- The two runtime routines were frozen as pre-assembled bytes, not
  re-implemented in the encoder — they never depend on the source
  program, a deliberate scope cut.

## What the real backend must do differently

A real AST/lowering pass, not inline CST matching; the full
register/immediate ranges (this IR covers only what four programs
exercise); real exports/fixups for programs with actual imports; and
the differential-test harness kept as a permanent regression gate.

## Verdict: **GO**

Owning the whole path is not just feasible but ~150x faster than
shelling out, with every macOS hazard documented and passing a
kernel-enforced acceptance test (`codesign --verify` + actual execution).

## Orchestrator verification addendum (2026-09-19)

Re-run independently of the implementing agent:

- `./run_tests.sh`: 12/12 PASS (4 programs x 3 rungs).
- Rung 3 with `env -i PATH=/nonexistent`: all four programs build and run, so
  no assembler, linker or `codesign` is reachable, let alone used.
- 40 consecutive rebuild-then-run cycles over the same output path: 40/40
  correct (the writer renames a fresh inode into place; compare
  `../macho-resign/REPORT.md`, where in-place patching was killed ~60%).
- `codesign --verify`: valid; `flags=0x20002(adhoc,linker-signed)`,
  CodeDirectory v20400, the same flags the system linker sets.
- **Timing, read carefully.** The ~150x above is IN-PROCESS time (0.43 ms vs
  ~63 ms). Measured from outside, including spawning the compiler process,
  collatz is 93.2 ms (rung 1) vs 7.5 ms (rung 3), median of 20: ~12x. The
  in-process figure is the relevant one for the resident `fors-driver` daemon,
  which never pays process start; the external figure is what a cold
  `fors build` would see. Quote whichever matches the claim being made.
- Scope cuts to remember: the two runtime routines are pre-assembled bytes (the
  encoder covers only compiler-emitted instructions); no imports, so chained
  fixups and the exports trie are minimal; wrapping arithmetic, not trap-on-overflow.
