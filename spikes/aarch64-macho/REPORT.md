# aarch64 Mach-O backend feasibility spike — report

**Highest rung reached: RUNG 1 (own codegen -> arm64 assembly text -> `cc`/`as`/`ld`).**
Rungs 2 (own encoder + relocatable-object writer) and 3 (own signed executable
writer) were not attempted: implementing rung 1's codegen against the real
`fors-syntax` CST (a flat, struct-of-arrays token tree, not a conventional
AST -- operators are raw tokens between flat n-ary operand lists, dotted
names collapse into single `NameExpr` leaves, parameter names are bare
tokens not wrapped in their own node) consumed the exploration and
debug-loop budget for this run. The evidence below is honest about that
gap; the closing sections give concrete next steps for rungs 2/3.

## Evidence: PASS/FAIL table (rung 1)

| program  | rung | exit | output matches | codesign --verify |
|----------|------|------|-----------------|--------------------|
| hello    | 1    | 0    | PASS            | accepted |
| fib      | 1    | 0    | PASS            | accepted |
| collatz  | 1    | 0    | PASS            | accepted |
| loops    | 1    | 0    | PASS            | accepted |
| all four | 2/3  | -    | not implemented | -- |

`run_tests.sh` reproduces this table. `codesign --verify` passes because
`cc`/`ld` apply the standard ad-hoc, linker-signed signature -- rung 1
never touches signing itself; that is exactly the piece rung 3 would have
to reimplement.

Note on `collatz`: an independent Python re-implementation of the exact
subset semantics gives **350** steps for the longest chain below 100000
(start 77031), not 351. The compiled binary agrees with the Python
oracle (350); I trust the two independent implementations over the task
prompt's figure and documented the discrepancy rather than silently
"fixing" the output to match an unverified expectation.

## Timing (rung 1 only -- no rung 2/3 to compare against)

Median of 20 runs, the compiler binary invoked directly (no cargo
overhead in the loop), `cc -arch arm64` doing assemble+link:

| program  | parse   | codegen | assemble+link (cc/as/ld) | total  | binary size |
|----------|---------|---------|---------------------------|--------|-------------|
| hello    | 0.016ms | 0.012ms | 59.8ms                    | 59.8ms | 16944 B |
| fib      | 0.019ms | 0.025ms | 60.7ms                    | 60.8ms | 16976 B |
| collatz  | 0.026ms | 0.039ms | 61.5ms                    | 61.5ms | 16992 B |
| loops    | 0.019ms | 0.022ms | 59.7ms                    | 59.7ms | 16944 B |

Parsing and codegen are noise (tens of microseconds -- `fors-syntax`'s
allocation-free CST is fast, and the flat statement/expression walk over
these tiny programs is trivial). The entire budget is `cc` invoking the
system `as` and `ld`: process-spawn overhead plus toolchain startup, not
our own logic. This is rung 1's own argument for rung 2/3: an own
encoder+writer replaces roughly 60ms of external-process overhead with
microseconds of in-process byte emission -- the actual payoff of owning
the whole path, which rung 1 alone does not show because it still shells
out to `as`/`ld`.

## macOS/arm64 requirements discovered (would matter most at rung 3)

- Every code section must be under an explicit `.text` directive; a
  literal data section (`__TEXT,__const`) placed inline without
  switching back to `.text` afterward silently continues in the data
  section for whatever assembly follows -- the linker does not error, but
  the resulting bytes land in a non-executable-looking region and a
  `bl` into it faults with EXC_BAD_INSTRUCTION. Caught by disassembling
  under `lldb` after a mysterious SIGILL, not by any tool warning.
- `__TEXT,__cstring,cstring_literals` is not a generic byte-blob
  section: the linker string-pools it as null-terminated C strings.
  Un-terminated raw bytes (as in a length-prefixed, non-null-terminated
  runtime string) get silently coalesced with whatever symbol follows,
  with only a linker warning, not an error (`ld: warning: c-string
  symbol '...' is located within another string, the entire string '...'
  will be used instead`) -- the resulting binary still links and runs,
  just wrong. `__TEXT,__const` is the section to use for arbitrary
  literal data instead.
- `mov xN, #imm` as an assembler pseudo-op refuses immediates that are
  neither a 16-bit-shifted value nor a bitmask-immediate pattern (e.g.
  `#100000` errors with "expected compatible register or logical
  immediate"); a real backend must decompose every 64-bit immediate into
  explicit `movz`/`movk` chunks itself rather than trust the assembler to
  synthesize it -- the assembler's `mov` alias is narrower than it looks.
- The ad-hoc, linker-signed signature `cc`/`ld` attaches by default is
  sufficient for `codesign --verify` and for the kernel to run the binary
  on Apple Silicon with no explicit `codesign` step -- confirming that
  reaching rung 3 (hand-built LC_CODE_SIGNATURE/CodeDirectory) is about
  reproducing that exact layout, not inventing a new one; `macho-resign`'s
  existing parser (`spikes/macho-resign/resign.py`) is the right reference
  for that layout and was not needed for rung 1.
- AAPCS64 frame discipline (paired `stp x29,x30,[sp,#-16]!` /
  `ldp x29,x30,[sp],#16`, 16-byte-aligned `sub sp,sp,#N` for locals,
  16-byte-aligned push/pop for spill/argument staging around every `bl`)
  was sufficient with no other surprises -- recursion (fib) and
  cross-function calls worked on the first correctly-aligned attempt.

## What a real (non-spike) backend must do differently

- Build a real AST/IR pass over `fors-syntax::Tree` once, instead of
  pattern-matching `NodeKind` inline in codegen as this spike does -- the
  flat CST (operators as raw tokens, dotted paths as single leaves) is
  the right lossless representation for tooling but the wrong shape to
  codegen from directly at any real scale; a lowering pass that resolves
  names, types and operators into a small typed IR should sit between
  them.
- Immediate synthesis, register allocation (this spike statically assigns
  one stack slot per local/param and never uses more than a two-register
  ALU discipline -- fine for a subset, not for a real backend), and
  calling-convention argument marshalling (only handled up to 8 i64
  args here, no stack-passed arguments, no non-integer types) all need
  real implementations.
- Rung 2's own instruction encoder is mechanical (this spike's assembly
  mnemonics are almost the full instruction set needed -- mov/movz/movk,
  add/sub/mul/sdiv/msub, cmp, cset, b/b.cond/bl/ret, ldr/str/strb,
  adrp/add -- the work is bit-packing each into its 32-bit encoding and
  emitting LC_SEGMENT_64/relocations instead of text) but was not
  attempted here for lack of remaining budget.
- Rung 3's signature work is copy-the-layout, not invent-a-layout: dump a
  rung-1 binary's load commands (`otool -l`) and CodeDirectory
  (`codesign -dvvv`, `resign.py`), and reproduce them exactly (page-aligned
  __PAGEZERO/__TEXT/__LINKEDIT, LC_LOAD_DYLINKER, LC_LOAD_DYLIB for
  libSystem, LC_MAIN, SHA-256 page hashes) -- genuinely mechanical but
  each of the "usual causes" the task lists (page alignment, codeLimit,
  partial-page hash, vmsize/filesize mismatch) will each cost a debug
  cycle against a real kernel, not against a spec.

## Verdict: GO-WITH-CAVEATS

Rung 1 proves the parsing-to-codegen path against the real frontend crates
end to end, with recursion, control flow, arithmetic, and hand-emitted
syscall-based I/O all working with zero LLVM and zero fors-authored
library code beneath the two I/O primitives. That derisks the
front half of "own the whole path." It does not derisk the back half
(rung 2 encoder/object-writer, rung 3 signed-executable writer) -- those
are mechanical but unverified here, and the task's own framing ("nobody
has proved... rung 3 answers this") is still open. Caveat: budget a
dedicated follow-up spike for rungs 2-3 specifically, seeded with this
report's macOS-requirements list and macho-resign's CodeDirectory
knowledge, before committing the real backend to the no-ld/no-codesign
path.

## Wrapping semantics

`+ - * / %` on i64 use plain AArch64 add/sub/mul/sdiv/msub -- natural
two's-complement wrapping, no overflow traps. Trap-on-overflow is out of
scope for this spike, as instructed.
