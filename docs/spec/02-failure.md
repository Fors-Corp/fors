# 02. Failure: errors, traps, contracts and check removal

## Status

Draft, M0.5, 2026-09-19. Implements PLAN.md R4 (failure ABI, traps,
backtraces) and R7 (check-elimination authority, contract removal). Where
this chapter conflicts with `docs/design/*.md`, this chapter wins (§4.2).

## Scope

Owns exclusively: the error-as-value model (`raises`, postfix `?`,
`else |e| { }`, `ErrorFrom`); the failure ABI classifier (register/tag/sret);
trap semantics and the whole-process-abort mechanism; cross-fiber backtrace
continuity; contract syntax (`pre`/`post`/`invariant`) as declarations and
when a check may be removed; sole authority for removing bounds/overflow
checks; checks-off build status; the C/C++ raise/unwind boundary.

Not owned: qualifiers/arenas (ch01), which conditions trap for numerics
(ch03), `needs` syntax (ch04), IR levels and the OIR pass's placement
(ch05), proof-engine internals and the C error-mapping table (future
chapters).

## Definitions

- **Trap**: unrecoverable, non-catchable termination from a contract,
  bounds, overflow, div-zero, shift, checked-conversion (ch03), arena-
  generation (ch01), or empty-reduce (ch03) violation (Rule 15's closed
  list). Other chapters name trap *conditions*; only this chapter defines
  what a trap *does* and the closed set of trap-kind identifiers.
- **Raise**: returning an error from a function declared `raises E`.
- **Classifier**: the pure `(payload_size) -> ClassResult` function both
  backends and the interpreter must compute identically, where
  `payload_size = max(size_of(T), size_of(E))` for `-> T raises E`.
- **`FAILURE_TAG_REG`**: register carrying the success/failure tag, fixed
  outside the target C ABI's return-value register set.
- **`FAILURE_INLINE_MAX`**: byte threshold; payloads at or under it are
  register-passed, above it use `sret`.
- **Contract policy**: per-module setting, one of `.runtime`/`.proved`/
  `.off`, identical in dev and release. Under `.proved` a contract the
  proof engine cannot discharge MUST be a compile error (no silent runtime
  fallback).

## Rules

1. A function that may fail MUST declare `raises E`; `E` MUST NOT be
   inferred from the body. An error originates only from the statement
   `raise expr;` (`expr: E`), legal only in a `raises E` function; `return`
   always returns the success value. A call to a `raises` function MUST be
   immediately followed by `?` or `else |e| { }`; anything else MUST be
   rejected.
2. Postfix `?` MUST propagate an error unmodified when the enclosing
   function's declared error type equals the callee's, else via Rule 3; `?`
   MUST NOT be legal on a non-`raises` expression.
3. Where caller raises `F` and callee raises `E != F`, `?` MUST perform
   exactly one `ErrorFrom[E, F]` lookup and apply it, MUST NOT chain a
   second conversion, and MUST be a compile error if none exists.
4. The failure ABI classifier has two outcomes by payload size only: (a)
   `<= FAILURE_INLINE_MAX`: payload in result general-purpose registers
   (aarch64: x0..x2), tag in `FAILURE_TAG_REG` (aarch64: `x9`), a register
   the target C ABI never uses for a return value; (b) `>
   FAILURE_INLINE_MAX`: payload via `sret` pointer in `x8`, tag still in
   `FAILURE_TAG_REG`. Tag `0` MUST mean success in both cases.
   `FAILURE_INLINE_MAX`/`FAILURE_TAG_REG` are named constants fixed by
   measurement on aarch64 first (initial default: 24 bytes, `x9`).
5. `else |e| { }` MUST bind `e: E` only directly after a call expression of
   static type `raises E`; it MUST NOT apply to a multi-statement block.
   The `else` block MUST either diverge (`return`, `raise`, trap) or yield
   a value of the call's success type.
6. A trap MUST lower to one breakpoint-class instruction (aarch64: `brk
   #imm`) plus a static read-only pc-to-info side-table entry (site id,
   kind, span); it MUST NOT allocate or call.
7. A trap is a WHOLE-PROCESS ABORT. It MUST terminate the whole process;
   no trap MUST be catchable, by any syntax, in any mode; the compiler
   MUST NOT emit an unwinder, personality routine, or landing pad for any
   trap or raise. "Domain abort" MUST NOT be implemented or exposed, and
   NO boundary is reserved for a future domain-recovery mechanism (owner
   decision 2026-09-19, round 5, D4: the plain confirmation, with no
   hedge). **Expected errors are not traps**: an error a caller is meant
   to handle travels as a VALUE, through `raises E`, `?` and `else |e|`
   (Rules 1-5). A trap is for a violated invariant — a contract, an index,
   an overflow (Rule 15's closed kind list) — which is a bug, not a
   condition, and therefore ends the process.
8. A backtrace crossing a fiber boundary MUST recognize the fiber-switch
   sentinel frame (parent fiber id, parent frame pointer, spawn-site pc) and
   continue through it, else report a truncated trace rather than reading
   unrelated memory.
9. `pre`/`post`/`invariant` MUST be part of the declaration they annotate
   and MUST be runtime-checked whenever the module's policy is `.runtime`
   (default). A contract expression MUST be pure and MUST NOT contain a
   `secret`-typed subexpression (a runtime check is a branch; ch05).
10. A contract check MUST be removable only by (a) a proof-engine discharge
    (future verification chapter) or (b) the module's explicit `.off` policy; MUST NOT
    be removed by `-O` level; a module's policy MUST behave identically in
    dev and release.
11. The OIR range-and-dominance pass MUST be the only pass permitted to
    delete a bounds or overflow check; no other stage or tier MUST delete
    one, even if it can locally prove safety.
12. Any module or build with `.off` policy or a checks-disabling flag MUST
    be tagged internal/instrumentation and MUST be rejected by `fors build
    --release` and by the registry's publish check.
13. An `extern "c"` function MUST NOT declare `raises`; a Fors error MUST
    NOT cross that boundary un-mapped (mapping table: future C-interop chapter).
14. A C++ exception crossing an `extern "cxx"` boundary MUST be stopped
    there; catching it, if enabled, MUST happen only inside a separately
    prebuilt `@catches_cxx` C++ object file — the Fors compiler itself MUST
    NOT emit a personality routine, landing pad, or unwind table, ever.
15. The trap-kind identifier set is exactly: `contract`, `bounds`,
    `overflow`, `div-zero`, `shift`, `checked-conversion`,
    `arena-generation`, `empty-reduce`. Every Rule 6 side-table entry MUST
    record one of these eight strings as its kind; no other identifier MUST
    appear there. `nesting-limit` (any recursion- or nesting-depth guard)
    is NOT a trap kind: a nesting-limit violation MUST NOT lower via Rule 6
    or carry a trap-kind identifier.

## Examples

```fors
module app.io;
needs { fs.read };
use std.fs;

fn read_config(let d: fs.Dir, let name: Str, inout buf: Slice[u8])
    -> usize raises fs.Error
{
    return d.read_into(name, &buf)?;
}
```

```fors
module app.net;
needs { net };
use std.net;

impl ErrorFrom[net.TimeoutError] for app.Error {
    fn from(let e: net.TimeoutError) -> app.Error { return app.Error.timeout(e); }
}

fn fetch(let c: net.Client, let url: Str, inout buf: Slice[u8])
    -> usize raises app.Error
{
    return c.get_into(url, &buf)?; // single ErrorFrom hop, Rule 3
}
```

```fors
module app.buf;
contracts: .proved;
needs { };

fn write_at[T](inout self: Buffer[T], let i: usize, let v: T)
    pre i < self.len
{
    self.data[i] = v;
}
```

```fors
module app.parse;
needs { };

fn take(let s: Str, let n: usize) -> Str raises app.Error {
    if n == 0 { raise app.Error.empty; }
    return s.slice(0, n) else |e| { raise app.Error.wrap(e); };
}
```

## Rejected alternatives

- Tag in `x1`/`x8`+flag (surface draft): collides with 16-byte aggregate
  return and the sret pointer register (reviews.md #3, #20).
- Two check-elimination engines (OIR + stage-1 both deleting bounds
  checks): ambiguous soundness owner; OIR now sole authority.
- Dropping contracts at `--release`: reintroduces the dev/release
  divergence PLAN forbids elsewhere.
- Domain abort at `spawn`: no mechanism without an unwinder and per-scope
  arena teardown (reviews.md #10); deleted.
- Compiler-generated `@catches_cxx`: needs a landing pad the compiler must
  never emit; moved to a prebuilt external object.

## Decisions made while drafting

- `FAILURE_TAG_REG = x9`, `FAILURE_INLINE_MAX = 24` bytes as aarch64
  defaults, pending `abi-fuzz` measurement.
- `ErrorFrom` is exactly one lookup, never chained — locally decidable.
- `else |e|` only follows a single call, not a block — no flow analysis.
- `contracts: .runtime|.proved|.off;` sits on the module-header line, after
  `module` and before `needs` (header precedes all declarations).
- `raise expr;` is the sole error-origination statement (verifier
  addition: drafts used `return Err`, `raises X;` and a bare trailing
  expression interchangeably; PLAN fixes only `raises` and `?`).
  Accepted by the owner 2026-09-19 (D4).
- `ErrorFrom[E]` is a trait implemented on the target type `F` (`impl
  ErrorFrom[E] for F`), since the language has no overloading.
- Examples return into caller buffers; `Own[T, A]`-returning signatures
  are now expressible with a brand parameter (ch01 Rules 15d, 18).
- Trap side-table entries are static/read-only; no allocation on the trap
  path.
- Sentinel frame fields fixed to (parent fiber id, parent fp, spawn-site
  pc) per reviews.md's proposed fix; no design doc specified fields.
- Owner decision 2026-09-19, round 2: the corpus audit found trap-kind
  identifiers scattered across chapters with no closed list; Rule 15 names
  the eight canonical strings verbatim and states that a nesting-limit
  violation is a distinct, non-trap failure mode.

## Closed by owner decision 2026-09-19, round 5

- **D4 — trap is a whole-process abort, confirmed plainly.** Open question
  1 is closed as drafted: no unwinder, nothing catchable, no reserved
  domain-recovery boundary, and no hedging language anywhere in this
  chapter. Rule 7 now states it prominently, together with the
  consequence the owner asked to be stated: expected errors travel as
  values via `raises`/`?`/`else`, so "no recovery" costs a server author
  nothing they were meant to have — it removes only recovery from bugs.

## Open questions for the owner

1. ~~§4.3(4): whole-process abort may disqualify some server users —
   confirm before it is load-bearing in the ABI and stdlib.~~ Closed by
   owner decision 2026-09-19, round 5 (D4): confirmed, plainly; see
   Rule 7 and the closed-decision section above.
2. Confirm `FAILURE_TAG_REG`/`FAILURE_INLINE_MAX` defaults, or block
   finalization on the aarch64 `abi-fuzz` measurement.
3. Confirm module-header placement for `contracts: ...;` (undecided in any
   design doc).
4. The classifier is size-only: a lone `f64` success value travels in a
   GPR, not `v0`. Accept, or add a float class before `fors-abi` freezes?

## Conformance tests

- `raises-no-infer`: raising call without `?`/`else` in a non-`raises`
  function is rejected.
- `raise-only-in-raises-fn`: `raise e;` in a non-`raises` function, or
  with `e` not of type `E`, is rejected.
- `contract-secret-rejected`: a `pre`/`post` mentioning a `secret` value
  is rejected.
- `contract-proved-undischarged-rejected`: under `.proved`, an
  undischarged contract is a compile error.
- `postfix-try-propagate`: matching-type `?` lowers to one cold branch, no
  `ErrorFrom` call.
- `error-from-single-hop`: two required conversions rejected; one accepted.
- `else-binds-call-only`: `else |e|` on a multi-statement block rejected;
  on one call accepted.
- `abi-classify-inline`: payload at threshold uses GPRs+tag; one byte over
  uses `sret`.
- `abi-tag-register-disjoint`: tag register never observed as a return
  value by a plain `extern "c"` caller.
- `trap-single-instruction`: each trap kind lowers to one `brk`-class
  instruction plus a side-table entry, no call.
- `trap-uncatchable`: any try/else wrapping a trapping expression is
  rejected — traps have no catch syntax.
- `no-domain-abort-surface`: no keyword/attribute/stdlib symbol for
  partial-process recovery at `spawn` exists.
- `fiber-backtrace-sentinel`: a trap in a stolen continuation prints a
  backtrace through its spawn ancestor.
- `contract-runtime-default`: no `contracts:` line checks `pre`/`post` at
  runtime in both dev and release.
- `contract-off-uniform`: `.off` disables identically in dev/release; `-O`
  alone has no effect.
- `oir-sole-check-deleter`: no stage but the OIR range pass removes a
  bounds/overflow check.
- `checks-off-unshippable`: `--release` and publish both reject `.off` or a
  checks-disabling flag.
- `extern-c-no-raises`: `extern "c"` with `raises` is rejected.
- `cxx-shim-external-only`: no compiler-emitted object has an unwind table;
  a linked `@catches_cxx` object may.
- `trap-kind-identifiers-closed`: every trap site's side-table kind is one
  of the eight Rule 15 strings; any other string is a spec violation.
- `nesting-limit-not-a-trap`: a nesting/recursion-limit violation does not
  lower via Rule 6 and carries no trap-kind identifier.
