# 02. Failure: errors, traps, contracts and check removal

## Status

Draft, M0.5, 2026-09-19. Implements PLAN.md R4 (failure ABI, traps,
backtraces) and R7 (check-elimination authority, contract removal). Where
this chapter conflicts with `docs/design/*.md`, this chapter wins (§4.2).

## Scope

Owns exclusively: the error-as-value model (`raises`, postfix `?`,
`else |e| { }`, `ErrorFrom`); the failure ABI classifier (register/tag/sret);
trap semantics and the whole-process-abort mechanism (including that a trap
runs no deferred body); which exits of a block are ERROR exits, the
definition `errdefer` keys on (Rule 16); what the runtime does with an error
that leaves `main` (Rule 17); cross-fiber backtrace
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
- **Error exit**: a way of leaving a block that carries an error out of it
  (Rule 16). Every other way of leaving a block is a **normal exit**.
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
   a value of the call's success type. Inside a `defer`/`errdefer` body a
   handler is the only way to call a `raises` function, and there it MUST
   NOT `raise` or `return` (ch01 Rule 23c): it yields the success value or
   traps.
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
   condition, and therefore ends the process. **A trap runs NO deferred
   body.** Every `defer` and `errdefer` body pending at the trap site (ch01
   Rules 23-23f) is skipped, because a trap is one breakpoint-class
   instruction that MUST NOT call or allocate (Rule 6) and the process ends
   there. A trap is therefore not an exit of any block and is neither a
   normal nor an error exit (Rule 16). Consequently no invariant of std or
   of a program MAY depend on cleanup happening on the abnormal path: after
   a trap an open file, socket, listener or child process is abandoned to
   the operating system, no `close`/`shutdown`/`wait`/`free` runs, and
   buffered bytes MAY be lost (ch10 Rule 40(b)). There is no
   flush-on-abort, no temporary-file removal and no lock-file release, and
   none will be added; a program that needs durability across a risky step
   writes and flushes before it.
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
16. **Error exit** (the definition `errdefer` keys on; ch01 Rules 23-23f
    are its only consumer in v0.1). An exit of a block `B` is an *error
    exit* iff control leaves `B` because a `raise` statement, or a `?`
    whose call failed, written in `B` or in a block nested in `B`,
    propagates the error out of the enclosing function (Rules 1-3). The
    error passes through every block between the raise site and the
    function body, and every one of those blocks is left by an error exit.
    Every other way of leaving a block is a *normal exit*: reaching its
    `}`, a tail value, `return`, `break`, `continue`. An `else |e| { }`
    handler (Rule 5) decides for the blocks it leaves by what it does — a
    handler that `raise`s makes an error exit, one that `return`s or yields
    a value makes a normal exit — so a `?` that a handler intercepts is not
    an error exit of anything. A trap is neither (Rule 7). The property is
    syntactic and per exit point: the set of error exits of a block is
    read off its statements, with no dataflow analysis, which is why ch01
    Rule 23b can apply `errdefer` bodies in one forward pass.
17. **An error raised out of `main`.** If `main` is declared `raises E`
    (ch04 Rule 8) and an error `e: E` propagates out of it, then, after
    `main`'s own `defer` and `errdefer` bodies have run (ch01 Rule 23e):
    (a) the runtime flushes `Stdout` exactly as on a normal return (ch10
    Rule 40(a)), ignoring any failure of that flush; (b) it writes exactly
    ONE line to the standard error file descriptor, unbuffered: the bytes
    `error: `, then `render(e)`, then `\n`; (c) the process exits with
    status 1, whether or not (a) or (b) succeeded, and this rule writes
    nothing to `Stdout`. `render` is defined on the STATIC type `E`,
    recursively, and is the whole of v0.1's error reporting: an enum value
    renders as its type's fully-qualified path (module path and item name,
    `std.net.Error`, `app.Error`), `.`, the variant name, and, for a
    variant with a payload, `(` the rendered components separated by `, `
    `)`, or `{ ` `name: ` rendered `, ` ... ` }` for a struct-form variant;
    a struct value as its path followed by `{ name: rendered, ... }` over
    its fields in declaration order; a tuple as `(` components `)`; an
    integer in base 10 with a leading `-` if negative, no grouping and no
    padding; `bool` as `true`/`false`; `()` as `()`; a `Str` as its text
    between double quotes with `\`, `"`, newline, carriage return and tab
    escaped as `\\`, `\"`, `\n`, `\r`, `\t`, so that the line stays ONE
    line; every other type — `Own`, `Slice`, a `fn` type, a `dyn` type, a
    root-capability or allocator type, a rigid type parameter — as `..`.
    No locale, no width, no colour, no backtrace. Examples of the whole
    line: `error: std.io.Error.closed`, `error: app.Error.timeout(3,
    "host")`.
    **If the write in (b) fails** — an error return, a short write, a
    closed descriptor — the runtime MUST NOT retry, MUST NOT write the line
    anywhere else, MUST NOT trap, and MUST still exit with status 1. The
    runtime entry shim installs `SIG_IGN` for `SIGPIPE` before `main` runs,
    so a write to a closed pipe fails as an ordinary `io.Error.closed`
    inside `main` (ch10 Rule 39's latching then works as described) and
    cannot end the process by a signal here. The exit-status table — 0, 1
    and 2 — is ch10 Rule 40(d), which cites this rule for status 1.

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

```fors
module app.main;
needs { io.stdout };
use std.io;

enum Error { boom, code(i32, Str) }

fn step(let n: i32) raises Error {
    if n == 0 { raise Error.boom; }
}

// An error out of `main`: the deferred line first (ch01 Rule 23e), then
// the runtime's one line `error: app.main.Error.boom` on stderr and
// status 1 (Rule 17). `errdefer` would run here and not on a normal exit.
fn main(inout out: io.Stdout) raises Error {
    defer out.write_line("done");
    step(0)?;
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
- **Rendering `main`'s error through a `Writer` trait the error type must
  implement** (Rule 17): a trait obligation on every error type, for a line
  that is almost always an enum name. Rejected.
- **Printing nothing but the exit status**: throws away the only diagnostic
  a script gets from a failing program.
- **Deriving the exit status from the variant's ordinal**: unstable across
  a variant addition (ch09 Rule 6), so a script would break on a
  source-compatible std change.
- **Running deferred bodies on a trap** (a "cleanup handler"): needs a call
  on the trap path, which Rule 6 forbids; the honest answer is Rule 7's.

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
- Round 6 (2026-09-20): the error-exit definition is this chapter's (Rule
  16) and not ch01's, because it is a property of `raise`/`?`, which this
  chapter owns; ch01 Rules 23-23f cite it. `render` (Rule 17) is defined
  structurally on the static type rather than by a trait, so no error type
  carries an obligation and no allocation happens on the failure path.
  Status 2 is reserved by ch10 Rule 40(d) for a failed final `Stdout`
  flush, kept distinct from 1 so a script can tell "the program failed"
  from "the output did not arrive".
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

## Closed by owner decision 2026-09-20, round 6

- **O4 — an error raised out of `main`.** Rule 17: one line on stderr,
  `error: ` + `render(e)`, exit status 1, a failed stderr write ignored,
  `SIGPIPE` ignored by the entry shim. This closes ch10 Open question 5
  ("`main`'s result and `raises`", which said the answer "is currently
  nowhere"). ch04 Rule 8 gains one sentence pointing here; ch10 Rule 40(d)
  carries the exit-status table.
- **O2 — traps run no deferred body.** Rule 7 states it and states the
  consequence the owner asked for: no std invariant and no program
  invariant may depend on cleanup on the abnormal path. Rule 16 gives
  `errdefer` the error-exit definition it keys on; the semantics of both
  words are ch01 Rules 23-23f.

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

Round 6 (Rules 16-17), all in `tests/conformance/02-failure/`. The harness
gains ONE expectation kind, `run-error`: the program is built and run, it
MUST exit with status 1, and its standard error MUST equal the directive's
`detail` followed by a newline (the directive carries the line without the
trailing newline). `run-ok` keeps its meaning (status 0, stdout compared);
a program that exits 2 is expected with `run-error` plus an explicit
`status: 2` field, which `tests/conformance/README.md` documents.

- `main-raises-unit-variant-run-error` (R17) — stderr is exactly
  `error: main.Error.boom`.
- `main-raises-payload-run-error` (R17) — `error: main.Error.code(7, "x\n")`,
  the newline in the payload escaped so the output is one line.
- `main-raises-std-error-run-error` (R17) — an `AllocError` out of `main`
  through `mem.Counting`: `error: std.mem.alloc.AllocError.out_of_memory`.
- `main-raises-nested-payload-run-error` (R17) — a payload component of a
  type with no rendering renders as `..`.
- `main-raises-flushes-stdout-run-error` (R17(a)) — buffered `Stdout`
  content still arrives, and the status is 1.
- `main-raises-after-defer-run-error` (R17, ch01 R23e) — the deferred
  line, written to `Stderr`, precedes the runtime's `error: ` line.
- `main-returns-latched-stdout-exit-2` (ch10 R40(d)) — a latched `Stdout`
  error on a normal return exits 2, not 1.
- `main-raises-not-declared-rejected` (R1) — a `?` in a `main` with no
  `raises` is a `check-error`, unchanged.
- `error-exit-through-nested-blocks` (R16) — a `?` inside a `for` inside a
  `with` leaves three blocks by error exits, each running its `errdefer`
  bodies (ch01 R23b).
- `handler-makes-normal-exit` (R16, R5) — a `?` intercepted by an
  `else |e|` that yields a value is NOT an error exit: the enclosing
  `errdefer` does not run (`run-ok`).
- `trap-runs-no-defer` (R7) — a `defer` that writes to `Stderr` before a
  trapping index: the marker MUST NOT appear (`trap` kind).
