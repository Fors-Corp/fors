# Chapter 4: Authority — capabilities, comptime and the build

## Status

Draft, M0.5, 2026-09-19. Implements PLAN.md R8 (comptime: one engine) and R9
(capability declaration has two sites: manifest = policy, `needs` =
requirement). Normative per §4.2: conflicts with `docs/design/*.md` resolve
in this chapter's favor.

## Scope

Owns: the capability name set; the closed set of root-capability types and
how `main`'s parameters grant root authority (Rule 21; there is no `World`
value); `needs { ... }` as requirement; the manifest's
per-target/per-dependency field as policy (an upper bound); the
requirement-⊆-policy check and when it runs; sealed capabilities
(`syscall`, `asm`, `ffi`) and which packages may hold them;
`asm`/`syscall` as capabilities
distinct from `@unsafe`; scanning emitted code for syscall-class instructions;
inline assembly's authority preconditions (architecture, register and
secret-input rules; ch05 owns the IR side); where capability values appear
and how `main` gets root authority; the `ffi`
taint rule; `@unsafe(invariant: "...")`'s grammatical form (not its runtime
semantics — ch01); the comptime engine's identity,
purity and budgets; the module-header `inputs { ... };` clause that declares
comptime file reads (ch07 owns its grammar); the build graph's
no-executable-steps rule; lockfile
capability pinning, `fors grant`, and the security-release channel; dynamic
module capability signing. `iso`/`imm`/`secret`, conventions, and the failure
ABI belong to other chapters and are only referenced here.

## Definitions

- **Capability**: `fs.read, fs.write, net, exec, ffi, clock, rng, env,
  io.stdout, io.stderr, io.stdin, gpu, asm, syscall`.
- **Sealed capability**: `syscall`, `asm`, `ffi`. Every other capability
  is **exported**.
- **Sealed operation**: inline assembly (`asm`); a syscall-class
  instruction or syscall intrinsic (`syscall`); a call to, or taking the
  address of, an `extern` function (`ffi`).
- **Holder**: a module whose own `needs` names a sealed capability.
- **Requirement**: the set named in a module's `needs { ... }`.
- **Exported requirement**: a module's checked requirement (Rule 2) minus
  the sealed capabilities.
- **Policy**: the manifest's per-target, per-dependency capability bound.
- **Root capability**: a value of one of the eleven fixed types in Rule 21.
  There is no `World` value; a root capability is obtainable only as a
  parameter of `main`, directly or by narrowing (Rule 7).
- **Taint**: a ledger-recorded fact (metadata), not a runtime check.

## Rules

1. A module MUST declare every capability it uses, or constructs a
   capability value from, in `needs { ... };` in its header (after
   `module` and any `contracts:` line, before `use`); an undeclared use
   MUST be a module-graph compile error. An absent `needs` clause MUST
   mean `needs { };` (zero authority).
2. Checked requirement of a module = its own `needs` ∪ the *exported*
   requirements of its imports, over the acyclic module graph (a cyclic
   graph MUST be rejected before this check runs). Sealed capabilities
   MUST NOT propagate to importers, by `use`, re-export, or any other
   edge; an importer of `std.fs` (which holds `syscall`) requires
   `fs.read`, not `syscall`.
2a. A sealed operation is a use of its sealed capability by the module in
   whose source text it appears (Rule 1). In particular calling a
   re-exported or `pub` `extern` function from another module is a use
   of `ffi` by the *calling* module. A sealed operation MUST NOT appear
   in a generic function, in a function the compiler may inline or
   instantiate into another module's code, or in a closure passed out of
   the holder; so every sealed operation's bytes are emitted in the
   holder's own object and Rule 4's per-module scan stays exact. A
   callback or generic argument supplied by an importer runs as the
   importer's code and gains nothing from being called inside a holder.
   Comptime evaluation reaching a sealed operation MUST be a build error
   (Rule 12); sealing never exempts it.
2b. The manifest policy MUST name, per sealed capability, each PACKAGE
   permitted to hold it (`std` is permitted by default; no wildcard). A
   holder in any other package MUST be a build error naming the package,
   module and capability. The exported capabilities of every module are
   still bounded by Rule 3.
3. The build MUST fail unless checked requirement ⊆ policy for every
   module and target (sealed capabilities checked per Rule 2b); this MUST
   be checked once at build time over the full graph and again at link
   time against signed BMIs, which record own `needs`, exported
   requirement and sealed holdings separately.
4. A module whose own `needs` lacks `syscall` MUST have
   every byte the compiler emits for it into an executable section —
   including inline-assembly bytes and constants placed in text — scanned
   for syscall-class instruction encodings at every offset that is a
   valid instruction start on the target (aarch64: every 4-byte-aligned
   word; x86-64: every byte offset); any found MUST be a build error
   naming the module and site. Holding `asm` MUST NOT exempt a module
   from this scan.
4a. The scan cannot see foreign objects. `ffi` therefore MUST be treated
   as the top capability: a policy entry granting `ffi` MUST be reported
   by `fors audit` and the lockfile as granting every capability
   (including `syscall` and `asm`), and no other capability implies
   `ffi`. Mapping memory executable or writing to text at run time is
   reachable only through `syscall` or `ffi`, so Rules 1-3 cover it.
5. A module lacking `asm` MUST NOT contain inline assembly; this MUST be
   rejected before codegen.
6. `asm` and `syscall` are declared under Rule 1 and sealed under Rules
   2-2b; they MUST NOT be implied by, or imply, `@unsafe`.
7. Every root-capability type (Rule 21) MUST have no constructor: it is
   opaque (no struct literal, no field access, not `Copyable`, no
   default/zero value) in every module, std included; only the runtime
   entry shim, which is not Fors source, creates the values it passes to
   `main`. Every reachable value of one MUST trace to a `main` parameter,
   directly or by narrowing (e.g. `fs.Dir.open_dir`, downward-only: it
   MUST yield only a subdirectory of its receiver, never a sibling or
   ancestor). A generic function cannot produce one either: a type
   parameter instantiated at a root-capability type gains no constructor
   (generics are checked once, on the declaration). Forging one by
   reinterpreting bytes is possible only inside an
   `@unsafe(invariant: "...")` declaration and therefore MUST appear in
   the published unsafe inventory (Rule 9's ledger); it is a breach of the
   trusted base, not a language feature.
8. `main` is the function named `main` declared in the build's root
   module; it MUST NOT be generic, `extern` or `comptime`, and a function
   named `main` in any other module is an ordinary function to which the
   runtime supplies nothing. `main`'s parameters MUST each be, exactly and
   nominally, one of the eleven root-capability types (Rule 21) — not a
   trait such as `io.Writer`, a `dyn` type, a type parameter, a tuple, or
   a qualified or wrapped form — and each type MUST appear at most once in
   `main`'s parameter list; a `main` parameter of any other type MUST be a
   compile error. The runtime supplies each argument by that nominal
   type. For every `main` parameter, the capability Rule 21 pairs with its
   type MUST be declared in the root module's `needs { ... }` (Rule 1);
   `main` MUST be the sole
   root of capability values, and no function other than `main` MAY obtain
   a root capability except by being handed one, as an ordinary parameter,
   by a caller that already holds it.
9. A module holding `ffi` MUST be marked `unguaranteed`; every transitive
   importer MUST inherit that mark in the audit ledger, `fors audit` and
   the published unsafe/FFI inventory. Sealing (Rule 2) stops the
   *capability* at the holder; it MUST NOT stop this *taint*.
10. `@unsafe(invariant: "...")` MUST be a declaration attribute only, never a
    block/statement form, with a non-empty invariant string.
11. Comptime MUST run on exactly one engine, the FMIR interpreter; no second
    comptime path (macro expander, separate constant-folder) MAY exist.
12. Comptime MUST be pure and deterministic: no capability value, clock, RNG,
    env read, or ambient I/O MAY be reachable.
13. Every comptime file read MUST be declared in the module header's
    `inputs { "path", ... };` clause (ch07 header grammar, after `needs`
    and before `use`) and enter the build graph, and the reproducibility
    hash, as a content-hashed edge keyed on that path; a comptime file read
    whose path is not listed there MUST be a build error.
14. Every comptime evaluation MUST be charged against a step and an
    allocation budget (manifest-declared, else the named constants
    `COMPTIME_STEP_BUDGET` / `COMPTIME_ALLOC_BUDGET`, whose numeric values
    are set by measurement and not yet fixed — Open question 1);
    exceeding either MUST be a build error naming the declaration.
15. A comptime body MAY tier up to native code only if the compiler proves no
    address observation (no ptr-to-int cast, no cross-allocation pointer
    comparison, no reachable `rawptr`); otherwise it MUST run interpreted.
16. The build graph MUST be declarative data with no executable step; a
    manifest/lockfile entry naming a script or command to run MUST be
    rejected.
17. Resolution MUST use minimal-version selection; the lockfile MUST pin each
    dependency's resolved version, capability set, and sealed holdings
    (package, module, capability).
18. A resolved capability set or sealed holding not within the locked one
    (including a dependency that newly holds a sealed capability after an
    update, even if the manifest already permits its package) MUST fail the
    build, naming the dependency and added capability, unless overridden by
    `fors grant <dep> <cap>`, which MUST record a reason string.
19. A security-release channel MAY widen a capability set without `fors
    grant` only with a recorded signer identity and reason; an unapproved
    widening MUST be rejected identically to Rule 18.
20. A dynamic Fors module MUST carry a signed interface declaring its
    capability set (exported requirement and sealed holdings); the loader MUST refuse one whose set exceeds the host's
    grant (a load-time integrity check, not address-space isolation).
21. The root-capability type set is closed and owned by this chapter, so
    that no two root capabilities ever share a type. Type -> capability
    that Rule 8 requires in root `needs`: `io.Stdout` -> `io.stdout`,
    `io.Stderr` -> `io.stderr`, `io.Stdin` -> `io.stdin`, `fs.Dir` (the
    process working directory) -> `fs.read` or `fs.write` (at least one;
    each operation on it still needs its own capability under Rule 1),
    `net.Net` -> `net`, `proc.Exec` -> `exec`, `time.Clock` -> `clock`,
    `rand.Rng` -> `rng`, `env.Env` -> `env`, `env.Args` -> `env`,
    `gpu.Device` -> `gpu`. `io.Stdout` and `io.Stderr` are distinct nominal
    types that each implement the trait `io.Writer` (`io.Stdin`:
    `io.Reader`); they are usable where a `T: io.Writer` bound or a
    `dyn io.Writer` is expected, but the trait is never a root-capability
    type, so the runtime never has to choose between them. No other type
    MAY be used as a `main` parameter (Rule 8), and this list MUST NOT be
    extended except by editing this chapter.
22. Inline assembly (`asm_expr`, ch07 grammar) MUST appear only inside a
    declaration marked `@unsafe(invariant: "...")` (Rule 10) in a module
    whose own `needs` holds the sealed `asm` capability (Rules 1-2); an
    `asm_expr` violating either MUST be a compile error Inline assembly
    is a sealed operation (Definitions), so Rule 2a applies unchanged: it
    MUST NOT appear in a generic function, a cross-module-inlinable
    function or a closure passed out of the holder, and comptime
    evaluation reaching it is a build error. The Rule 24 target guard is a
    comptime test *around* the block, never an evaluation of it.
23. An `asm_expr` instruction of syscall class (`svc`, `syscall`,
    `sysenter`, `int`) additionally requires the module's own `needs` to
    hold the sealed `syscall` capability, and MUST be found by the Rule 4
    machine-code scan exactly as any other syscall-class instruction;
    holding `asm` MUST NOT exempt it.
24. An `asm_expr` whose architecture (the `IDENT` naming it, ch07 grammar)
    is not the current build target MUST be a compile error, unless the
    block is lexically guarded by a `comptime` test on the build target
    that excludes it from compilation on that target.
25. Every register named in an `asm_expr`'s `in`, `out` or `clobber` items
    MUST be a valid register name for the block's architecture; the
    register sets named by `out` and `clobber` MUST be disjoint; either
    violation MUST be a compile error naming the block and register.
26. A `secret`-typed value MUST NOT be supplied as an `asm_expr` `in` input
    unless the enclosing declaration also carries `@ct_audited(by:
    "...")`, in which case the block MUST appear in the constant-time
    inventory (ch05); a `secret` input on an unaudited declaration MUST be
    a compile error.
27. The value of an `asm_expr` is its `out` register: unit `()` with no
    `out` item, the register's value with one, a tuple in `out`-item
    declaration order with several. Its type comes only from the expected
    type (CHECK mode, ch03 Rule 25): that type MUST be `()`, a scalar or
    pointer type that fits the register, or a tuple of such with one
    component per `out` item; anything else MUST be a compile error. An
    `asm_expr` used directly as an expression statement (`asm(...) { ... };`)
    is checked against `()`. An `asm_expr` in any SYNTH position (e.g.
    `let x = asm(...) { ... };` with no annotation, a method receiver, an
    operand) MUST be a compile error. This is a checker rule, never a
    parse error: the parser accepts `asm_expr` wherever `primary_expr` is
    legal (ch07).

## Examples

```fors
module img.decode;
needs { };                       // pure compute: zero authority
use core.mem, core.simd;
```

```fors
module hello;
needs { io.stdout };

fn main(inout out: io.Stdout) raises io.Error {
    out.write_line("hello")?;    // root capability handed in by the runtime, Rule 8
}
```

```fors
module fetch;
needs { net, io.stderr };        // capabilities, not type names (Rule 21)
use std.net;

fn main(inout net: net.Net, inout err: io.Stderr) raises net.Error {
    var buf: Buffer[u8] = Buffer.fixed(4096);
    let n: usize = get(&net, "https://example.org", &buf)?;
}

fn get(inout c: net.Net, let url: Str, inout out: Buffer[u8]) -> usize raises net.Error {
    return c.get_into(url, &out)?;   // c is handed down, not obtained fresh (Rule 8)
}
```

```fors
module drv.port;
needs { asm };

@unsafe(invariant: "port is a valid MMIO-mapped I/O port for this target")
fn out_byte(let port: u16, let value: u8) {
    asm(x86_64) {
        in(dx) = port,
        in(al) = value,
        "out dx, al",             // no `out` item: statement form, value `()`, Rule 27
    };
}
```

```fors
module vendor.blas;
needs { ffi, asm };              // sealed: importers do not need them (Rule 2),
use std.ffi;                     // but inherit the ffi taint (Rule 9); the
                                 // manifest must permit package `vendor` to
                                 // hold ffi and asm (Rule 2b); asm is still
                                 // syscall-scanned (Rule 4)

@unsafe(invariant: "n matches the caller-allocated buffer length")
extern "c" fn dgemm(let n: i32, let a: rawptr[f64]);   // no `raises`: ch02 Rule 13
```

```fors
module std.fs;
needs { syscall, fs.read, fs.write };   // holder: syscall stays here
```
```fors
module app.cfg;
needs { fs.read };                       // checked requirement {fs.read}; no syscall
use std.fs;
```

## Rejected alternatives

- Plain transitive union for `syscall`/`asm`/`ffi`: every std importer would need `syscall`, making the grant meaningless (owner decision D2).

- Single declaration site (manifest-only or `needs`-only): R9 requires both, so declared authority and actual use are independently reviewable.
- `asm`/`syscall` folded into `@unsafe`: conflates memory-safety risk with ambient-authority risk.
- Two comptime engines: rejected by R8; two purity regimes, two possibly-disagreeing oracles.
- Sandboxed executable build scripts: still a payload that can diverge from declared behavior (xz-utils pattern); data-only graph makes this inexpressible.
- Semantic (not byte-scan) syscall detection: unsound against inline asm and hand-encoded sequences with no LLVM isel guarantee to lean on.
- A single aggregate `World` value: any function receiving it could reach
  every root capability regardless of its declared `needs`, defeating
  least-privilege; replaced by one distinct type per root capability,
  handed out only via `main`'s parameter list (owner decision, R2-1).
- `@comptime_input(path)` as a per-read attribute: scattered across a
  module's declarations instead of being one auditable header fact;
  replaced by the `inputs { ... };` header clause (owner decision, R2-1's
  companion cleanup).

## Decisions made while drafting

- Capability names are the chapter brief's list verbatim; PLAN.md itself names only an illustrative subset.
- Rule 15's "no address observation" test is a syntactic predicate, not an abstract-interpretation proof, per the no-solver constraint.
- Verifier additions: Rule 4 now states scan coverage precisely and that
  `asm` does not exempt from it (the draft example claimed the opposite);
  Rule 4a makes `ffi` the explicit top capability, because no scan can
  see into a foreign object; absent `needs` = empty.
- Owner decision 2026-09-19 (D2): `syscall`/`asm`/`ffi` are sealed
  (Rules 2-2b, 17-18). Verifier additions closing laundering paths: use
  is attributed to the source module, so a re-exported `extern` needs
  `ffi` in the caller; sealed operations are banned from generic,
  cross-module-inlinable and escaping-closure bodies so the byte scan
  stays per-object; comptime cannot reach them (Rule 2a).
- The comptime budget default is a named token, not a number — a tuning decision, not an authority-model one.
- Security-release widening (Rule 19) is a lockfile field, not a manifest section, keeping the lockfile the single resolved-truth artifact.
- Owner decision 2026-09-19, round 2 (R2-1): authority enters only through
  `main`'s parameters, typed from the closed list in Rule 21, each at most
  once (Rule 8) and each declared in root `needs` (Rule 1).
- Owner decision 2026-09-19, round 2 (R2-4): inline assembly ships from
  v0.1. Verifier decisions: statement-form `asm` is a CHECK position
  against `()` (Rule 27), since the owner text gives a no-`out` block the
  value unit; `env.Args` is paired with the `env` capability (Rule 21). `asm` is sealed like `syscall`/`ffi` (Rule 6); a syscall-class
  instruction inside `asm` still needs the Rule 4 scan and `syscall`
  itself; a secret input reuses ch05's `@ct_audited` discipline rather
  than a new mechanism.
- Comptime file-read declarations move from a per-declaration attribute to
  the module header's `inputs { ... };` clause (Rule 13), matching
  `needs`'s shape and covering every input in one reproducibility hash.

## Attack classes this model does not stop

Confinement is an authority boundary, not an information-flow one: a module
legitimately granted `net` can still exfiltrate data it legitimately reads.
Also unstopped: abuse of a capability the module was correctly granted;
a permitted holder that exports an over-wide wrapper (a `pub fn
raw_syscall`) — sealing makes holders the trusted base, which is why
Rule 2b names them per package and Rule 18 blocks new ones;
"capability laundering" through a granted `ffi` subtree (already marked
unguaranteed, but unguaranteed code can do anything); a pure-compute module
(`needs {}`) that is a logic bomb with no authority to exercise; and tier-A
`dylink` integrity checks, which verify the declared set but do not isolate
the address space, so a same-process dynamic module can still corrupt memory
within its granted authority.

## Open questions for the owner

1. Comptime budget default value; does `--release`/`--secure` change it?
2. Who signs a security-release widening — maintainer key, registry key, or both?
3. Does dynamic-module loading require the host to declare `dyn.load` itself?

## Conformance tests

- `needs-undeclared-capability-rejected`: using `net` without declaring it fails.
- `needs-transitive-union-accepted`: importer inherits an imported module's exported capability.
- `sealed-not-propagated`: importer of a `syscall` holder builds with `needs { fs.read }` and a policy lacking `syscall` for it.
- `sealed-holder-package-must-be-named`: a non-std package holding `asm` without a manifest entry naming that package fails; `std` passes by default.
- `sealed-gain-on-update-blocks-build`: a dependency newly holding `ffi` fails until `fors grant`, even if its package is permitted.
- `sealed-extern-reexport-needs-ffi`: calling another module's `pub extern "c" fn` without own `ffi` fails.
- `sealed-op-in-generic-rejected`: inline asm / `extern` call inside a generic or cross-module-inlinable function fails.
- `sealed-op-at-comptime-rejected`: comptime call reaching a sealed operation fails.
- `ffi-taint-crosses-seal`: importer of an `ffi` holder needs no `ffi` but is listed `unguaranteed`.
- `policy-subset-enforced`: requirement exceeding manifest policy fails.
- `link-time-recheck-catches-swapped-bmi`: an inflated substituted BMI fails at link despite a passing build.
- `syscall-scan-rejects-undeclared-instruction`: inline `svc`/`syscall` without `syscall` fails with a site diagnostic.
- `syscall-scan-covers-asm-and-text-constants`: a module with `asm` but
  not `syscall` whose inline asm (or a text-section constant) encodes
  `svc` fails the scan.
- `ffi-reported-as-top`: `fors audit` lists a dependency granted `ffi` as
  holding every capability.
- `needs-absent-means-empty`: a module with no `needs` clause using
  `io.stdout` fails.
- `asm-without-capability-rejected`: inline assembly without `asm` fails before codegen.
- `capability-value-no-public-constructor`: constructing `fs.Dir`/`time.Clock`/`rand.Rng`/`gpu.Device` outside `main`-parameter narrowing fails.
- `ffi-taint-propagates`: a transitive importer of an `ffi` module is marked `unguaranteed`.
- `unsafe-attribute-rejects-block-form`: bare `unsafe { ... }` is a parse/checker error.
- `comptime-rejects-clock-read`: a comptime clock read fails to build.
- `comptime-undeclared-file-read-rejected`: an undeclared comptime file read fails.
- `comptime-budget-exceeded-named`: exceeding the step budget fails, naming the declaration.
- `comptime-tierup-rejected-on-address-observation`: a ptr-to-int cast blocks tier-up.
- `build-graph-rejects-script-entry`: a manifest/lockfile executable-command entry is rejected.
- `lockfile-capability-gain-blocks-build`: a resolved superset of the locked set fails until `fors grant`.
- `fors-grant-records-reason`: `fors grant` persists a non-empty reason string.
- `security-release-widen-requires-approval`: an unapproved widening is rejected like Rule 18.
- `dylink-loader-refuses-excess-capability`: a dynamic module exceeding the host's grant fails to load.
- `main-param-type-closed`: a `main` parameter of a type outside Rule 21's
  eleven fails, including `io.Writer`, `dyn io.Writer` and a generic `main`.
- `main-outside-root-module-is-ordinary`: a function named `main` in a
  non-root module receives nothing from the runtime.
- `asm-value-typing`: statement-form `asm` with no `out` passes; `let x =
  asm(...) { out(x0), "..." };` (SYNTH position) fails in the checker, not
  the parser; an expected tuple whose arity differs from the `out` count
  fails.
- `main-param-duplicate-type-rejected`: two `main` parameters of the same
  root-capability type fail.
- `main-param-must-be-in-needs`: a `main` parameter of a declared type
  whose capability is missing from the root module's `needs` fails.
- `root-capability-only-from-main`: a non-`main` function constructing a
  root-capability value, or obtaining one other than as a handed-down
  parameter, fails (Rule 7-8).
- `no-world-type-exists`: no stdlib symbol named `World` exists.
- `asm-requires-unsafe-and-capability`: an `asm_expr` outside
  `@unsafe(invariant: ...)`, or in a module lacking `asm`, fails.
- `asm-syscall-class-requires-syscall-capability`: an `svc`/`syscall`
  instruction inside `asm` without the module's own `syscall` fails.
- `asm-wrong-architecture-rejected-without-guard`: an `asm(x86_64)` block
  compiled for `aarch64` with no comptime target guard fails; guarded,
  passes.
- `asm-register-clobber-overlap-rejected`: an `asm_expr` naming the same
  register in `out` and `clobber` fails.
- `asm-invalid-register-rejected`: an `asm_expr` naming a register invalid
  for its architecture fails.
- `asm-secret-input-requires-ct-audited`: a `secret` value as an `asm` `in`
  input without `@ct_audited(by: ...)` fails; with it, passes and appears
  in the constant-time inventory.
- `comptime-input-clause-required`: a comptime file read whose path is
  absent from the module's `inputs { ... };` clause fails.
- `comptime-input-clause-enters-hash`: two builds differing only in an
  `inputs`-declared file's contents produce different reproducibility
  hashes.

Sources: `docs/design/safety-security.md` §5–7; `docs/design/surface-language.md` "Capability surface", "Five programs" (1),(4).
