# Chapter 4: Authority — capabilities, comptime and the build

## Status

Draft, M0.5, 2026-09-19. Implements PLAN.md R8 (comptime: one engine) and R9
(capability declaration has two sites: manifest = policy, `needs` =
requirement). Normative per §4.2: conflicts with `docs/design/*.md` resolve
in this chapter's favor.

## Scope

Owns: the capability name set; `needs { ... }` as requirement; the manifest's
per-target/per-dependency field as policy (an upper bound); the
requirement-⊆-policy check and when it runs; `asm`/`syscall` as capabilities
distinct from `@unsafe`; scanning emitted code for syscall-class instructions;
where capability values appear and how `main` gets root authority; the `ffi`
taint rule; `@unsafe(invariant: "...")`'s grammatical form (not its runtime
semantics — ch01); the comptime engine's identity,
purity and budgets; the build graph's no-executable-steps rule; lockfile
capability pinning, `fors grant`, and the security-release channel; dynamic
module capability signing. `iso`/`imm`/`secret`, conventions, and the failure
ABI belong to other chapters and are only referenced here.

## Definitions

- **Capability**: `fs.read, fs.write, net, exec, ffi, clock, rng, env,
  io.stdout, io.stderr, io.stdin, gpu, asm, syscall`.
- **Requirement**: the set named in a module's `needs { ... }`.
- **Policy**: the manifest's per-target, per-dependency capability bound.
- **Root capability**: obtainable only from `main`'s `sink World` parameter.
- **Taint**: a ledger-recorded fact (metadata), not a runtime check.

## Rules

1. A module MUST declare every capability it uses, or constructs a
   capability value from, in `needs { ... };` in its header (after
   `module` and any `contracts:` line, before `use`); an undeclared use
   MUST be a module-graph compile error. An absent `needs` clause MUST
   mean `needs { };` (zero authority).
2. Checked requirement = `declared ∪ transitive(imports)` over the acyclic
   module graph; a cyclic graph MUST be rejected before this check runs.
3. The build MUST fail unless requirement ⊆ policy for every module and
   target; this MUST be checked once at build time over the full graph and
   again at link time against signed BMIs.
4. A module whose checked requirement (Rule 2) lacks `syscall` MUST have
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
6. `asm` and `syscall` are checked as ordinary capabilities under Rules 1–3
   and MUST NOT be implied by, or imply, `@unsafe`.
7. Capability-value types (`io.Writer`, `fs.Dir`, `Clock`, `Rng`,
   `gpu.Device`) MUST have no public constructor; every reachable value MUST
   trace to `main`'s `World`, directly or by narrowing.
8. `main` MUST have signature `fn main(sink w: World) [raises E] { ... }` and
   MUST be the sole root of capability values.
9. A module requiring `ffi` MUST be marked `unguaranteed`; every transitive
   importer MUST inherit that mark in the audit ledger and `fors audit`.
10. `@unsafe(invariant: "...")` MUST be a declaration attribute only, never a
    block/statement form, with a non-empty invariant string.
11. Comptime MUST run on exactly one engine, the FMIR interpreter; no second
    comptime path (macro expander, separate constant-folder) MAY exist.
12. Comptime MUST be pure and deterministic: no capability value, clock, RNG,
    env read, or ambient I/O MAY be reachable.
13. Every comptime file read MUST be declared via `@comptime_input(path)` and
    enter the build graph as a content-hashed edge; an undeclared read MUST
    be a build error.
14. Every comptime evaluation MUST be charged against a step and an
    allocation budget (manifest-declared, else the named constants
    `COMPTIME_STEP_BUDGET` / `COMPTIME_ALLOC_BUDGET`);
    exceeding either MUST be a build error naming the declaration.
15. A comptime body MAY tier up to native code only if the compiler proves no
    address observation (no ptr-to-int cast, no cross-allocation pointer
    comparison, no reachable `rawptr`); otherwise it MUST run interpreted.
16. The build graph MUST be declarative data with no executable step; a
    manifest/lockfile entry naming a script or command to run MUST be
    rejected.
17. Resolution MUST use minimal-version selection; the lockfile MUST pin each
    dependency's resolved version and capability set.
18. A resolved capability set not a subset of the locked set MUST fail the
    build, naming the dependency and added capability, unless overridden by
    `fors grant <dep> <cap>`, which MUST record a reason string.
19. A security-release channel MAY widen a capability set without `fors
    grant` only with a recorded signer identity and reason; an unapproved
    widening MUST be rejected identically to Rule 18.
20. A dynamic Fors module MUST carry a signed interface declaring its
    capability set; the loader MUST refuse one whose set exceeds the host's
    grant (a load-time integrity check, not address-space isolation).

## Examples

```fors
module img.decode;
needs { };                       // pure compute: zero authority
use core.mem, core.simd;
```

```fors
module fetch;
needs { net, io.stderr };
use std.net;

fn main(sink w: World) raises net.Error {
    var client: net.Client = move w.net;       // narrowing from the root, Rule 7
    var buf: Buffer[u8] = Buffer.fixed(4096);
    let n: usize = get(client, "https://example.org", &buf.slice)?;
}

fn get(let c: net.Client, let url: Str, inout out: Slice[u8]) -> usize raises net.Error {
    return c.get_into(url, &out)?;
}
```

```fors
module vendor.blas;
needs { ffi, asm };              // ffi: tainted, top authority (Rule 4a);
use std.ffi;                     // asm: still syscall-scanned (Rule 4)

@unsafe(invariant: "n matches the caller-allocated buffer length")
extern "c" fn dgemm(let n: i32, let a: rawptr[f64]);   // no `raises`: ch02 Rule 13
```

## Rejected alternatives

- Single declaration site (manifest-only or `needs`-only): R9 requires both, so declared authority and actual use are independently reviewable.
- `asm`/`syscall` folded into `@unsafe`: conflates memory-safety risk with ambient-authority risk.
- Two comptime engines: rejected by R8; two purity regimes, two possibly-disagreeing oracles.
- Sandboxed executable build scripts: still a payload that can diverge from declared behavior (xz-utils pattern); data-only graph makes this inexpressible.
- Semantic (not byte-scan) syscall detection: unsound against inline asm and hand-encoded sequences with no LLVM isel guarantee to lean on.

## Decisions made while drafting

- Capability names are the chapter brief's list verbatim; PLAN.md itself names only an illustrative subset.
- Rule 15's "no address observation" test is a syntactic predicate, not an abstract-interpretation proof, per the no-solver constraint.
- Verifier additions: Rule 4 now states scan coverage precisely and that
  `asm` does not exempt from it (the draft example claimed the opposite);
  Rule 4a makes `ffi` the explicit top capability, because no scan can
  see into a foreign object; absent `needs` = empty.
- The comptime budget default is a named token, not a number — a tuning decision, not an authority-model one.
- Security-release widening (Rule 19) is a lockfile field, not a manifest section, keeping the lockfile the single resolved-truth artifact.

## Attack classes this model does not stop

Confinement is an authority boundary, not an information-flow one: a module
legitimately granted `net` can still exfiltrate data it legitimately reads.
Also unstopped: abuse of a capability the module was correctly granted;
"capability laundering" through a granted `ffi` subtree (already marked
unguaranteed, but unguaranteed code can do anything); a pure-compute module
(`needs {}`) that is a logic bomb with no authority to exercise; and tier-A
`dylink` integrity checks, which verify the declared set but do not isolate
the address space, so a same-process dynamic module can still corrupt memory
within its granted authority.

## Open questions for the owner

0. **Privileged-capability sealing.** Rule 2's transitive union means
   every importer of `std.fs`/`std.net` inherits std's own `syscall` (and
   `asm`/`ffi` where std uses them), so every real program's policy must
   grant `syscall`, making it meaningless. Either (a) a designated trusted
   set (std, signed) may *seal* `syscall`/`asm`/`ffi`, exporting only the
   API-level capability (`fs.read`, `net`), or (b) accept the union and
   treat `syscall` as std-only by policy convention. Blocks the manifest
   schema, the lockfile capability sets, `fors audit`, and std's layout.
1. Comptime budget default value; does `--release`/`--secure` change it?
2. Who signs a security-release widening — maintainer key, registry key, or both?
3. Does dynamic-module loading require the host to declare `dyn.load` itself?

## Conformance tests

- `needs-undeclared-capability-rejected`: using `net` without declaring it fails.
- `needs-transitive-union-accepted`: importer inherits an imported module's capability.
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
- `capability-value-no-public-constructor`: constructing `fs.Dir`/`Clock`/`Rng`/`gpu.Device` outside `World` narrowing fails.
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

Sources: `docs/design/safety-security.md` §5–7; `docs/design/surface-language.md` "Capability surface", "Five programs" (1),(4).
