# 05. The IR contract: levels, alias classes, secrets, tiles and parallel regions

## Status

Draft, M0.5, 2026-09-19. Implements PLAN.md R10 (secret/`ct_region`/tile/
alias IR homes), R11 (CFG-SSA + e-graph, restricted autovectorizer) and R13
(DWARF companion artifact). Normative for the **compiler**, not the surface
language; `docs/design/*.md` conflicts resolve in this chapter's favor
(§4.2).

## Scope

Owns: the IR level sequence (tokens → AST → FIR → FMIR → OIR → LIR →
atoms) and which level is source-of-truth for which fact; mandatory
verifier-checked fields (alias class + disjointness set; secret bit +
`ct_region`; the allocator's secret spill class; `detach` capture lists);
FMIR→OIR lowering of `spawn`/`sync` to Tapir `detach`/`reattach`/`sync`
and serial-elision legality; `tile.*`'s FMIR-only placement and the
FMIR→OIR device-pipeline fork point; the optimizer's shape (CFG-SSA,
acyclic e-graph, restricted autovectorizer scope); the constant-time rule
set and post-regalloc CT verifier; bit-for-bit differential agreement
across both backends and the interpreter; the unsigned DWARF companion
artifact.

Not owned: the qualifier/arena lattice (ch01); failure ABI and traps
(ch02); reduction shape, its before-parallel-lowering order, and FP
contraction scoping (ch03); capability manifests, `needs`, and the
identity of the comptime engine (ch04 — Rule 3 here only fixes the IR it
reads); SIMD/GPU/tensor surface syntax (future
chapters) — this chapter pins only where their compiled facts live.

## Definitions

- **FIR**: typed, still-generic semantic IR; the sole binary module
  interface — no textual re-inclusion.
- **FMIR**: checked mid IR — ownership/isolation, contracts, `spawn/sync`,
  `tile.*`, secret-taint origin; the only IR the interpreter, comptime VM,
  race checker and contract prover read.
- **OIR**: CFG-SSA optimizer IR; Tapir `detach`/`reattach`/`sync`.
- **LIR**: SoA machine IR, pre-allocation.
- **Atom**: one encoded function/global.
- **Alias class**: an opaque disjointness-set id on a memory operand.
- **`ct_region`**: an id grouping operations under constant-time rules.
- **Isolation-domain capture list**: the typed list of values a
  `detach`/`spawn` moves or shares into its region.
- **Serial elision**: rewriting every `detach` to an unconditional branch.

## Rules

1. The compiler MUST implement exactly tokens → AST → FIR → FMIR → OIR →
   LIR → atoms; no pass MUST touch a level out of order.
2. FIR MUST be the only serialized binary module interface; downstream
   compiles MUST NOT re-parse an imported module's source text.
3. FMIR MUST be the sole input to the interpreter, comptime VM, race
   checker and contract prover.
4. Every OIR memory op MUST carry an alias-class + disjointness-set
   operand; `--verify-each` MUST reject any lacking one.
5. An alias class MUST derive only from parameter convention, affine
   ownership, arena brand id, split-token provenance, or SoA field
   identity; one untraceable to these five MUST fail verification.
6. Every FMIR/OIR/LIR value MUST carry a secret bit and `ct_region` id as
   non-optional fields; `--verify-each` MUST reject any lacking them.
6a. Secret propagation is a local FMIR type rule: the result of any
   operation with a secret operand is secret; `secret` on an aggregate
   covers every field and its discriminant; a secret value MUST NOT be
   stored to, passed as, or returned as a non-secret type. The only
   removal is `@declassify(reason)`, legal only inside an
   `@unsafe(invariant: "...")` declaration and listed in the audit
   inventory. The CT rules apply to every operation with a secret
   operand, everywhere; `ct_region` only groups them for the verifier.
6b. FMIR checking MUST reject, with a source diagnostic: a branch, loop
   bound, or `match` on secret; an index, slice bound or address from
   secret; any trapping operation on a secret operand (plain `+ - * / %`,
   shifts, checked `as`, bounds-checked indexing — each hides a branch;
   use `wrap_`/`sat_`/`ct_` forms); a secret in a `pre`/`post`/`invariant`
   (ch02 Rule 9); a `raise` or `?` whose *taken-ness* depends on secret;
   and a secret argument to a capability-value method (I/O, logging). An
   error *payload* MAY be secret-typed: it stays secret in the handler,
   so branching on it is rejected there by this same rule. Rule 15 is the
   backstop that re-checks these after optimization.
7. The allocator MUST expose a distinct spill class for secret values; one
   spilled outside it MUST fail verification.
8. A secret spill store MUST be exempt from dead-store elimination and
   store-forwarding and MUST be zeroized before the epilogue; either
   omission MUST fail the CT verifier (rule 15).
9. `detach` MUST carry an explicit typed capture list as an IR operand; no
   pass MUST reconstruct it from alias classes.
10. FMIR `spawn`/`sync` MUST lower to OIR `detach`/`reattach`/`sync`;
    rewriting every `detach` to a branch MUST stay a legal,
    verifier-accepted rewrite for every verifying program.
11. A value defined in a detached region MUST NOT be used after its `sync`
    except through memory that region owns, checked as dominance.
12. `tile.*` MUST appear only in FMIR; the device pipeline MUST fork from
    FMIR before OIR lowering; a `tile.*` op found in OIR or LIR MUST fail
    verification.
13. The optimizer MUST be CFG-SSA with an acyclic e-graph (dedup-on-insert,
    no fixed-point saturation); sea-of-nodes MUST NOT be used anywhere.
14. The autovectorizer MUST fire only on a countable loop with
    trusted-length or affine access and no cross-iteration dependence
    disproved by alias classes; otherwise it MUST NOT transform the loop.
15. A post-regalloc CT verifier MUST run in both backends and MUST reject
    a function whose `ct_region` has: a branch on secret; an address/index
    from secret; a denylisted instruction on a secret operand; a
    synthesized `@ct_select` branch; or a rule-8 violation.
16. Constant folding, CSE, inlining and PGO/layout passes MUST propagate
    `ct_region`/secret unchanged, MUST NOT consume secret-derived profile
    data, and MUST NOT reorder across a `ct_region` boundary.
17. Both backends and the interpreter MUST produce bit-for-bit identical
    output (including which trap site fires) on every accepted program
    that contains no `@fastmath` block and no `reduce.fast` (ch03), for
    identical inputs and capability-value responses, exercised by a
    differential runner across {interp, dev, release -O1/-O2/-O3,
    `--serial-elide`}.
18. Dev-tier debug info MUST live only in an unsigned companion artifact;
    a debug-info-only edit MUST NOT change the signed image's
    CodeDirectory hash.

## Examples

```fors
needs { };

fn scale_halves(inout buf: Slice[f64], let k: f64) {
    let (lo, hi) = split_at(&buf, buf.len / 2);   // ch01 Rules 19-19b
    parallel {
        spawn scale(&lo, k);
        scale(&hi, k);
    }                                             // implicit sync
}
```
Split halves get distinct alias classes from split-token provenance
(rule 5); the surface `parallel { spawn ...; }` (implicit sync at the
closing brace) becomes FMIR `spawn`/`sync`, then OIR
`detach`/`reattach`/`sync` (rule 10) with an explicit capture list (rule 9).

```fors
fn ct_compare(let a: secret u64, let b: secret u64) -> secret bool {
    return ct_eq(a, b);      // accepted: no branch, no denylisted op
}

fn leaky(let a: secret u64, let table: Slice[u64]) -> u64 {
    if a > 0 { return table[a]; }    // REJECTED (rule 6b): branch on secret,
    return 0;                        // index from secret, secret -> public
}
```

```fors
@device
fn gemm_tile(inout c: Tile[f32, 16, 16], let a: Tile[f32, 16, 16], let b: Tile[f32, 16, 16]) {
    tile.dot(&c, a, b);
    tile.sync();
}

@device
fn bad_kernel(let a: secret u64) -> secret u64 { return a; }   // REJECTED: secret in @device
```
`tile.*` exists only in FMIR and never reaches OIR (rule 12; the `@device`
surface belongs to a future chapter); secret is banned there per the
drafting decision below.

## Rejected alternatives

- Sea-of-nodes mid-IR: dissolves loop structure serial elision and tiling
  both need.
- Secret bit/`ct_region` as optional metadata: droppable, like
  undisciplined alias metadata.
- Trusting passes, not a verifier, for CT: optimizers break CT code doing
  their job correctly.
- Autovectorization with reassociation: belongs to `@fastmath(reassoc)` (ch03).
- Device fork after OIR: isolation facts are already erased by then.

## Decisions made while drafting

- **Secret is forbidden inside `@device`/`@tensor` code.** PLAN is silent;
  CT cannot be guaranteed through a vendor compiler (MSL, StableHLO/MIL),
  so FMIR rejects any secret value flowing into such a signature/capture.
- **`tile.*`'s home is FMIR, not a separately named "PIR."** The design
  docs name one level two ways; FMIR is canonical per R10/R11.
- **Alias-class merges are "merge and record," never silent.** A merge
  unable to prove rule-5 provenance MUST emit an alias-precision record —
  decidable with no whole-program analysis.
- **Verifier additions (rules 6a/6b).** The draft never said what makes a
  value secret downstream or what a `ct_region` covers, so contracts,
  trapping arithmetic, indices and raise conditions on secrets were
  uncaught until post-regalloc. Propagation and rejection are now FMIR
  type rules (from `safety-security.md`'s static rule list); rule 15
  remains as the verify-don't-trust backstop. Rule 17 now exempts
  `@fastmath`/`reduce.fast`, whose results legitimately differ by backend.
- **Spill-class assignment is syntactic**: a value gets the secret spill
  class whenever its secret bit is set at the spill decision.
- **`--serial-elide` is mandatory, not optional, in rule 17**: it is the
  cheapest available oracle.

## Open questions for the owner

1. The variable-latency denylist depends on undocumented Apple silicon
   timing. Default until measured: conservative ban, or trust the DIT bit
   where advertised?
2. Is the secret-in-`@device` ban permanent, or should the spec reserve a
   future `@spectre_hardened` opt-in once a vendor toolchain is audited?

3. `@declassify(reason)` is drafted as `@unsafe`-gated and audited;
   `surface-language.md` instead calls it "capability-gated". Which gate?

## Conformance tests

- `ir_verify_alias_missing_rejected` — OIR memory op with no alias class:
  rejected.
- `ir_verify_alias_source_five_only` — alias class untraceable to the five
  sources: rejected.
- `ir_verify_secret_fields` — construct missing secret bit/`ct_region`, or
  a secret value spilled outside its class: rejected.
- `ct_no_branch_or_index_on_secret` — branch, or address/index, derived
  from secret: compile error.
- `secret_propagates` — `let x: u64 = s.wrap_add(1)` with `s` secret:
  rejected; with `x: secret u64`: accepted.
- `secret_trapping_op_rejected` — `s + 1`, `s as u8`, `t[s]` on secret
  `s`: rejected at FMIR.
- `secret_raise_condition_rejected` — `raise` under a secret-derived
  condition rejected; secret-typed error payload accepted but branching
  on it in the handler rejected.
- `declassify_requires_unsafe` — `@declassify` outside an `@unsafe`
  declaration rejected.
- `ct_denylist_rejected` — denylisted instruction on secret, `@ct_select`
  lowered to a branch, or an un-zeroized secret spill: fails the CT
  verifier in both backends.
- `secret_forbidden_in_device` — secret into `@device`/`@tensor`: error.
- `detach_capture_explicit` — `detach` with no typed capture list: rejected.
- `detach_no_use_after_sync` — detached value used post-sync other than
  via sync-owned memory: error.
- `serial_elision_always_legal` — rewriting all `detach`es to branches
  typechecks for every accepted program.
- `tile_ops_fmir_only` — `tile.*` in OIR or LIR: rejected.
- `autovectorizer_scope_limit` — vectorizer skips a loop with an
  alias-undisproven cross-iteration dependence.
- `backend_bitforbit_agreement` — interp/dev/release outputs are
  byte-identical on the differential corpus.
- `dwarf_companion_unsigned` — debug-only edit leaves the signed image's
  CodeDirectory hash unchanged.
