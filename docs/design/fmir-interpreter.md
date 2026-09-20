# Fors design: FMIR and its interpreter (`fors-fmir`, `fors-lower`, `fors-interp`)

> **Status: design draft, 2026-09-20 (round 6 semantics), revised after adversarial review —
> see §13.** An implementation CONTRACT in the genre of `docs/design/type-checker.md`: crates, data
> structures, a rule-to-mechanism table, numbered increments each gated on NAMED corpus tests,
> measured budgets, open questions with recommended answers, ranked risks with the cheapest
> retiring experiment. Normative inputs: `docs/PLAN.md` §4.2 (R2-R8, R10, R11),
> `docs/spec/05-ir-contract.md`, `01-ownership.md`, `02-failure.md`, `03-numerics-determinism.md`,
> `04-authority.md`, `10-std.md`, and `docs/design/compiler-architecture.md` §1, §5, §8. Where this
> conflicts with a spec chapter, the chapter wins; every place the spec is **silent or
> self-contradictory** is marked **[HOLE-n]** and collected in §11.1 or §11.3.

---

## 1. Scope and non-goals

### 1.1 What M1 must do

PLAN §4.1: *"One FMIR interpreter, three jobs: comptime VM, Miri-class reference semantics, differential-testing oracle."* M1 is the
first two, plus the oracle harness with only one side of the comparison present (there is no backend until M2). The acceptance gate
is fixed and already written: the **64 runtime conformance tests** — 37 `run-ok`, 19 `trap`, 8 `run-error` — which nothing can run
today.

The three jobs and their M1 evidence: **reference semantics** — every dynamic MUST rule of ch01/02/03 and the run-time rules of
ch04/ch10 is executed, and every erroneous condition a compiled program would get silently wrong is DETECTED, not approximated (§8's
table; the 19 `trap` tests); **comptime VM** — ch04 R11-R15, one engine, pure, declared inputs, step and alloc budgets,
content-addressed results (F9; ch04's five comptime tests); **oracle** — deterministic, replayable, with a stable comparison record
and a reducer (F10; with no backend yet the M1 exit is *self*-differential, `--interp` twice, and `--serial-elide` once `spawn`
exists).

FMIR surface for those 64 tests and nothing beyond: scalars `i8..i64`, `u8..u64`, `usize`, `f32`, `f64`, `bool`, `()`, `never`,
`Str`, `Array[T, N]`, `Slice[T]`, tuples, `struct`, `enum` (incl. payloads), `Own[T, A]`, `Ref[T, A]`, `Arena[T, A]`, `fn` values
and closures; conventions `let`/`inout`/`sink`/`set` with destructive moves; scoped projections (R3); linear obligations;
`defer`/`errdefer`; `raises`/`?`/`else |e|`; contracts; traps; arena brands and generation checks; `reduce`; and the `secret` bit
and `ct_region` id as carried, verified fields plus the FMIR checks R6a/R6b themselves (§3.11).

### 1.2 Non-goals for M1 (named, with the milestone that owns them)

| Deferred | Owner | Why it can wait |
|---|---|---|
| `spawn`/`sync` scheduling, `parallel`/`parallel for`, continuation stealing, fibers | M3 | Zero of the 64 tests contain `spawn` or `parallel`. FMIR must still **represent** them (§3.7) so serial elision is a legal rewrite from day one; M1 executes a `spawn` region by running it inline, which IS the serial elision, and asserts the capture list is well-formed. |
| `tile.*`, `@device`, `kernel`, the device fork point | M6 | ch05 R12 fixes the home; no op is defined yet. The verifier rejects `tile.*` outside FMIR from F0, which costs nothing. |
| `vector[T, N]`, `mask[N]`, `simd for`, `SVec` | M3/M7 | No run test uses them. `reduce`'s 8 logical lanes are **not** SIMD: ch03 R11 requires scalar emulation to give the same answer, which is what M1 does. |
| Tier-up of hot comptime to the dev backend (ch04 R15, PLAN R8) | M2 | There is no backend. The purity precondition (no address observation) is computed in M1 and recorded; nothing consumes it yet. |
| Full ch01 exclusivity (R6-R9), sendability (R12-R13), race checking | M3 | The type checker's §8 table already defers these. FMIR carries the access events; the checker pass that consumes them is M3. |
| `libm`, float formatting, transcendentals | M4+ | **No test needs one.** ch10 R10(f) keeps floats unformatted in v0.1, and every float test compares against a literal. M1 uses `+ - * / %`, comparison and conversion only. |
| Alias-class *computation* and disjointness, `ct_region` grouping, the CT verifier | M5 | ch05 R4/R15 are OIR/LIR obligations. What M1 owes is not the classes but their five **seeds** (§3.4a): OIR cannot recover an arena brand id or a split-token provenance that FMIR threw away. M1 carries the seeds and computes nothing. |

## 2. Crates

Zero external dependencies, edition 2024, no crate below depends on one above.

| Crate | Owns | Depends on | Size estimate |
|---|---|---|---|
| **`fors-fmir`** | the IR data model (SoA pools, `DeclFmir`, instruction encoding), the canonical byte encoding + `fmir_hash`, the **verifier**, the textual dump/parse used by tests and the reducer | `fors-index` (ids, `Symbol`, fingerprint), `fors-fir` (`TyId`, `SigStore`, layout) | ~2.2k lines |
| **`fors-lower`** | checked bodies → FMIR: CST walk driven by `BodyFacts`, defer/errdefer inlining, `?` edges, contract ops, `reduce` shaping, monomorphization-vs-witness decision (PLAN R6) | `fors-fmir`, `fors-fir`, `fors-check`, `fors-syntax`, `fors-resolve`, `fors-index` | ~2.5k lines |
| **`fors-interp`** | the interpreter: value/memory model, dispatch loop, trap machinery, budgets, the host surface (`intrinsic.rs`), comptime mode, oracle record | `fors-fmir`, `fors-fir`, `fors-index` | ~3k lines |

**Why three.** (1) *The verifier must not see the checker*: if `fors-fmir` could call `fors-check`, ch05 R4/R6's "`--verify-each`
MUST reject" would test the checker twice instead of the IR once — a CI grep asserts `crates/fors-fmir/src` mentions neither
`fors_check` nor `fors_syntax`, the gate the type-checker design already puts on `fors-fir`. (2) *The interpreter must not see the
CST* (ch05 R3): it is the oracle, and if it could consult source it could be right for a reason no backend can reproduce; a second
grep asserts it. (3) `fors-lower` is separate because it is the only crate that *shrinks* as the checker grows — every piece of it
reads a decision the checker already made (§4). Folding it into `fors-fmir` would put `fors-check` under the verifier.

**[HOLE-1] The crate name contradicts the architecture doc.** `compiler-architecture.md` §9 lists `fors-mir` and `fors-interp`; ch05
names the level **FMIR** normatively and notes the design docs "name one level two ways". I choose `fors-fmir` (level name = crate
name, as `fors-fir` already does) and `fors-lower` (§9 lists no lowering crate at all). An engineering call (E2), but §9's list
should be corrected rather than left to drift.

## 3. The FMIR data model

### 3.1 Shape: struct-of-arrays, `u32` indices, no pointers

Three forces fix this, all from outside the interpreter. The **query engine** (PLAN §5) keys everything on a content hash per
declaration, and a pointer-linked IR is not content-hashable; SoA pools with declaration-relative `u32` indices hash by `hash_bytes`
over the pools. **The rewrite in Fors**: Fors has no `Rc`, no interior mutability and destructive moves, so an index-and-pool IR is
expressible in Fors verbatim and an arena of `&'a mut` nodes is not. **The reducer** (`compiler-architecture.md` §8, "SoA-level
delta-debugging"): deleting an instruction is a splice plus an index remap, not graph surgery.

```rust
/// One declaration's FMIR. Self-contained: every index is relative to this
/// struct's own pools, so a `DeclFmir` is content-hashable and movable
/// between processes without fixups.
pub struct DeclFmir {
    pub decl:     DeclKeyId,         // identity (fors-fir::defpath)
    pub sig:      FnSigId,           // the FIR signature this body implements
    // --- value universe -------------------------------------------------
    pub vals:     ValPool,           // SoA, one row per FMIR value
    // --- code -----------------------------------------------------------
    pub blocks:   BlockPool,         // SoA: first_inst, inst_len, term, scope
    pub insts:    InstPool,          // SoA: op, a, b, c, ty, site
    pub operands: Vec<ValId>,        // variadic operand spill (calls, phis)
    // --- structure (§3.3) ------------------------------------------------
    pub scopes:   ScopePool,         // the lexical scope tree
    pub places:   PlacePool,         // interned (root, [Field|Index|Deref])
    pub regions:  RegionPool,        // spawn / parallel / with-arena regions
    // --- side tables -----------------------------------------------------
    pub sites:    SitePool,          // SiteId -> (span, TrapKind slot, decl)
    pub consts:   ConstPool,         // comptime-known values, content-addressed
    pub fingerprint: u128,           // blake3 of the canonical encoding
}

/// One FMIR value. 12 bytes. There is no `Vec<Box<..>>` anywhere.
#[repr(C)]
pub struct ValRow {
    pub ty:     TyId,     // u32, interned in fors-fir
    pub flags:  u16,      // SECRET | CONST | SCOPED | LINEAR | ISO | IMM | TMP
    pub ct:     u16,      // ct_region id; 0 = none (ch05 R6: NON-OPTIONAL)
    pub def:    u32,      // defining instruction, or PARAM|u16 for parameters
}
```

`flags.SECRET` and `ct` are **not** `Option`: ch05 R6 requires exactly this, a field that cannot be absent cannot be dropped by a
pass, and it is free because the row is fixed-width.

### 3.2 Structured control flow or CFG: **CFG + a scope tree**

A pure structured tree has no terminators for ch05 R10's `detach`/`reattach`/`sync` and makes OIR construction a second lowering; a
pure CFG loses the nesting that R10, R12 and ch01 R23a's *static* pending-defer set all need. Both fail, and for different reasons.

**Decision.** FMIR is a **CFG of basic blocks** — SoA, one terminator each, reducible by construction (Fors has no `goto`) — **plus
a scope tree that is an annotation on blocks, never a control-flow structure.** Each block names its `ScopeId`; each scope records
its parent, its arena brand (§3.4a), its pending `defer`/`errdefer` body ranges, its linear obligations and its region membership.
Nothing about execution reads the scope tree: it exists so that (a) OIR lowering rebuilds Tapir regions without analysis, (b) the
verifier checks ch05 R11 (no use of a detached value after its `sync`) as a dominance question inside a known region, and (c) the
reducer deletes a whole scope atomically. Consequence: **`defer` needs no runtime stack** — ch01 R23a says so explicitly.
`fors-lower` emits the pending bodies at each exit edge as ordinary blocks (§3.8), so the interpreter has no defer machinery at all,
which is also exactly why a trap runs no defer (ch02 R7): there is nothing to run.

### 3.3 Places, moves, conventions

```rust
pub enum Seg { Field(u16 /*field index*/), Index(ValId), Deref }
pub struct PlaceRow { root: u32 /*local slot*/, segs: Range<u32>, ty: TyId }
```

A place is interned per declaration (same shape as `fors-check::tape::PlaceId`, extended with `Deref` for `Own`/`Ref`). Moves are
**destructive and explicit**:

| Op | Meaning | Checker source |
|---|---|---|
| `move_from p -> %v` | reads `p`, marks its slot **dead** | tape `UseKind::Move` |
| `copy_from p -> %v` | reads `p`, leaves it live (`T: Copyable` only) | tape `UseKind::Copy` |
| `init p <- %v` | writes `p`, marks it **live** | tape `Assign`/`Declare` |
| `borrow_mut p -> %r` | `inout` argument / `&x` marker | tape `MutBorrow` |
| `borrow_out p -> %r` | `&out x`, target **uninitialised** on entry | tape `OutBorrow` |
| `borrow p -> %r` | `let` argument | tape `Read` |

Call-site conventions are recorded per argument on the call instruction, never inferred:
`CallRow { callee, args: Range<u32>, convs: Range<u32>, ... }` with `convs[i] ∈ {Let, Inout,
Sink, Set}`. ch01 R2's implicit receiver move (`x.finish()` with `sink self`) lowers to
`move_from` exactly like `move x`, and a test asserts the two produce identical instruction
sequences modulo the site id, mirroring the checker's
`implicit_and_explicit_receiver_move_produce_identical_tapes`.

### 3.4 Scoped projections (PLAN R3, ch01 R19-R19d)

A `flags.SCOPED` value carries `sources: Range<u32>` into a `SourcePool` of `PlaceId`s — the set ch01 R19c(d) says a result keeps
from EVERY scoped argument. The verifier checks, per declaration and with no interprocedural analysis:

- a `SCOPED` value is never stored through `init` into a place whose root is not a local of the current or an inner scope (R19a: no
  field, container, heap object, outer binding);
- a `SCOPED` value is never an operand of `erase_to_dyn` (R19a, R22f);
- a `SCOPED` value returned by `ret` has exactly one source, and that source's root is the parameter the signature's `scoped(p)`
  names (R19);
- the access to each source is live across the receiving binding's scope (R19a's extent) — the scope tree makes this an interval
  check.

### 3.4a Alias seeds — the five sources of ch05 R5, carried not computed

ch05 R5 closes the derivation of an OIR alias class to five sources, and ch01 R7's "note for the backend" repeats the list. Three of
the five are **erased by the checker** and are unrecoverable at OIR unless FMIR carries them, which is why they are fixed-width
fields here and not a later pass:

| R5 source | FMIR carrier | Note |
|---|---|---|
| parameter convention | `CallRow.convs[i]`, and the callee signature's own conventions | ch01 R7: a `let` parameter is **not** a no-alias fact and MUST NOT seed one |
| affine ownership | `PlaceRow.root` + the `move_from`/`init` chain | an `Own[T, A]` root is its own seed |
| arena brand id | `ScopeRow.brand: BrandId` and `AliasSeed::Arena(BrandId)` on every `arena_alloc`/`arena_deref` result | **compile-time IR metadata only** (ch05 R5, ch01 R15e): it has no runtime representation, the interpreter never reads it, and two distinct brand *parameters* are NOT assumed disjoint |
| split-token provenance | `AliasSeed::Split{parent: PlaceId, side: u8}` recorded by `slice_range` and by any ch01 R19b split | without it `split_at`'s two halves alias in OIR and the headline SoA/SPMD win disappears |
| SoA field identity | `PlaceRow.segs` (`Field(i)` under a `soa` head) | derivable from the place, no extra field |

```rust
pub enum AliasSeed { None, Conv(Conv), Own(PlaceId), Arena(BrandId), Split { parent: PlaceId, side: u8 } }
```
`AliasSeed` is one `u64` per memory-producing instruction, in its own pool. The verifier checks only that every memory-producing
instruction has a seed row and that an `Arena` seed names a brand in scope; **disjointness is M5's**. Gate:
`alias_seed_present_on_every_memory_op`, `arena_brand_survives_lowering`, `split_at_halves_get_distinct_seeds`.

### 3.5 Linear obligations (ch01 R22-R22i, round 6)

`flags.LINEAR` is set by `fors-lower` from `lin(T)` (ch01 R22a), which `fors-fir` computes. Each scope row carries `obligations:
Range<u32>` into an `ObligPool` of `PlaceId`. At every block whose terminator leaves a scope, the verifier requires each obligation
of the scopes being left to have a **discharge record** on that edge:

```rust
pub enum Discharge { MovedTo(InstId), DeferredBody(ScopeId, BodyId), Raised(InstId), Returned }
```

The interpreter does **not** re-derive this (R22h is static, and [HOLE-11] says whose), but it **asserts** it: in Miri mode a scope
exit whose obligation has no discharge record is the interpreter diagnostic `linear-leak`, not a trap. A leak reaching the
interpreter is a **compiler bug**, and a compiler bug must not look like a program trap — there is no trap kind for it in ch02 R15's
closed list of eight, and inventing one would violate that rule.

### 3.6 `raises` / `?` / traps / contracts

- A `raises E` function's FMIR signature returns `(tag: u32, ok: T, err: E)` abstractly. **The interpreter never models ch02 R4's
  register classifier** (`FAILURE_INLINE_MAX`, `FAILURE_TAG_REG = x9`): that is an ABI fact with no observable consequence above
  LIR. §8 records this as a rule the interpreter structurally *cannot* be the oracle for.
- `?` is a **terminator**, `try_br { call: InstId, ok: BlockId, err: BlockId }`. The `err` edge is the "error exit" of ch02 R16, and
  it is the edge `errdefer` bodies attach to. `else |e| { }` is an ordinary two-way branch on the tag with the handler inline;
  because the handler decides (ch02 R16), the edge out of a value-yielding handler is a NORMAL exit and carries no `errdefer`
  bodies.
- `ErrorFrom[E, F]` (ch02 R3) is resolved by the checker and lowered as an ordinary call on the `err` edge, exactly once — the
  verifier rejects two conversion calls on one edge (R3's "MUST NOT chain a second conversion").
- `trap { kind: TrapKind, site: SiteId }` is a terminator with **no successors**. Its kind is one of ch02 R15's eight; `TrapKind` is
  a Rust enum with exactly eight variants and a `const KINDS: [&str; 8]` asserted against the corpus's `detail:` strings by a test,
  so a ninth kind cannot be added without a spec edit.
- `check_pre` / `check_post` / `check_inv` are instructions, not calls, each with a `policy: {Runtime, Off}` field resolved from the
  module's `contracts:` line at lower time. **The interpreter never consults an optimisation level** — ch02 R10 / PLAN R7 — and a
  test (`contract_policy_is_not_a_flag`) asserts the interpreter has no `-O` input at all.

### 3.7 Arenas, brands, generation checks (PLAN R2, ch01 R15-R18)

Brands are erased from the **type** after checking (ch01 R15e), so an FMIR `Ref[T, A]` has no brand in its `TyId`. They are **not**
erased from the IR: ch05 R5 makes "arena brand id" one of the five alias sources and calls it "compile-time IR metadata only", so
the brand survives as an `AliasSeed` (§3.4a) that no execution reads. What survives at run time is the other half:

```rust
pub struct ArenaVal { id: ArenaId, gen: u32, bump: usize, cap: usize, data: AllocId }
pub struct RefVal   { arena: ArenaId, gen: u32, off: u32 }   // 12 bytes
```

`arena_deref %r -> %p` compares `RefVal.gen` against the live `ArenaVal.gen` and traps `arena-generation` on mismatch. ch01 R17 says
*"in every build mode, never elided by optimization level"*, so the check is an instruction with no `may_elide` bit — there is no
representation in which it could be dropped. `arena_reset` bumps `gen` (wrapping is a verifier-rejected condition: `gen == u32::MAX`
traps `arena-generation` preemptively rather than aliasing an old generation — **[HOLE-2]**, ch01 R17 does not say what a wrapped
counter does).

### 3.8 `defer` / `errdefer` regions

`fors-lower` records, per scope, `defers: Range<u32>` into a `DeferPool`:

```rust
pub struct DeferRow { kind: DeferKind /*Defer|ErrDefer*/, body: BlockId, stmt_order: u16 }
```

and emits, at each exit edge of that scope, the pending bodies **inlined in reverse `stmt_order`**, interleaved across `Defer` and
`ErrDefer` in one order (ch01 R23b), with `ErrDefer` bodies present only on error edges. The `DeferPool` itself is kept for three
consumers: the verifier (asserting every exit edge of a scope carries exactly the right multiset), the reducer, and OIR's later
"emit one copy and jump to it" size optimisation that R23a explicitly permits.

`ret e` / `raise e` evaluate and `move_from` the operand **before** the first deferred body block, which is R23a's *"`e` is
evaluated, and moved into the result, BEFORE any body runs"* — made structural by the block order, not by a runtime rule.
`defer-result-evaluated-first-run-ok` is exactly this test.

### 3.9 `reduce`, and the one place the spec cannot be implemented literally

ch03 R12: *"`reduce` MUST lower to this explicit tree in FMIR **before** parallel lowering."* **[HOLE-3] This is impossible for a
runtime-length input, and the corpus contains one.** `reduce-n257-shape-run-ok` reduces a `Slice[f64]` whose length is a runtime
value as far as FMIR is concerned; an "explicit tree" would have to be unrolled at a length nobody knows.

Resolution, and I believe it is what R12 means: FMIR gets **one** instruction `reduce_tree { op: Callee, xs: ValId, identity:
Option<ValId>, b: u32, l: u32, site: SiteId }` with `b = REDUCE_BLOCK = 256` and `l = REDUCE_LANES = 8` as **literal operands**, not
implicit constants, plus a normative expansion given once in `fors-fmir::reduce.rs` that the interpreter executes and every backend
must implement identically. When `n` is comptime-known, `fors-lower` additionally emits the fully unrolled tree and the verifier
asserts the two agree — the only form in which "lower to the explicit tree" is checkable. What R12 actually buys is preserved: the
shape is fixed **before** parallel lowering, so `--serial-elide` is bit-exact. Owner **Q3** proposes the reword.

Expansion, normatively (ch03 R11, R11a, R13), 40 lines of straight-line code:

```
reduce(op, xs, id?):
  n = len(xs)
  if n == 0: return id if present else trap(empty-reduce, site)
  k = ceil(n / B)
  for each block j in 0..k:                         # consecutive elements
      m = size of block j                           # B, or n mod B for the last
      for lane i in 0..min(m, L):                   # lane fold, ascending
          acc = x[j*B + i]
          for t in 1.. while i + t*L < m: acc = op(acc, x[j*B + i + t*L])
          lane[i] = acc
      # lane combine: ((l0∘l1)∘(l2∘l3))∘((l4∘l5)∘(l6∘l7)), lower lane LEFT,
      # a node with one empty operand yields the other UNCHANGED (no op call),
      # a node with two empty operands is empty.   NO identity padding (R13a).
      part[j] = combine(lane[0..L])
  # block combine: pairwise (0,1),(2,3),... per level; unpaired last carried up
  while k > 1: part[i] = op(part[2i], part[2i+1]) for pairs; carry odd tail; k = ceil(k/2)
  return part[0]
```

`identity` never participates for `n >= 1` (R11a), so both forms are bit-identical on non-empty input — asserted by
`reduce-identity-no-effect-n3-run-ok`. Hand-checking the expansion against the corpus reproduces every pinned value: n = 7 gives
`((x0-x1)-(x2-x3))-((x4-x5)-x6)` = 83.0, n = 9 gives `(((x0-x8)-x1)-(x2-x3))-((x4-x5)-(x6-x7))` = -301.0, and n = 257 gives
`op(block0, x256)` = -1.0 with all `xi = 1.0`.

### 3.10 The instruction set

**71 opcodes in M1**, counting the groups below exactly as listed and taking `wrap_`/`sat_`/`unchecked_` as a 2-bit **mode field**
on the eight trapping arithmetic opcodes rather than as 24 further opcodes (the earlier "62" did not match this table). Operand
shape is `(a, b, c)` `ValId`s plus `ty` and `site`; anything variadic spills to `operands`.

| Group | Ops |
|---|---|
| Constants | `const_int`, `const_float`, `const_bool`, `const_unit`, `const_str`, `const_fn` |
| Arithmetic (trapping) | `add`, `sub`, `mul`, `div`, `rem`, `shl`, `shr`, `neg` — each traps per ch03 R2 |
| Arithmetic (explicit) | `wrap_*`, `sat_*`, `unchecked_*` (ch03 R4) |
| Float | `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fneg` — **no `fma` opcode exists in M1** (ch03 R7); `@fastmath` sets a per-instruction `relax: u8` bitmask |
| Compare / logic | `icmp`, `fcmp`, `and`, `or`, `xor`, `not` |
| Conversion | `conv_checked` (traps `checked-conversion`), `conv_wrap`, `conv_sat`, `conv_trunc` |
| Aggregate | `agg_new`, `field`, `variant_new`, `discr`, `payload`, `tuple_new` |
| Place / memory | `move_from`, `copy_from`, `init`, `borrow`, `borrow_mut`, `borrow_out`, `index` (traps `bounds`), `slice_range` (traps `bounds`) |
| Heap / arena | `alloc`, `free`, `arena_alloc`, `arena_deref`, `arena_reset` |
| Calls | `call_direct`, `call_witness`, `call_closure`, `intrinsic` |
| Contracts | `check_pre`, `check_post`, `check_inv` |
| Reduce | `reduce_tree` |
| Erasure / secret | `erase_to_dyn`, `declassify` (verifier: only inside `@unsafe`, ch05 R6a) |
| Regions (M3 shells) | `region_enter`, `region_exit`, `spawn`, `sync` — represented, verified, executed serially in M1 |
| Terminators | `br`, `cond_br`, `switch_discr`, `try_br`, `ret`, `raise`, `trap`, `unreachable` |

`intrinsic` is the single door to the host (§5.6); the verifier requires its callee to be in a closed table, so a new host effect
cannot be smuggled in.

### 3.11 `secret` propagation and rejection (ch05 R6a, R6b)

ch05 calls these "a local FMIR type rule", and no increment of `type-checker.md` claims them — its §15 excludes "ch05's
constant-time verification beyond the `secret` flag". So FMIR owns them, and both are cheap because both are local.

- **R6a, propagation (`fors-lower`).** `ValRow.flags.SECRET` is set on a result iff any operand is secret; `agg_new`/`variant_new`
  set it on the aggregate and it covers every field and the discriminant; `init` into a non-secret-typed place with a secret operand
  is rejected. The only clearing op is `declassify`, which the verifier accepts only inside a declaration carrying
  `@unsafe(invariant:)` and records in the audit inventory.
- **R6b, rejection (`fors-fmir::verify`).** A source-located diagnostic, never a trap, for each of: `cond_br`/`switch_discr`/loop
  bound on a secret operand; `index`/`slice_range` with a secret index or bound; any *trapping* arithmetic, shift or `conv_checked`
  with a secret operand (`wrap_`/`sat_`/`ct_` are the escape); a secret operand of `check_pre`/`check_post`/`check_inv` (ch02 R9); a
  `raise`/`try_br` whose taken-ness depends on secret; a secret argument to a host-effecting `intrinsic`. A secret error *payload*
  is accepted and stays secret, so branching on it in the handler is rejected by the same pass.
- `ValRow.ct` is `0` for every value in M1 and only checked for presence; grouping semantics are M5 (§1.2). `0` is a legal region
  id, not an `Option` sentinel — the field cannot be absent, which is R6's whole point.

The datum this needs from the checker is **D13** (§4.1): the `secret` qualifier on each expression's type. Gate, as `fors-fmir` unit
tests and as `tests/conformance/05-ir/` (§8.1): `secret_propagates`, `secret_trapping_op_rejected`,
`ct_no_branch_or_index_on_secret`, `secret_raise_condition_rejected`, `declassify_requires_unsafe`, `ir_verify_secret_fields`.

## 4. The interface the checker must expose to lowering

This is a **scheduling document as much as a data one**: the checker's increments I0-I11 and the interpreter's F0-F10 run in
parallel only where the data below already exists.

### 4.1 What is needed, and which checker increment provides it

| # | Datum | Exact shape | Provided by | Status today |
|---|---|---|---|---|
| D1 | per-expression type | `expr_ty: Vec<TyId>` indexed by body CST node | I3 | **computed and DISCARDED** — see [HOLE-4] |
| D2 | resolved callee | `Callee::{Direct(DefId, ArgsId), TraitMethod{trait_def, method: DefId, self_ty: TyId, args: ArgsId}, Closure(ValId), Builtin(BuiltinOp)}` per call node | I4 (trait methods), I5 (generic args) | absent |
| D3 | receiver convention | `Conv` per method call, plus per-argument `Conv` per call | **I4** — `type-checker.md` §13 puts R43 (inherent-before-trait lookup) and R46's typing side in I4, not I3; I3 resolves only free calls and struct literals | in the tape only, not retained |
| D4 | field / variant resolution | `(head DefId, field index)` per projection; `(enum DefId, variant index)` per construction and pattern | I3 / I6 | partial |
| D5 | pattern decision material | per `match`: arm order, per-arm binding list with `PlaceId`s and `Conv`, exhaustiveness witness or proof | I7 | absent |
| D6 | move / liveness decisions | per place: move points, re-init points, the loop-head merge result | I8 | tape emitted, `flow.rs` absent |
| D7 | defer / errdefer decisions | per scope: ordered `(kind, body block, stmt_order)`; per exit: the multiset that runs; per body: the place→strongest-access summary of R23d | **nobody** — see [HOLE-11] | absent |
| D8 | linear obligations and discharges | per scope: obligation places; per exit edge: `Discharge` per obligation; `lin(T)` per type | **nobody** — see [HOLE-11] | absent |
| D9 | scoped sources | per value: the source `PlaceId` set of ch01 R19c(d) | **nobody** — see [HOLE-11]; R19a extents are M3 per the checker's §8 | absent |
| D10 | contract policy | per declaration: `Runtime` or `Off`, from the module's `contracts:` line | I10 | absent |
| D11 | mono-vs-witness decision | per call site with a bound: `Mono(instantiation key)` or `Witness(table id)` per PLAN R6 / ch03 R16-R18 | **nobody** — see [HOLE-5] | absent |
| D12 | layout | `size_of`, `align_of`, field offsets, enum discriminant encoding, in `Target` width | **nobody** — see [HOLE-6] | absent |
| D13 | `secret` qualifier per expression type | one bit, from the FIR type's qualifier | I10 (ch01 R14 `lower::quals` lands it on signatures at I2; the body side is I3's `expr_ty` once D1 exists) | signatures only |

**[HOLE-4] `BodyFacts` is named but not landed.** `type-checker.md` §4.2 lists `facts.rs` — *"`BodyFacts` (typed side table:
`expr_ty`, `callee`, `recv_conv`, resolved members), FMIR's input"*. I3 has landed (`crates/fors-check/src/` has `body.rs`,
`expr.rs`, `call.rs`, `member.rs`, `tape.rs`) but there is **no `facts.rs`**, and `CheckOutput` (`lib.rs:37`) carries `diagnostics`,
`fir`, `defs`, counters, `check_sites` and `deps` — no per-expression type, no callee map, no tape. Every increment from F1 onward
is blocked on this. *Recommendation:* add `facts.rs` as a **strictly additive** I3 follow-up (`I3.5`, ~250 lines: a `BodyFacts` SoA
filled by the existing `synth`/`check` recursion, plus retaining the tape) before F1 starts — the smallest possible unblocking
change, testable on its own (`body_facts_cover_every_typed_node`).

**[HOLE-11] Round 6's linearity and `defer` rules are owned by no checker increment — this is the schedule's real critical path, not
`BodyFacts`.** `docs/design/type-checker.md` is dated the same day as round 6 but is a ch09 document: its §8 rule-to-code table has
rows for ch01 R2, R3, R4a, R8, R10-R18, R19-R19b and R21-R21d and **none for ch01 R22-R22i (linearity), R23-R23f
(`defer`/`errdefer`) or R19c/R19d (scope inheritance through a call, closure captures)**; the words `defer`, `errdefer` and `Linear`
do not occur in it. §15 ("what this design does not cover") does not list them either, so they are not deferred — they were never
considered. I8's own scope is exactly "ch01 R3, R4a(a)-(e), R8's loop-head merge for moves, R46's message". Worse, §8 routes ch01
**R4 and R5** ("`sink` moved on every path; `set` initialised on every return") to *"not in v0.1 M1: M3 (needs definite-init
dataflow)"* — and R22h's scope-exit check is that same dataflow.

Consequence: F4 and F6 are not "blocked on I8", they are blocked on checker work **nobody has planned**, and three data (D7, D8, D9)
that this design declares as inputs have no producer. That is rework inside `fors-check`, and it is the finding this document exists
to surface. *Recommendation:* a new checker increment **I8b — round-6 flow** (opus, ~900 lines, after I7 because R22d(ii)'s "every
linear component bound by a pattern" needs exhaustiveness): `lin(T)` in `fors-fir` (ch01 R22a-R22c, a memoised structural descent,
~120 lines); the definite-init lattice R4/R5 already need; R22d-R22i's scope-exit check over the live set; R23-R23f's static pending
set, the R23d place→strongest-access summary and R23b's "`errdefer` with no error exit" rejection; R19c/R19d's source sets. Its gate
is ch01's round-6 corpus, which already exists (the README's round-6 note counts +52 ch01 tests for R19c and R22-R23f). Until I8b is
scheduled, F4's and F6's *lowering* halves are speculative and only their interpreter halves (the `ub:` machinery, arena
generations, `@alloc`/`@free`) can proceed.

**[HOLE-5] Nobody owns the monomorphization decision.** PLAN R6 and ch03 R16-R18 fix the rule; the type-checker's §8 table routes
ch03 R16-R18 to "FMIR/OIR, not in v0.1 M1". *Engineering call:* `fors-lower` owns it, computing it from (a) the instantiation's
scalar-ness and size against `MONOMORPHIZE_SIZE_MAX = 16`, (b) the callee's FMIR instruction count against
`MONOMORPHIZE_INSTR_THRESHOLD`, and caching by ch03 R17's key `(declaration hash, argument type shape hashes)`. It needs D12.

**[HOLE-6] No chapter defines type layout.** ch09 §"delegations" routes *"Layout, alias classes, `soa` representation"* to ch05;
ch05's Scope owns alias classes, secrets, tiles and parallel regions and says nothing about layout. ch10 R13 defines the `Layout`
*type* and `MEM_MAX_ALIGN = 16` but not the layout *algorithm*. The interpreter needs it for `Layout.of[T]()`, `Own`, `Vec`,
`Buffer`, `Array` indexing, `Block`, and for D11's 16-byte test. This is an **owner decision** (§11 Q1) because it is observable:
`Layout.of[T]().size` is a value a program can branch on.

### 4.2 What can start when

**Immediately, on no checker output at all:**

- **F0** — entirely. Data model, encoding, verifier, textual dump, round-trip and negative tests over hand-built FMIR. This is the
  `spikes/fir-normalise` pattern: build the representation and test it against synthetic input before any real input exists. F0 also
  writes R6's negative corpus (§12) and the `tests/conformance/05-ir/` directory (§8.1, owner Q5).

**After I3 + the `BodyFacts` follow-up ([HOLE-4]) + I4:**

- **F1**. The earlier draft of this section claimed F1 needs only I3. That is **false**: every one of F1's 19 gate tests ends in
  `out.write_line("ok");`, an **inherent method call on a root-capability value**, and `type-checker.md` §13 puts inherent method
  lookup (R43) and receiver conventions (R46, typing side) in **I4**, not I3 — I3 resolves only free calls and struct literals. So
  F1 needs D1, D2, D3 and D4, i.e. I3.5 **and** I4. What F1 does *not* need is I5-I8: no gate test is generic, has a `defer`, holds
  a linear value or uses `?`. `for x in xs` over a `Slice` is also safe — ch09 R31 makes `for` over `Range`/`Array`/`Slice` a
  language-known form, so it does **not** drag in `Iterator`, I4's provided methods or I7's `Option` patterns.
- **F2** — contracts, entry shim, exit statuses, `Stderr`. D10 is I10's, but `contract-off-no-check-run-ok` needs the policy to be
  `.off`, so a "default to `Runtime`" stand-in does not pass the gate: until I10, `fors-lower` **reads the module header's
  `contracts:` line itself** (it already depends on `fors-syntax`) and I10 later replaces that read with D10. Recorded as
  engineering call E11.
- **F5** — `reduce`. Needs D1 and a checker rule that types `reduce` at all — which **no increment in `type-checker.md` §13 claims**
  ([HOLE-7]: ch03 R11's `reduce` is a language primitive, not a function; I3's gate list and I10's "ch03 R6, R19-R24a" both omit
  R11). F5's lowering hard-codes the primitive's typing until an increment adopts it; the shape is F5's own, so nothing about the
  tree depends on that adoption.

**After I5/I6/I7:** F7 (provided `Iterator` methods, `I.Item` projections, `Option` patterns), and the generic, brand-carrying
halves of F6.

**After a checker increment that does not yet exist ([HOLE-11]):** the *lowering* halves of **F4** (D7) and **F6** (D8), and every
linear-obligation assertion. Their *interpreter* halves — `Slot`/`Alloc` state, the `ub:` machinery, arena generations,
`@alloc`/`@free`, exit-edge block emission driven by a hand-written FMIR fixture — have no checker dependency and can be built and
tested against F0's textual FMIR first. That split is what keeps [HOLE-11] from stopping the track dead.

The critical path is **I3.5 → I4 → F1**, with **I8b → F4 → F6** running behind it, and F0, F2 and F5 available in parallel. F0 is
the only increment that can be handed to an implementer today with nothing else in flight.

## 5. The interpreter

### 5.1 Value representation

**The interpreter takes an explicit `Target`, never the host.** ch09 R3 gives `isize`/`usize`/`rawptr` "the target pointer" width,
so a `usize` value, a `Layout.of[T]().size` and every comptime result computed from them are target-dependent. `Target { ptr_bits:
u8, endian: Endian, layout_rule: u8 }` is an input to `fors-interp` and to `fors-lower`; the crates use Rust's own `usize` for host
bookkeeping (indices into pools) and **never** for a program-visible value, asserted by a CI grep that `usize` does not appear in
`value.rs`/`arith.rs`. v0.1's only targets are `aarch64-apple-darwin` and `x86_64-*`: `ptr_bits = 64`, `endian = Little`. Endianness
is observable — `@memcpy` plus a `Slice[u8]` view of an integer is one line of Fors — so it is pinned here rather than inherited.

**Every FMIR scalar fits in 64 bits.** ch03 R1 forbids 128-bit integers in v1, and `f64` is the widest float. That single fact
removes the usual tagged-union sprawl:

```rust
/// A scalar slot. 16 bytes. Aggregates never live here — they live in memory.
#[derive(Clone, Copy)]
pub struct Slot {
    pub bits: u64,          // zero-extended integer, bool, f32/f64 bit pattern
    pub prov: ProvId,       // NONE for non-pointers; else the pointer's provenance
    pub init: bool,         // Miri: is this slot initialised?
    pub secret: bool,       // ch05 R6, carried for the verifier and dumps
}
```

Frames are `Vec<Slot>` over one reusable stack arena; a call pushes a frame window and a return pops it. No per-value heap
allocation exists in the dispatch loop — that, plus a flat typed tape, is the whole of why `compiler-architecture.md` §8 expects to
beat Zig's AST-walking comptime.

Aggregates, arrays, `Str`, heap blocks and arena bodies live in **allocation objects**:

```rust
pub struct Alloc {
    pub bytes:   Vec<u8>,
    pub init:    BitVec,            // one bit per byte — uninit reads are DETECTED
    pub prov:    BTreeMap<u32, ProvId>, // provenance at pointer-sized offsets
    pub kind:    AllocKind,         // Stack | Heap(AllocatorId) | Arena(ArenaId) | Static | Capability
    pub gen:     u32,               // arena generation at creation
    pub state:   AllocState,        // Live | Freed(SiteId) | Reset(SiteId)
    pub align:   u32,
}
```

### 5.2 What makes it Miri-class: the detection list

The contract: *anything a compiled program would get silently wrong, the interpreter names.* Each row is detected and reported with
a site — as an interpreter diagnostic, distinct from a program `trap` unless the spec says it is one.

| Condition | Detection mechanism | Reported as |
|---|---|---|
| Use after move | place slot's `live` bit, set false by `move_from` | `ub: use-after-move` + the move site (compiler bug if it reaches here: the checker's ch01 R4a(a) should have caught it) |
| Double consume of a linear value | obligation record already discharged on this edge | `ub: double-consume` |
| Linear value leaked | scope exit with an undischarged obligation (§3.5) | `ub: linear-leak` |
| Arena generation mismatch | `RefVal.gen != ArenaVal.gen` | **`trap arena-generation`** (ch01 R17 — a program-visible trap) |
| Out-of-bounds index / slice | `index`/`slice_range` against the allocation extent | **`trap bounds`** |
| Integer overflow, div-by-zero, shift ≥ width, lossy checked `as` | per-op check (§5.5) | **`trap overflow` / `div-zero` / `shift` / `checked-conversion`** |
| Uninitialised read (incl. through `&out`) | `Alloc.init` bitmap / `Slot.init` | `ub: uninit-read` |
| `inout`/`sink`/`set` exclusivity violation | a borrow stack per allocation range with **two item kinds**: `borrow_mut`/`borrow_out` push a *unique* tag; `borrow` pushes into the topmost *shared-read-only group*. A read through any item of a live SharedRO group is legal and pops nothing; only a write or a new unique tag pops. **ch01 R7 makes two overlapping `let` accesses LEGAL** (`f(&x, &x)`-shaped calls are sound), so a single-tag Stacked-Borrows would report UB on accepted code — and because a `ub:` report exits 70, that would fail the corpus, not merely annoy. `ub_aliasing_accepts_two_let_borrows` and `ub_aliasing_accepts_nested_let_under_let` are gate tests of F6, ranked above the positive detections | `ub: aliasing` |
| Scoped value escaping | `flags.SCOPED` reaching `init` of an outer-scope place, a field, or `erase_to_dyn` | `ub: scope-escape` |
| Use of a freed or reset allocation | `AllocState` | `ub: use-after-free` (heap) / `trap arena-generation` (arena, because ch01 R17 makes it a program trap) |
| Wrong-allocator free | `AllocKind::Heap(id)` vs the freeing allocator | `ub: allocator-mismatch` (ch01 R18 makes the *typed* case a compile error; this catches the erased case) |
| Contract violation | `check_pre`/`post`/`inv` | **`trap contract`** |
| Empty `reduce` without identity | `reduce_tree` with `n == 0` | **`trap empty-reduce`** |

The `ub:` rows are **not traps**: ch02 R15 closes the kind list at eight, so a ninth would be a spec violation. A `ub:` diagnostic
exits with status `70` and a machine-readable record, so the differential runner can tell "the program is wrong" from "the compiler
is wrong".

### 5.3 Traps

`trap` is a **deterministic whole-process abort** (ch02 R7, PLAN R4): the interpreter prints one line to its own stderr — `trap:
<kind> at <file>:<L>:<C>` — with `<kind>` one of ch02 R15's eight strings, performs **no** deferred body (§3.8: there is nothing
pending to perform, because pending bodies are blocks on the *exit edges*, and `trap` has no successor), does **not** flush `Stdout`
(ch10 R40(b): buffered bytes MAY be lost, and the interpreter chooses to lose them, deterministically, so the oracle's answer is the
same every run), and exits by `raise(SIGTRAP)` so the harness sees a signal status, never 1 or 2 (ch10 R40(d): *"A TRAP is in
neither row"*).

`trap-runs-no-defer` and `defer-not-run-on-trap` test exactly this, both observing it through `Stderr` because `Stderr` is
unbuffered (ch10 R40); §7.2a pins how the runner reads them.

### 5.4 `raises` / `?` / `errdefer` ordering

The order at an error exit of `main`, from ch02 R17 + ch01 R23e, executed in exactly this sequence:

1. The error operand is evaluated and moved into the result (R23a).
2. The pending bodies of each scope being left run, innermost first, in one reverse textual order per scope, `errdefer` bodies
   included because this is an error exit (R23a, R23b). `main-raises-after-defer-run-error` fixes the observable order: the deferred
   line reaches `Stderr` before the runtime's `error: ` line.
3. The runtime flushes `Stdout` as on a normal return, **ignoring failure** (R17(a)). `main-raises-flushes-stdout-run-error` tests
   it.
4. It writes ONE unbuffered line to fd 2: `error: ` + `render(e)` + `\n` (R17(b)). `render` is on the **static** type and is
   implemented in `fors-interp::render.rs` as a direct reading of R17's clause list — fully-qualified path, `.`, variant, payload in
   `( )` or `{ name: … }`, integers base 10, `Str` between quotes with `\\ \" \n \r \t` escaped, every opaque type as `..`. Five
   tests pin it: `main-raises-unit-variant`, `-payload`, `-nested-payload`, `-std-error`, and `10-std/main-raises-exit-status-one`.
5. Exit status 1, whether or not 3 or 4 succeeded (R17(c)).

A handler that yields a value makes a **normal** exit (R16), so no `errdefer` runs — `handler-makes-normal-exit` and
`errdefer-skipped-on-return-run-ok`.

### 5.5 Integer semantics

Every trapping op is computed in `i128`/`u128` host width and range-checked against the FMIR type's bounds, then narrowed; that is
uniformly correct and, measured on the dispatch loop, costs less than a branch per op because the check is a single comparison pair.
`wrap_*` is two's-complement truncation; `sat_*` clamps to the type's bounds; `unchecked_*` is wrapping **plus** a Miri-mode `ub:
unchecked-overflow` diagnostic when the true result is out of range (ch03 R4 puts it behind `@unsafe(invariant:)`, so violating the
invariant is exactly a UB report, not a trap).

`frem` is the one arithmetic op whose obvious Rust spelling is a **libm call**: `f64 % f64` lowers to `fmod`. §5.6(4) forbids that,
and it would also make the oracle depend on the host's libm. `fmod` is *exact* — its result is representable with no rounding — so
`fors-interp::arith::frem` implements it in-crate by scaled repeated subtraction over the exponent range (≈30 lines, bit-exact by
construction, no rounding mode involved), and `frem_matches_reference_over_10e6_pairs` checks it against a table generated once. The
same rule bans `%` on floats being written as `%` anywhere in the crate (CI grep).

Two conditions the spec does not decide:

- **[HOLE-8] `i64::MIN / -1` and `i64::MIN % -1`.** ch03 R2 lists trapping on *"overflow, div-by-zero, or shift-by-≥-width"*. `MIN /
  -1` overflows a division. Which of the eight kinds? *Recommendation:* `overflow`, because the condition is representability, not a
  zero divisor. Needs a corpus test either way (§8 gap).
- **[HOLE-9] the shift operand's type and sign.** R2 says "shift-by-≥-width" and says nothing about a negative shift amount or a
  shift count whose type is wider than the shifted type. *Recommendation:* the count is `u32` by language rule and a wider or signed
  count is a compile error, so the runtime condition is exactly `count >= width`. Owner question 4.

### 5.6 Strict IEEE floats, and bit-exactness against future backends

ch03 R7 and ch05 R17 together demand that interpreter and both backends be **bit-for-bit identical**. The interpreter's guarantees:

1. **No fused operation exists.** There is no `fma` opcode (§3.10), and a CI grep asserts `f64::mul_add`/`f32::mul_add` appear
   nowhere in `crates/fors-interp/src`. `float-default-no-fma-run-ok` computes `a*b + c` against the unfused
   `-2.220446049250313e-16`, with the fused `-2.9511114736925357e-16` recorded as the failure signature. The decimal literals must
   reach FMIR correctly rounded, which is `fors-syntax`'s obligation, not one this crate can repair.
2. **Rounding mode is fixed** to round-to-nearest-even; the interpreter never touches the host FPCR/MXCSR and a startup assertion
   verifies the default. Point 5 is therefore a **software** canonicalisation inside `arith.rs`: nothing in M1 depends on DN=1, and
   what the backends must do to match is an M2 obligation this document cannot make good on.
3. **No x87, no extended precision**: `f32` arithmetic is computed in `f32`, never widened and narrowed back.
4. **No libm** — no transcendental, no `sqrt`, no float formatting (ch10 R10(f)); §5.5's in-crate exact `frem` is what keeps `%` off
   `fmod`. The first libm function is a differential-testing event, not a casual addition.
5. **NaN payload policy — [HOLE-10], the spec is silent and ch05 R17 makes it observable.** ch03 R13(c) fixes the *order* of `op`
   applications but not the *bits*, and aarch64 and x86-64 propagate payloads by different rules. *What M1 implements:* an operation
   whose result is NaN yields the **canonical quiet NaN** — sign 0, exponent all ones, quiet bit set, payload zero. This is a
   deliberate departure from 754's *recommendation* to propagate an input payload; it is the cheapest policy to implement
   identically on both targets, it makes byte comparison of outputs total, and v0.1 cannot observe a payload (floats are not
   formatted). Owner **Q2**: it constrains the backend and cannot change later without invalidating every recorded oracle output.
6. **`@fastmath` is a per-instruction mask** (`relax: u8` over `{reassoc, contract, nsz, finite, recip}`) and the interpreter
   **ignores it**, always computing the strict result. ch03 R8 *permits* but never *requires* relaxation — which is exactly what
   `fastmath-scope-ends-run-ok` checks: only the value **after** the block is pinned — and ch05 R17 exempts `@fastmath` from
   bit-for-bit agreement anyway.

### 5.7 `reduce` as the normative tree

The interpreter executes §3.9's expansion literally, with `B = 256`, `L = 8` read from the instruction's operands, never from the
host's vector width. Four properties are asserted by unit test beyond the corpus:

- shape is a pure function of `(n, B, L)` — a table of 0..1024 tree shapes is generated and hashed, and the hash is checked in;
- it equals the serial left fold **only** for `n <= 3` (ch03 R11's own claim — a test that would catch an accidental left fold);
- no identity padding: an empty lane is skipped, not fed to `op` (R13(a)), verified by an `op` that counts its calls;
- `op` is called with the lower-numbered lane as the **left** operand, verified by a non-commutative `op` (subtraction — which is
  exactly what `reduce-n7/n8/n9/n257` use, and why their expected values distinguish the tree from a fold: `83.0` vs `-125.0` at
  n=7).

### 5.8 The std surface: how stubs get behaviour

`std/*.fors` is real Fors source with **stub bodies** (`{}`) carrying the signatures, the linearity `impl`s, the contracts and the
module `needs`. Three mechanisms, in this order of preference.

**1. Written in Fors, interpreted like any other code** — the default, and the reason it is the default: the less of std that is
intrinsic, the more of std the oracle actually tests. Everything that is pure data manipulation: `Vec`, `Buffer`,
`Str.len`/`at`/`slice` with UTF-8 boundary checking, `Option`, `Slice`, `Map`, the `Iterator` provided methods, `rand.Pcg` (a PCG
step is ~4 integer ops), `Layout`. These need nothing beyond §5.1-§5.7.

**2. `intrinsic` ops from a closed table** for what Fors cannot express — raw allocation, raw byte moves, and the host calls:

| Intrinsic | Signature (abstract) | Used by | Host effect | comptime |
|---|---|---|---|---|
| `@alloc` | `(size, align) -> rawptr raises` | `mem.PageAllocator`, `mem.Heap` | new `Alloc{kind: Heap}` | Allowed |
| `@free` | `(rawptr, size, align)` | ditto | `AllocState::Freed` | Allowed |
| `@memcpy` / `@memset` | `(dst, src, n)` / `(dst, b, n)` | `Vec.grow`, `copy_from` | byte + init-bit + provenance copy | Allowed |
| `@size_of` / `@align_of` | `[T]() -> usize` | `Layout.of` | from D12, in `Target` width | Allowed |
| `@input_read` | `(path: Str) -> Str` | `fs.read_to_string` | the declared-inputs map, never a descriptor | **Allowed; Forbidden at run time** |
| `@fd_write` | `(fd: i32, bytes) -> isize` | `io`'s five writers and flush | `write(2)` | Forbidden |
| `@clock_mono` / `@clock_wall` | `() -> i64` | `time.Clock` | `clock_gettime` | Forbidden |
| `@entropy` | `(inout Slice[u8])` | `rand.Rng` | host entropy | Forbidden |
| `@exit` | `(i32) -> never` | entry shim | terminate | Forbidden |

Ten intrinsics, each a row in `fors-interp::intrinsic.rs` with that explicit `comptime` column — which is how ch04 R12's *"no
capability value, clock, RNG, env read, or ambient I/O"* becomes a mechanical check instead of a review promise. `@input_read` is
the inverse, forbidden at run time: ch10 R42 makes `fs.read_to_string` comptime-only and total and ch04 R13 makes its bytes a
content-hashed build-graph edge, so it is neither a syscall nor an error value. Without a row for it the closed table cannot express
two of F9's five gate tests.

**3. Interpreter-resident state, for the entry shim only**: the initial `fd` and terminal-detection result in each stream, `SIGPIPE`
→ `SIG_IGN`, and the construction of the root-capability values. This is *not Fors source* (ch04 R7: *"only the runtime entry shim,
which is not Fors source, creates the values it passes to `main`"*), so it is the one place the interpreter legitimately fabricates
a value.

**How a std stub gets a body.** `std/io.fors` declares `Stdout.write_line` and its four siblings as `{}` — stubs that, interpreted
literally, print nothing, which would fail all 37 `run-ok` tests. Mechanism 1 is the answer and **F1 owns it**: F1 writes the five
`write_*`, `check` and `clear_error` bodies in Fors over `@fd_write`, with the 8192-byte buffer and the `latched: Option[Error]`
flag as ordinary fields of `io.Stdout` (they already are). ch10 R39's latching and R40's buffering are then Fors code the oracle
tests like any other, and mechanism 3 shrinks to the initial field values. The rule generalises: **no increment may make a std
method interpreter-resident without adding a row to the intrinsic table.**

**What the 64 tests require of the host is startlingly small.** Only `@fd_write`, `@clock_mono`, `@alloc`/`@free` and `@exit` are
reached. `fs-name-dotdot-invalid-run-ok` issues no syscall at all — ch10 R41 raises `Error.invalid_name` **before** one — and
`capability-value-from-narrowing-accepted-run-ok` needs a `net.Net` value only to *exist*. No test reads a file, opens a socket,
spawns a process or reads the environment, so `fs`, `net`, `proc`, `env` and `gpu` need only their types, their name validation and
their error enums.

### 5.9 Capabilities at run time

Root-capability values are `Alloc { kind: Capability }` objects carrying a host handle, created **only** by the entry shim, one per
`main` parameter, by the nominal type ch04 R8/R21 fixes. Three run-time enforcements: **no FMIR op constructs one** (`agg_new` on a
root-capability type is a verifier rejection, not a run-time check — ch04 R7 is static and this is the backstop); **at most one live
value per capability type**, and per process for `mem.Heap` (ch10 R17, ch01 R15a), asserted; and **comptime mode starts with an
empty capability table**, where every intrinsic marked `comptime: Forbidden` raises a *build error naming the declaration*, not a
trap (ch04 R12; `comptime-clock-read-rejected`).

## 6. Comptime mode

One engine (PLAN R8, ch04 R11): the same interpreter with a different `Env`.

| Aspect | Run mode | Comptime mode |
|---|---|---|
| Capability table | 12 root values from the shim | **empty** |
| Intrinsics | all 10 except `@input_read` | only those marked `Allowed`: `@alloc`, `@free`, `@memcpy`, `@memset`, `@size_of`, `@align_of`, `@input_read` |
| Declared inputs | n/a | `inputs { "path", … }` (ch04 R13) resolved to content hashes **before** evaluation; `@input_read` reads only that map |
| Step budget | none | charged per instruction; `COMPTIME_STEP_BUDGET` |
| Alloc budget | host | charged per allocated byte; `COMPTIME_ALLOC_BUDGET` |
| Address observation | permitted | tracked: any `ptr_to_int`, cross-allocation pointer compare or reachable `rawptr` sets `observed_address = true`. The *value* observed is **synthetic and deterministic** — `(AllocId << 32) \| offset`, never a host address — because ch04 R12 requires determinism while R15 makes observation only a bar to *tier-up* |
| Result | none | a **content-addressed constant** |

**Budgets are deterministic counters, never wall time**: a wall-clock budget would make the build non-reproducible, contradicting
ch04 R12. Step charging is **per instruction** — `compiler-architecture.md` leaves the granularity as one of Marc's named lines
(`budget.rs::charge()`), and it is the only one that bounds a pathological straight-line body. Cost is one `sub`+`jz` per dispatch,
amortised by charging a block's instruction count once at block entry: per-instruction accounting with per-block checking, exact
because a block is straight-line.

**Recommended defaults** (ch04 R14 leaves them to measurement; Open question 1 there):

| Constant | Recommended | Derivation |
|---|---|---|
| `COMPTIME_STEP_BUDGET` | `2^20` = 1,048,576 steps | ≈35 ms at the §10 speed target — one runaway declaration cannot dominate a cold build |
| `COMPTIME_STEP_BUDGET_INCR` | `2^17` = 131,072 steps | ≈4.4 ms; a single-token edit must fit inside the 50 ms p95 with room for the other seven phases. Exceeding it is a *"comptime too expensive for the incremental path"* diagnostic, not a build failure |
| `COMPTIME_ALLOC_BUDGET` | 64 MiB | large enough for a generated table, small enough to fail fast |
| `COMPTIME_BUILD_STEP_BUDGET` | `2^28` ≈ 2.7 × 10⁸ steps | ch04 R14 charges **per evaluation**, so 200 declarations each at `2^20` is 2 × 10⁸ steps ≈ 7 s — seven times the 1 s allowance §10.1 derives. A per-declaration cap is not a build cap; this is the build cap, and exceeding it is a build error naming the *most expensive* declaration. Not in ch04 — owner Q6 |

**Observability.** A comptime evaluation observes exactly its arguments, its declared inputs' bytes and `@size_of`/`@align_of` — not
allocation addresses (opaque `AllocId`s; observing one sets the tier-up bar of ch04 R15), not the iteration order of any std
container (ch10 R37), not anything about the host.

**Content-addressing.** The result is a `ConstPool` row keyed `blake3(target_hash ‖ decl.sig_hash ‖ fmir.fingerprint ‖
canonical_encoding(arguments) ‖ Σ input_content_hashes)`. `target_hash` covers `Target` (§5.1) and Q1's layout-rule version: without
it a memo entry computed for one pointer width or field ordering would be reused for another, since `@size_of` and every `usize`
value are target-dependent. The encoding is `fors-fmir`'s, so a comptime constant is bit-identical across machines, which is what
makes it a legitimate build-graph input — and the memo is what keeps `COMPTIME_STEP_BUDGET` affordable, since a declaration whose
fingerprint is unchanged is never re-evaluated.

**Tier-up (ch04 R15, PLAN R8)** is computed in M1 and consumed in M2+: a body may tier up iff `observed_address == false` over its
whole transitive comptime call graph. M1 records the flag and `address_observation_blocks_tierup` asserts a pointer-to-integer cast
marks a body ineligible.

## 7. Oracle mode

### 7.1 What is compared

One run produces an **`OracleRecord`**, the complete observable behaviour:

```rust
pub struct OracleRecord {
    pub exit: Exit,                 // Normal(0|1|2) | Trap{kind, site_digest} | Ub{class, site_digest}
    pub stdout: Vec<u8>,            // exact bytes
    pub stderr: Vec<u8>,            // exact bytes
    pub heap_digest: Option<u128>,  // blake3 over live allocations at exit, canonical order
    pub steps: u64,                 // NOT compared; recorded for cost regression
}
```

- `exit` carries the trap **kind** and a **site digest** `blake3(decl key ‖ file ‖ line ‖ col ‖ kind)` — the only form of ch05 R17's
  *"which trap site fires"* that survives two different code generators.
- `stdout`/`stderr` compare as **bytes**, which is what `run-ok`'s `detail` and `run-error`'s stderr line already are.
- `heap_digest` is **opt-in** (`--oracle-heap`): live allocations in creation order, each hashed over bytes **masked by init bits**,
  provenance and addresses excluded. Masking is essential — ch10 R13 lets `alloc` return uninitialised bytes, so unmasked padding
  would make two correct engines disagree. Off by default for that reason.
- `steps` is never compared across engines (a backend has none); it is compared across runs of the same engine as a cost-regression
  gate.

### 7.2 Determinism requirements

For the record to be a valid oracle the interpreter must be a function of (FMIR, declared inputs, capability responses):

- no address is ever observable (allocation ids are dense and deterministic, assigned in creation order);
- no hash-container iteration reaches an output — `fors-interp` uses sorted vectors or insertion-ordered maps on every path that can
  affect a record, asserted by a CI grep against `HashMap`, `HashSet` and `RandomState` in `src/` (the same discipline `fors-fir`
  already applies with its own cons table);
- nothing reads the host's pointer width, endianness, locale, environment or `std::time`: the only clock is
  `@clock_mono`/`@clock_wall`, and `Target` (§5.1) supplies the widths;
- `@entropy` and both clocks are **recorded and replayable**: `--oracle-record` writes a response log, `--oracle-replay` feeds it
  back, so `time-now-is-monotonic-run-ok` is deterministic under replay while still being a real clock test in a live run;
- the step counter is deterministic, which makes it a cheap divergence *detector*: two runs of the same FMIR that differ in `steps`
  have a nondeterminism bug even if their outputs match.

`--serial-elide` (ch05 R10/R17, mandatory) is, in M1, the *only* execution mode for a `spawn` region — so the M1 statement is simply
that serial elision is trivially bit-exact, and the real test arrives with M3's scheduler.

### 7.2a What the conformance runner compares — and three tests that need it pinned

`tests/conformance/README.md` defines the four runtime expectation kinds in one sentence each, and three of the 64 tests cannot pass
under the literal reading. F10 owns the runner, so this document owns the resolution:

| Kind | Exit | `Stdout` | `Stderr` |
|---|---|---|---|
| `run-ok` | 0 | bytes equal `detail` (`(no output)` = empty) | not compared |
| `run-error` | 1 | not compared | **the last line** equals `detail` |
| `run-error` + `status: 2` | 2 | stdout descriptor closed before `main` | not compared |
| `trap` | signal status (SIGTRAP), never 0/1/2 | not compared | the **last** line is the interpreter's `trap: <kind> at <file>:<L>:<C>`, whose `<kind>` equals `detail`; the lines before it are the program's own `Stderr` bytes and a test MAY assert their content |

Why "last line" and not "equals", for `run-error`: `02-failure/main-raises-after-defer-run-error` has `defer
err.write_line("deferred");` in `main`, and ch01 R23e runs it **before** ch02 R17's line, so the process's stderr is
`deferred\nerror: main.Error.boom\n` while the directive's `detail` is only the second line. Under "stderr MUST equal detail +
newline" the test fails against correct behaviour. The same shape makes `trap-runs-no-defer` and `10-std/defer-not-run-on-trap`
work: they assert that `cleanup` is **absent** from the lines before the trap line, which is exactly what ch10 R40 says is
observable (`Stderr` is unbuffered, `Stdout` may lose buffered bytes).

Two consequences worth stating rather than discovering. **The trap line is part of ch05 R17's byte comparison**: its format is fixed
here and the backends' trap handler must emit the same bytes from ch02 R6's side table, which makes a **backtrace on the trap path
illegal for any program in the differential corpus** — `compiler-architecture.md` §7 promises an FP-walking backtrace printer, and a
host-dependent backtrace would make interp and backend disagree on every trap test (owner Q7). And the runner's line-splitting lives
in the *test harness*, never in `OracleRecord`, which stays an exact byte image.

### 7.3 Minimising a mismatch

Three fully automatic stages, following `compiler-architecture.md` §8's "SoA-level delta-debugging reduction": **declaration-level
ddmin** over the build (cheap, because FMIR is per-declaration and content-hashed); **instruction-level ddmin** within the
survivors, deleting instructions and whole blocks, repairing with `unreachable`, re-verifying and keeping the mismatch — the
verifier is what makes this safe, since a reduction that produces invalid FMIR is discarded rather than executed; and **operand
narrowing**, replacing constants with the smallest value that preserves the mismatch. Exit criterion, borrowed from
`compiler-architecture.md` C3: a seeded miscompile reduces to **under 30 FMIR instructions**.

## 8. Rule-to-mechanism table

Every **dynamic-semantics MUST** rule of ch01, ch02, ch03 and ch05, plus the run-time rules of ch04 and ch10. "Corpus" names real
files under `tests/conformance/`; **GAP** means no runtime test exists.

| Rule | FMIR construct | Interpreter mechanism | Corpus |
|---|---|---|---|
| 01 R2, R4a | `move_from` / `copy_from` / `init`; implicit receiver move is `move_from` | per-place `live` bit; `ub: use-after-move` | static (I8); `10-std/vec-deinit-empty-nonempty-trap` exercises the lowering |
| 01 R4 | `sink` param obligation record on the frame | scope-exit discharge check | static |
| 01 R15/R15a | `region_enter`/`region_exit` with `ScopeRow.arena` | one live `ArenaVal` per brand per block instance, asserted | `01-ownership/arena-generation-trap` |
| 01 R17 | `arena_deref` (no `may_elide` bit) | generation compare → **trap `arena-generation`** | `01-ownership/arena-generation-trap` |
| 01 R18 | `free` carries `AllocatorId` | `AllocKind::Heap(id)` compare → `ub: allocator-mismatch` | static (`10-std/free-wrong-brand-rejected`); **GAP** at run time |
| 01 R19-R19d | `flags.SCOPED` + `SourcePool` | escape detection (§5.2) | static; **GAP** at run time |
| 01 R7 | `borrow` vs `borrow_mut`/`borrow_out` items on the borrow stack | SharedRO groups: two overlapping `let` accesses are ACCEPTED (§5.2) | **GAP** at run time; `ub_aliasing_accepts_two_let_borrows` (F6 unit) |
| 01 R22d | `Discharge` per exit edge | undischarged → `ub: linear-leak` | **GAP** — no corpus test reaches a leak at run time (`vec-deinit-empty-nonempty-trap` traps on a *contract*, not on a leak); `ub_linear_leak_is_not_a_trap` is a hand-written FMIR test |
| 01 R23a | pending bodies inlined on each exit edge, reverse `stmt_order` | block order; nothing dynamic | `01-ownership/defer-reverse-order-run-ok`, `defer-runs-on-return-run-ok`, `defer-nested-scope-order-run-ok`, `defer-result-evaluated-first-run-ok` |
| 01 R23b | `ErrDefer` rows emitted on error edges only | `try_br.err` / `raise` edges | `01-ownership/errdefer-skipped-on-return-run-ok`, `02-failure/handler-makes-normal-exit` |
| 01 R23e | loop-body scope exits each iteration | scope tree | `01-ownership/defer-per-iteration-run-ok` |
| 01 R23f | `trap` terminator has no successors | nothing to run | `02-failure/trap-runs-no-defer`, `10-std/defer-not-run-on-trap` |
| 02 R1-R3 | `try_br`; one `ErrorFrom` call per error edge | tag test | `10-std/try-for-each-error-propagates-run-ok` |
| 02 R4 | — | **not representable above LIR**; the interpreter cannot be this rule's oracle | **GAP by construction** (backend-only, M2) |
| 02 R5 | handler inline; handler edges typed normal/error | — | `02-failure/handler-makes-normal-exit` |
| 02 R6, R7 | `trap{kind, site}` terminator with no successors; `SitePool` | abort, no defers, no flush, signal exit (§5.3, §7.2a) | `02-failure/{trap-bounds,trap-div-zero,trap-overflow,trap-shift,trap-runs-no-defer}`, `10-std/{buffer-index-past-len-trap,defer-not-run-on-trap}` |
| 02 R9 | `check_pre`/`post`/`inv` instructions | evaluate; false → **trap `contract`** | `02-failure/contract-runtime-violation-trap`, `10-std/rand-bounded-zero-trap`, `time-since-reversed-trap`, `vec-deinit-empty-nonempty-trap` |
| 02 R10 | `policy` field from the module header only | interpreter has no `-O` input | `02-failure/contract-off-no-check-run-ok` |
| 02 R11 | no check-elision bit in FMIR | n/a (OIR's rule) | **GAP** (M5) |
| 02 R15 | `TrapKind` enum, exactly 8 | `KINDS: [&str; 8]` asserted against every `trap` test's `detail` | all 19 `trap` tests; all 8 kinds are covered at least once |
| 02 R16 | normal vs error edge label | edge kind | `02-failure/handler-makes-normal-exit` |
| 02 R17 | entry shim sequence (§5.4) + `render.rs` | defers → flush → one stderr line → status 1 | `02-failure/main-raises-{unit-variant,payload,nested-payload,std-error,flushes-stdout,after-defer}-run-error`, `10-std/main-raises-exit-status-one-run-error` |
| 03 R1 | scalar types ≤ 64 bits | `Slot.bits` | `03-numerics/int-fixed-width-i64-accepted-run-ok` |
| 03 R2 | `add`/`sub`/`mul`/`div`/`rem`/`shl`/`shr` trapping | 128-bit compute + range check | `overflow-trap-{add,sub,mul}`, `div-zero-trap`, `shift-width-trap` |
| 03 R3 | no flag reaches the interpreter | no `-O` input | covered by R2's tests (no mode varies) |
| 03 R4 | `wrap_*`/`sat_*`/`unchecked_*` opcodes | truncate / clamp / wrap+UB report | `wrap-add-no-trap-run-ok`, `sat-add-saturates-run-ok` |
| 03 R6 | `conv_checked`/`conv_wrap`/`conv_sat`/`conv_trunc` | exact-representability test → **trap `checked-conversion`** | `checked-as-exact-accepted-run-ok`, `checked-as-lossy-trap`, `wrap-as-truncates-run-ok`, `sat-as-clamps-run-ok`, `trunc-as-truncates-run-ok` |
| 03 R7 | no `fma` opcode; fixed rounding mode | CI grep for `mul_add` | `float-default-no-fma-run-ok` |
| 03 R8 | per-instruction `relax` mask | ignored; strict always | `fastmath-scope-ends-run-ok` |
| 03 R9 | `comptime_int` never reaches FMIR | lowering asserts it | `comptime-int-explicit-conversion-accepted` |
| 03 R10 | — | single-threaded in M1 | **GAP** (M3) |
| 03 R11, R13 | `reduce_tree{b:256, l:8}` + §3.9 expansion | scalar emulation of 8 logical lanes | `reduce-n1`, `-n7`, `-n8`, `-n9`, `-n257-shape-run-ok` |
| 03 R11a | `identity` operand | `n==0` → identity, or **trap `empty-reduce`** | `reduce-n0-with-identity-run-ok`, `reduce-n0-without-identity-trap`, `reduce-identity-no-effect-n3-run-ok` |
| 03 R12 | shape fixed in FMIR before parallel lowering | see **[HOLE-3]** | `reduce-n257-shape-run-ok` |
| 03 R15 | no auto-reduce pass exists | n/a | `plain-for-accumulator-accepted-run-ok` |
| 03 R16-R18 | mono-vs-witness decision on each call | `call_direct` vs `call_witness` | **GAP**; see **[HOLE-5]** |
| 04 R7, R21 | `AllocKind::Capability`, shim-only construction | `agg_new` on a root type is a verifier error | `04-authority/capability-value-from-narrowing-accepted-run-ok`, `main-signature-correct-accepted-run-ok`, `needs-declared-accepted-run-ok` |
| 04 R11, R12 | one engine; `comptime` column on the intrinsic table | empty capability table | `comptime-clock-read-rejected`, `sealed-op-at-comptime-rejected` |
| 04 R13 | declared-inputs map | `fs.read_to_string` reads only from it | `comptime-file-read-declared-accepted`, `-undeclared-rejected` |
| 04 R14 | step/alloc counters | budget exceeded → build error naming the declaration | `comptime-budget-exceeded-rejected` |
| 04 R15 | `observed_address` flag | tracked, recorded, unused in M1 | **GAP** (M2) |
| 05 R3 | FMIR is the interpreter's sole input | `fors-interp` cannot see the CST (CI grep) | **GAP** — no ch05 corpus directory exists at all |
| 05 R5 | `AliasSeed` pool (§3.4a) | carried, never computed; brand survives as IR metadata | **GAP** (M5); `alias_seed_present_on_every_memory_op` (F0 unit) |
| 05 R6, R6a | `ValRow.flags.SECRET`, `ValRow.ct` non-optional | verifier rejects a row without them; `fors-lower` propagates on every result (§3.11) | **GAP** — ch05 names `secret_propagates`, `ir_verify_secret_fields` etc. but `tests/conformance/` has **no `05-*` directory** |
| 05 R6b | rejection pass in `fors-fmir::verify` (§3.11) | source diagnostic for a branch, index, trapping op, contract, or `raise` condition on secret | **GAP**; `secret_trapping_op_rejected`, `ct_no_branch_or_index_on_secret`, `secret_raise_condition_rejected` (F0) |
| 05 R9, R10, R11 | `spawn` with typed capture list; `sync`; region dominance | verified; executed serially (= serial elision) | **GAP** (M3) |
| 05 R12 | `tile.*` opcodes absent; verifier rejects them downstream | — | **GAP** (M6) |
| 05 R17 | `OracleRecord` (§7) | byte comparison + trap site digest | **GAP** — `backend_bitforbit_agreement` has no file; it is M2's gate |
| 10 R11c | `deinit_empty`'s `pre self.len() == 0` | `check_pre` → **trap `contract`** | `10-std/vec-deinit-empty-nonempty-trap` |
| 10 R13 | `@size_of`/`@align_of` intrinsics | from D12, in `Target` width | **GAP**; see **[HOLE-6]** |
| 10 R42, 04 R13 | `@input_read` intrinsic, comptime-only | declared-inputs map, no descriptor | `04-authority/comptime-file-read-{declared-accepted,undeclared-rejected}` |
| 10 R17 | one live `mem.Heap`, brand named by the parameter | asserted | `10-std/vec-deinit-empty-nonempty-trap` |
| 10 R26 | `Str` is bytes; UTF-8 boundary check raises (data, not a trap) | written in Fors | `str-index-is-bytes-run-ok`, `str-slice-non-boundary-raises-run-ok` |
| 10 R23 | `Buffer` index past `len` | `index` → **trap `bounds`** | `buffer-index-past-len-trap` |
| 10 R32-R35 | provided methods on `Iterator`; concrete adaptor structs | ordinary Fors code | `try-for-each-error-propagates-run-ok` |
| 10 R39 | five total latching writers; `check` surfaces | sticky `latched` flag in the shim's stream state | `write-line-without-question-accepted-run-ok`, `sigpipe-ignored-write-latches-run-ok` |
| 10 R39, R40(a)-(c) | the five `write_*` written in Fors over `@fd_write` (§5.8); shim flush on normal return; nothing on trap | buffered bytes deterministically dropped on trap | `10-std/defer-not-run-on-trap` |
| 10 R40(d) | exit-status table 0/1/2 | shim | `02-failure/main-returns-latched-stdout-exit-2`, every `run-ok` (status 0), every `run-error` (status 1) |
| 10 R41 | name validation **before** any syscall | pure check in Fors | `fs-name-dotdot-invalid-run-ok` |
| 10 R45 | `Instant.since`'s `pre` | `check_pre` → **trap `contract`**; `@clock_mono` | `time-now-is-monotonic-run-ok`, `time-since-reversed-trap` |
| 10 R47 | `Pcg.bounded`'s `pre n > 0` | `check_pre` → **trap `contract`** | `rand-bounded-zero-trap` |
| 10 R55 | std introduces no trap of its own | the 8-kind assertion | all 19 `trap` tests |

### 8.1 Corpus gaps, ranked by how much they can hurt

1. **There is no `05-ir-contract` conformance directory.** ch05 lists 22 conformance tests by name (`ir_verify_secret_fields`,
   `secret_propagates`, `detach_capture_explicit`, `serial_elision_always_legal`, `tile_ops_fmir_only`,
   `backend_bitforbit_agreement`, …) and **none exists as a file**; `tests/conformance/` holds `01`, `02`, `03`, `04`, `07`, `08`,
   `09`, `10` only. Every ch05 rule above is therefore corpus-unverified. F0 writes the verifier-level subset as `fors-fmir` unit
   tests **and** as `tests/conformance/05-ir/` (owner Q5).
2. **No run test exercises `i64::MIN / -1`, `% 0`, or a `wrap_`/`sat_` shift**, so [HOLE-8] and [HOLE-9] are undecidable from the
   corpus.
3. **No run test distinguishes `Stdout` line-buffering from block-buffering.** ch10 R40 makes the mode depend on terminal detection;
   a wrong choice is invisible to all 64 tests and very visible to a user.
4. **Five of the twelve root capabilities never appear in a run test**: `io.Stdin`, `proc.Exec`, `env.Env`, `env.Args`, `gpu.Device`
   (and `rand.Rng` — `rand-bounded-zero-trap` uses the capability-free `rand.Pcg`).
5. **No run test covers ch03 R13(b)'s `-0.0` or R13(c)'s NaN in `reduce`**, and [HOLE-10] makes NaN bits an unpinned observable.
6. **No run test covers a live `Ref` dereference after `reset` + realloc** — only the trapping case, so a generation check that
   always trapped would pass.
7. **No run test reaches a linear leak or an aliasing violation**: both are `ub:` classes with no corpus file, which is why risk
   R5's hand-written negative corpus is not optional.
8. **Two corpus tests appear self-inconsistent**, and one gates F2 — owner Q8 (§11.1).

## 9. Increments F0..F10

Model tier per the owner's rule: **opus** where a wrong answer is expensive (data model, memory model, float semantics, the
flow-dependent increments), **sonnet** for bounded work against a named gate, **haiku** for mechanical sweeps. Every corpus name
below is a real file under `tests/conformance/`.

**F0 — `fors-fmir` (opus for `inst.rs`/`verify.rs`, sonnet for pools and dump; ~2.2k lines). CHECKER DEPENDENCY: none — the one
increment that can be handed to an implementer today.** Builds §3.1's pools, the 71 opcodes,
`ScopePool`/`PlacePool`/`RegionPool`/`SitePool`/`AliasSeed` (§3.4a), canonical encoding + `fmir_hash`, the textual dump and its
parser, the verifier (well-typedness, one terminator per block, `secret`/`ct` on every row, R6a/R6b (§3.11), `tile.*` absent,
`spawn` captures present, scoped/linear records well-formed), and risk R5's negative FMIR corpus. GATE: `encode_decode_roundtrip`
over 10k generated declarations; `fmir_hash` invariant under block renumbering, changed by any operand edit;
`verify_rejects_{missing_secret_field,missing_ct_region,detach_without_captures,tile_op,two_terminators}`;
`alias_seed_present_on_every_memory_op`, `arena_brand_survives_lowering`, `split_at_halves_get_distinct_seeds`; ch05's
`secret_propagates`, `secret_trapping_op_rejected`, `ct_no_branch_or_index_on_secret`, `secret_raise_condition_rejected`,
`declassify_requires_unsafe`; a CI grep that `crates/fors-fmir/src` mentions neither `fors_check` nor `fors_syntax`. COUNTERS: FMIR
bytes per source byte (§10.3); verifier steps per instruction, O(1) amortised.

**F1 — lowering + interpreter core (opus for `value.rs`/`arith.rs`, sonnet for the lowering walk; ~2.5k lines). CHECKER DEPENDENCY:
I3 + [HOLE-4]'s `BodyFacts` + **I4** (every gate test calls `out.write_line(...)`, §4.2); not I5-I8.** Builds the `BodyFacts`-driven
lowering of non-generic bodies, `Slot`/`Alloc`, `Target`, the dispatch loop, trapping and explicit arithmetic, conversions,
`if`/`while`/`for` over ranges, arrays and slices, direct calls, the entry shim — and the **Fors bodies** of `io.Stdout`'s five
`write_*`, `check`, `clear_error` over `@fd_write` (§5.8), without which every `run-ok` test prints nothing. GATE (19):
`03-numerics/{overflow-trap-add,overflow-trap-sub,overflow-trap-mul,div-zero-trap,shift-width-trap,checked-as-exact-accepted-run-ok,checked-as-lossy-trap,wrap-add-no-trap-run-ok,sat-add-saturates-run-ok,wrap-as-truncates-run-ok,sat-as-clamps-run-ok,trunc-as-truncates-run-ok,implicit-widen-with-as-accepted,int-fixed-width-i64-accepted-run-ok,comptime-int-explicit-conversion-accepted,float-default-no-fma-run-ok,fastmath-scope-ends-run-ok,plain-for-accumulator-accepted-run-ok}`,
`02-failure/trap-overflow`; plus `interp_has_no_opt_level_input`, `frem_matches_reference_over_10e6_pairs`, and the
`mul_add`/`usize` greps. COUNTERS: steps/second (§10.1), steps per test, frame-arena bytes.

**F2 — contracts, entry shim, exit statuses, `Stderr` (sonnet; ~600 lines). CHECKER DEPENDENCY: I3 + I4; `fors-lower` reads the
module `contracts:` line itself until I10 lands D10 (E11).** Builds `check_pre`/`post`/`inv` with the module policy, unbuffered
`Stderr`, `SIGPIPE` → `SIG_IGN`, the 0/1/2 exit table, latching and `check`. GATE (7):
`02-failure/{contract-runtime-violation-trap,contract-off-no-check-run-ok,main-returns-latched-stdout-exit-2,trap-bounds,trap-div-zero,trap-shift}`,
`10-std/write-line-without-question-accepted-run-ok`. `10-std/sigpipe-ignored-write-latches-run-ok` is **held out** pending owner
Q8.

**F3 — `raises`/`?`/`else` and `render` (opus for `render.rs`, sonnet for the edges; ~700 lines). CHECKER DEPENDENCY: I10 (ch02
R1-R5), I4 for a trait-method callee.** Builds `try_br`, error edges, at most one `ErrorFrom` per edge, the handler form, and ch02
R17's five-step exit sequence with the full `render` clause list. GATE (7):
`02-failure/{main-raises-unit-variant-run-error,main-raises-payload-run-error,main-raises-nested-payload-run-error,main-raises-std-error-run-error,main-raises-flushes-stdout-run-error,handler-makes-normal-exit}`,
`10-std/main-raises-exit-status-one-run-error`.

**F4 — `defer`/`errdefer` (opus; ~500 lines). CHECKER DEPENDENCY: I8b (D7), an increment that does not yet exist ([HOLE-11]); also
F3.** Builds `DeferPool`, exit-edge inlining in reverse `stmt_order` interleaved across kinds, the R23d place→strongest-access
summary, and the verifier check that every exit edge carries exactly the right multiset. The **interpreter half** (block emission,
ordering, `trap` having no successor) runs on hand-written FMIR fixtures and is not blocked; only the lowering half is. GATE (9):
`01-ownership/{defer-reverse-order-run-ok,defer-runs-on-return-run-ok,defer-per-iteration-run-ok,defer-nested-scope-order-run-ok,defer-result-evaluated-first-run-ok,errdefer-skipped-on-return-run-ok}`,
`02-failure/{main-raises-after-defer-run-error,trap-runs-no-defer}`, `10-std/defer-not-run-on-trap`. COUNTERS: inlined-body growth
as a ratio of body size (risk R6).

**F5 — `reduce` (opus for `reduce.rs`; ~400 lines). CHECKER DEPENDENCY: I3 — but [HOLE-7]: no increment claims ch03 R11's typing, so
F5 hard-codes it.** Builds `reduce_tree`, §3.9's expansion, the comptime-`n` unrolled form and the agreement assertion. GATE (8):
`03-numerics/{reduce-n1-shape-run-ok,reduce-n7-shape-run-ok,reduce-n8-shape-run-ok,reduce-n9-shape-run-ok,reduce-n257-shape-run-ok,reduce-n0-with-identity-run-ok,reduce-n0-without-identity-trap,reduce-identity-no-effect-n3-run-ok}`;
plus `reduce_shape_table_hash` over n ∈ 0..1024, `reduce_equals_left_fold_only_below_4`, `reduce_no_identity_padding`.

**F6 — arenas, `Own`, allocators, linear obligations (opus; ~900 lines). CHECKER DEPENDENCY: I4 (the `Index` impl on `Arena`,
method-on-bound), I5 (brands), I8b (D8, [HOLE-11]), D12 ([HOLE-6]).** Builds `ArenaVal`/`RefVal`, generation checks, `arena_reset`,
`@alloc`/`@free`, `AllocKind`, the obligation/discharge machinery and §5.2's `ub:` reports. GATE (1 corpus test):
`01-ownership/arena-generation-trap`; plus `ub_use_after_free`, `ub_uninit_read_through_out`, `ub_allocator_mismatch`,
`ub_linear_leak_is_not_a_trap`, `arena_gen_wraps_safely` ([HOLE-2]), and the two **positive** cases
`ub_aliasing_accepts_two_let_borrows`, `ub_aliasing_accepts_nested_let_under_let` (ch01 R7, E14).
`10-std/vec-deinit-empty-nonempty-trap` moves to **F7**: its `Vec.new`, `push` and `deinit_empty` bodies are F7's, and
`a.create(1)?` needs I4.

**F7 — std in Fors: containers, `Str`, iterators (sonnet, opus review of `Str`/UTF-8; ~800 lines of Fors, ~200 of interpreter).
CHECKER DEPENDENCY: I4 (provided methods), I6 (`I.Item`), I7 (`Option` patterns).** Builds real bodies for `Vec`, `Buffer`, `Str`,
`Slice`, `Option`, `mem.iter` and the `Iterator` provided methods the corpus needs. GATE (6):
`10-std/{str-index-is-bytes-run-ok,str-slice-non-boundary-raises-run-ok,buffer-index-past-len-trap,try-for-each-error-propagates-run-ok,vec-deinit-empty-nonempty-trap}`;
`03-numerics/reduce-n257-shape-run-ok` re-run over a `Vec`-backed slice.

**F8 — capability host surface (sonnet; ~500 lines). CHECKER DEPENDENCY: I10 (ch04 R7, R8).** Builds `time.Clock`, `rand.Pcg`/`Rng`,
`fs.Dir` name validation and error enums, `net.Net` as a value, the shim's construction of all twelve root values, and
`--oracle-record`/`--oracle-replay` for clocks and entropy. GATE (7):
`10-std/{time-now-is-monotonic-run-ok,time-since-reversed-trap,rand-bounded-zero-trap,fs-name-dotdot-invalid-run-ok}`,
`04-authority/{capability-value-from-narrowing-accepted-run-ok,main-signature-correct-accepted-run-ok,needs-declared-accepted-run-ok}`;
plus `fs_name_validation_issues_no_syscall` (an intrinsic counter).

**F9 — comptime mode (opus for `budget.rs`, sonnet for the rest; ~700 lines). CHECKER DEPENDENCY: I10 (ch04).** Builds the comptime
`Env`, the intrinsic `comptime` column, `@input_read` and declared-inputs resolution, step/alloc charging plus the build-wide cap,
synthetic deterministic addresses, `observed_address`, and the `target_hash`-keyed content-addressed memo. GATE (5, run through the
interpreter as a build step):
`04-authority/{comptime-budget-exceeded-rejected,comptime-clock-read-rejected,comptime-file-read-declared-accepted,comptime-file-read-undeclared-rejected,sealed-op-at-comptime-rejected}`;
plus `comptime_memo_is_content_addressed`, `comptime_result_identical_across_processes`, `address_observation_blocks_tierup`.
COUNTERS: steps and bytes per evaluation; memo hit rate on the 100k corpus.

**F10 — oracle mode, differential runner, reducer (opus for the reducer, sonnet for the runner; ~900 lines). CHECKER DEPENDENCY:
everything above.** Builds `OracleRecord`, the conformance runner of §7.2a, the three-stage minimiser, and the FMIR-level random
program generator of `compiler-architecture.md` §8. GATE: **all 64 runtime tests green**; `record_is_deterministic_over_100_runs`;
the reducer shrinks a seeded miscompile to **< 30 FMIR instructions**; 10⁵ generated programs with zero interpreter panics and zero
`ub:` reports (the generator is UB-free by construction, so any report is triaged, never waived). This is the M1 exit.

## 10. Performance and incrementality

### 10.1 Speed target, and why this number

**Target: 30 M FMIR steps/second in comptime mode, 8 M steps/second in Miri mode**, single P-core, measured by `fors-interp --stats`
on a fixed kernel.

Derivation, for a 100k-line comptime-heavy build: 100k lines ≈ 4,000 declarations at the corpus's ~25 lines each; allow comptime **≤
1 s of a cold build** (more would make it the dominant phase); 1 s × 30 M = 3 × 10⁷ steps for the whole build, so if 5% of
declarations (200) are comptime-heavy each gets ~1.5 × 10⁵ steps — a 128×128 integer table, or a parser over a 4 KiB embedded file —
which memoization then makes free on every rebuild. `COMPTIME_STEP_BUDGET = 2^20` is ~35 ms, well under that allowance, and
`COMPTIME_STEP_BUDGET_INCR = 2^17` ≈ 4.4 ms fits inside `compiler-architecture.md` §2's 50 ms p95 beside its 6 ms "FMIR build +
checks" line. (§6's `COMPTIME_BUILD_STEP_BUDGET` exists because 200 × 2^20 is 7× the 1 s allowance: a per-declaration cap is not a
build cap.)

30 M steps/s is ~33 ns per step, conservative for a switch-dispatch loop over a flat typed tape (3-10 ns is typical) — the margin
pays for §5.5's range checks and init-bit maintenance. The Miri figure is ~4× slower because every memory op touches the init
bitmap, the provenance map and the borrow stack. **Neither number is set by the corpus**: the largest of the 64 tests
(`reduce-n257`) is ~10⁴ steps, so all 64 interpret in well under a second and process overhead dominates. The target exists for
comptime and for F10's 10⁵-program differential runs.

### 10.2 Fingerprints and invalidation

`DeclFmir.fingerprint = blake3(canonical_encoding(pools))`. The query node set extends the type checker's §9.1 with three nodes:

| Query | Key | Output | Depends on |
|---|---|---|---|
| `fmir_of(k)` | `DeclKey` | `DeclFmir` | `check_body(k)`'s `BodyFacts`, `signature_of(k)`, `signature_of` of every callee, layout of every mentioned head |
| `fmir_fingerprint(k)` | `DeclKey` | `u128` | `fmir_of(k)` |
| `comptime_eval(k, args, inputs)` | content hash | `ConstId` | `fmir_of` of the transitive comptime call graph, input content hashes |

What invalidates what: a **body-only** edit changes `fmir_of(k)` and nothing else, because a caller references a callee by `DeclKey`
plus its *signature* hash, never its body; a **signature** edit invalidates `fmir_of` of every direct caller (their call
instructions carry argument conventions and the mono/witness decision); a **layout-affecting** edit (adding a field, reordering an
enum) invalidates `fmir_of` of every declaration mentioning the head — the one edit class where FMIR fans out further than type
checking does, and the reason D12 ([HOLE-6]) must be a *declared* algorithm; a **contract-policy** edit invalidates that module and
nothing outside it; a **comptime input file** edit invalidates only `comptime_eval` rows naming it, by ch04 R13's content-hashed
edge.

`check_output_identical_cold_vs_incremental` has an FMIR twin: `fmir_fingerprints_identical_cold_vs_incremental` over the same eight
edit classes the type checker's §9.2 enumerates.

### 10.3 Memory budgets

| Quantity | Budget | Basis |
|---|---|---|
| FMIR bytes per source byte | **≤ 12 B** | the checker's signatures measured ≤ 1.5 B/source byte; bodies are ~8× the content of signatures, and SoA rows are 12-16 B. At 100k lines ≈ 3 MB of source that is ≤ 36 MB resident — acceptable for a daemon. |
| Interpreter live state per run | **≤ 2 MiB** + the program's own allocations | frame arena + slot stack; the corpus's largest frame is `Array[f64, 257]` ≈ 2 KiB |
| `SitePool` | ≤ 8 B per trap site | `(span: u32, kind: u8, decl: u16, pad)` — ch02 R6's side table is the same data |
| Comptime memo | content-addressed, LRU-evictable | a memo miss is correct, just slow |

A CI gate records FMIR bytes/source byte at 12.5k, 25k, 50k, 100k and 200k lines and fails on a **slope** change, the same shape of
gate the type checker uses — a flat ratio is the claim, not a single number.

## 11. Open questions

### 11.1 Owner decisions (Marc)

| Q | Question and what it blocks | Recommendation |
|---|---|---|
| **Q1** | **Type layout — who defines it, and what is it?** ch09 delegates layout to ch05; ch05 does not define it, and `Layout.of[T]().size` is observable from a Fors program, so this is a language fact. Blocks F6, F7, D11, D12 — every allocation in `Vec`, `Own`, `Buffer`, and the mono-vs-witness rule. **[HOLE-6]** | A new normative section in ch05 with the thinnest honest content: fields in **declaration order** with natural alignment and no reordering (so `soa struct` and FFI stay predictable), `align ≤ MEM_MAX_ALIGN = 16`, enum discriminant the smallest unsigned type fitting the variant count, payload at the first suitably aligned offset. "Implementation-defined + opaque `Layout.of`" is tempting but breaks ch03 R16's *"scalar, ≤ 16 bytes"*, which is meaningless without a layout rule |
| **Q2** | **NaN payload policy.** ch03 R13(c) fixes the order of `op` applications, not the bits; aarch64 and x86-64 differ, and ch05 R17 makes it observable. Blocks nothing today and **everything after M2**, since every recorded oracle output is invalidated by a later change. **[HOLE-10]** | **Canonical quiet NaN** on every NaN-producing op (§5.6(5)). Cheapest to implement identically on both targets, makes R17's byte comparison total, and v0.1 cannot observe a payload (ch10 R10(f)). Leaving it target-defined would put a permanent hole in the differential tester |
| **Q3** | **Reword ch03 R12**, which as written — *"MUST lower to this explicit tree in FMIR"* — is unimplementable for a runtime-length input, and `reduce-n257-shape-run-ok` is one. **[HOLE-3]** | *"`reduce` MUST be given its final shape in FMIR, as a function of `(n, B, L)`, before parallel lowering; where `n` is comptime-known the tree MUST be explicit."* Keeps everything R12 buys (`--serial-elide` bit-exactness) and becomes true |
| **Q4** | **`i64::MIN / -1` and shift-count typing.** ch03 R2 lists "overflow, div-by-zero, shift-by-≥-width" and decides neither. Blocks F1. **[HOLE-8]**, **[HOLE-9]** | `MIN / -1` and `MIN % -1` trap **`overflow`** (the condition is representability, not a zero divisor); the shift count is `u32` by language rule, so the runtime condition is exactly `count >= width`. Two corpus tests are needed either way (§8.1 gap 2) |
| **Q5** | **May F0 add `tests/conformance/05-ir/`?** ch05 names 22 conformance tests and none exists as a file, so every ch05 rule in §8 is corpus-unverified — but adding them changes the counts the corpus README states (921 tests, 1010 files), and the corpus is ground truth | Yes, with the README's count line updated in the same commit. It is transcription plus the verifier, not design |
| **Q6** | **A build-wide comptime budget.** ch04 R14 charges per *evaluation*; §10.1 allows ~3 × 10⁷ steps for a whole cold build, but 200 declarations at `2^20` is 2 × 10⁸ | Add `COMPTIME_BUILD_STEP_BUDGET = 2^28` to ch04 R14 beside the two existing constants |
| **Q7** | **Backtraces on the trap path.** `compiler-architecture.md` §7 promises an FP-walking backtrace printer; ch05 R17 requires interp and both backends byte-identical "including which trap site fires", and a backtrace is host- and layout-dependent. Blocks M2's R17 gate | The trap handler prints exactly the one line §7.2a fixes; a backtrace is opt-in (`FORS_BACKTRACE=1`) and excluded from the differential corpus |
| **Q8** | **Two corpus tests that look self-inconsistent.** `10-std/sigpipe-ignored-write-latches-run-ok` applies `else \|e\| { }` to `Stdout.write_line`, which ch10 R39 declares total and ch02 R5 therefore forbids `else` on; and it expects exit 0 with `(no output)` where ch10 R40(d) makes a latched `Stdout` error exit 2. Blocks F2's eighth gate test | **LEFT OPEN.** Either the test wants the `status: 2` form or R39 wants a `raises` writer; either way it is a corpus edit, not an interpreter behaviour |

### 11.2 Engineering calls I made (no owner input needed)

| # | Call | Alternative rejected because |
|---|---|---|
| E1 | CFG + scope tree, not a structured tree or a bare CFG (§3.2) | a tree has no terminators for ch05 R10; a bare CFG loses the structure R10/R12 and ch01 R23a need |
| E2 | Three crates `fors-fmir`/`fors-lower`/`fors-interp` (§2) | fusing lowering into `fors-fmir` would put `fors-check` under the verifier |
| E3 | `defer` inlined at exit edges, no runtime stack (§3.8) | ch01 R23a states it; a stack would also make the trap rule a special case instead of a consequence |
| E4 | `ub:` reports are **not** traps and exit with status 70 (§5.2) | ch02 R15's kind list is closed at eight; a compiler bug must not look like a program trap |
| E5 | Per-instruction step charging, checked per block (§6) | per-back-edge accounting lets a straight-line comptime body overrun |
| E6 | `heap_digest` off by default, masked by init bits (§7.1) | uninitialised padding is permitted by ch10 R13 and would produce false mismatches |
| E7 | `@fastmath` ignored; the interpreter always computes strict (§5.6) | ch03 R8 permits but never requires relaxation; ch05 R17 exempts those blocks |
| E8 | Nine intrinsics, closed table, each with a `comptime` column (§5.8) | an open intrinsic set makes ch04 R12 a review promise instead of a check |
| E9 | Arena generation at `u32::MAX` traps rather than wrapping (§3.7) | wrapping silently revalidates a stale `Ref`, which is the exact bug R17 exists to prevent |
| E10 | `fors-lower` owns the mono-vs-witness decision (§4.1 [HOLE-5]) | nobody else can: the checker's §8 table defers ch03 R16-R18 past M1 |
| E11 | `fors-lower` reads the module `contracts:` line itself until I10 lands D10 (§4.2) | a "default to `Runtime`" stand-in cannot pass `contract-off-no-check-run-ok`, which is F2's gate |
| E12 | `Target` is an explicit input; no host width, endianness or clock is read (§5.1, §7.2) | `usize` is the target pointer width (ch09 R3), so a host-derived one silently breaks the comptime memo and cross-compilation |
| E13 | `frem` is implemented in-crate, exactly, never as Rust's `%` (§5.5) | `f64 % f64` is a libm `fmod` call, which §5.6(4) forbids and which makes the oracle host-dependent |
| E14 | the borrow stack has SharedRO groups, not one tag kind (§5.2) | ch01 R7 makes overlapping `let` accesses legal; a single-tag model reports UB on accepted programs |

### 11.3 Holes that are engineering calls, not owner questions

§0 promises every `[HOLE-n]` is collected here. **[HOLE-1]** crate naming (`fors-fmir`/`fors-lower` vs `compiler-architecture.md`
§9's `fors-mir`) — E2, but §9's crate list should be corrected. **[HOLE-2]** a wrapped arena generation counter — E9, trap at
`u32::MAX`; ch01 R17 should gain one sentence. **[HOLE-7]** no checker increment types `reduce` — F5 hard-codes it; the cheapest fix
is one line in I10's rule list (add ch03 R11). **[HOLE-11]** is owner-sized but is not an owner *decision*: it is a plan gap in
`type-checker.md` that needs scheduling (increment I8b), not adjudication.

## 12. Risks, ranked, with the cheapest experiment that retires each

| # | Risk | Impact | Cheapest experiment |
|---|---|---|---|
| R1 | **[HOLE-11]: nothing plans ch01 R22-R23's checker side.** D7/D8/D9 have no producer, and `type-checker.md` routes R4/R5's definite-init to M3 | F4 and F6's lowering halves have no input; discovering it at F4 means re-opening `fors-check` mid-track | *(½ day)* draft I8b's scope against ch01's round-6 corpus and count the tests it must turn green. If `lin(T)` plus the definite-init lattice is under ~900 lines, schedule it after I7; if not, F4/F6 slip behind M3 and this document's F-order is wrong |
| R2 | **`BodyFacts` does not exist**; F1..F10 all need it | the whole track is blocked inside another workflow's crate | *(½ day)* land `crates/fors-check/src/facts.rs` as a pure addition — a `BodyFacts` SoA filled by the existing `synth`/`check` recursion, plus retaining the `UseTape` — with `body_facts_cover_every_typed_node` and no behaviour change. If the recursion cannot cheaply record a type per node, `type-checker.md` §7.3 has a problem worth knowing now |
| R3 | **Layout is undefined** and three increments need it (Q1) | `Vec`, `Own`, `Buffer` and D11's 16-byte test are all blocked | *(1 day)* `spikes/fors-layout/`: implement Q1's rule over the FIR types the 64 tests use, print the size/align/offset table, diff it against `clang` on the C-equivalent structs. If they agree, the rule is also the FFI rule and Q1 answers itself |
| R4 | **Bit-exactness against a backend that does not exist** (§5.6, Q2) | a wrong float or NaN choice compounds silently for months | *(1 day)* `spikes/fp-agreement/`: a fixed 10⁴-op float trace through (a) `fors-interp::arith`, (b) hand-written aarch64 via the existing `spikes/aarch64-macho` encoder, (c) `clang -O0 -ffp-contract=off`; compare bit patterns including NaN and `frem` |
| R5 | **The interpreter becomes lenient.** An oracle that misses UB certifies wrong programs | worse than no oracle | *(1 day)* a **negative corpus**: ~20 hand-written FMIR declarations, one per §5.2 condition, each asserted to its `ub:` class — plus the two *positive* aliasing cases of E14, because a false `ub:` is as fatal as a missed one. Written in F0's textual FMIR, before F1 |
| R6 | **Defer inlining explodes** on nested scopes × many exits | FMIR size blows the 12 B/source-byte budget and the dev backend's 50 ms with it | *(½ day)* a generator emitting the worst shape at increasing sizes, plotting FMIR instructions against source bytes. If superlinear, adopt R23a's permitted "emit one copy and jump to it" in F4 rather than in M2 |
| R7 | **`reduce`'s tree is subtly wrong and every test still passes.** The corpus pins only n ∈ {0,1,3,7,8,9,257} | a shape bug at n = 300, or in a partial lane of a non-final block, survives to M2 | *(2 h)* generate the shape for n ∈ 0..1024, hash the table, check the hash in, and independently re-derive it in Python from ch03 R11's text. Two derivations from one paragraph is the cheapest proof the paragraph was read right |
| R8 | **Comptime budgets are guesses** derived from a speed target | if the real figure is 5 M steps/s, the budgets shrink 6× and the memo becomes load-bearing, which changes F9 | *(½ day, after F1)* run the dispatch loop on three shapes (integer loop, memory-heavy, call-heavy), report steps/s, re-derive §6's table |
| R9 | **`fors-interp` drifts into consulting the front end** (ch05 R3) | one `use fors_syntax::` for a better diagnostic destroys the oracle | *(10 min)* the CI grep, written in F0, before there is anything to grep |
| R10 | **Two whole spec chapters and five root capabilities have no runtime test** (§8.1) | every ch05 rule is unverified by the corpus | *(1 day, owner Q5)* write `tests/conformance/05-ir/` during F0 from ch05's own 22-name list — transcription plus the verifier, not design |

## 13. Review dispositions (adversarial review, 2026-09-20)

An independent reviewer attacked this document against ch01/02/03/04/05/10, `type-checker.md` §8/§13/§15, and all 64 runtime tests.
Findings and repairs, in the style of §17 there.

| # | Finding | Severity | Disposition |
|---|---|---|---|
| 1 | **D7/D8/D9 claimed I8 as their producer. `type-checker.md` has no rows and no increment for ch01 R22-R22i, R23-R23f or R19c/R19d** — the words `defer`, `errdefer` and `Linear` do not occur in it, and its §8 routes R4/R5's definite-init to M3 | critical | **[HOLE-11]** added (§4.1) with a recommended increment **I8b**; D7/D8/D9 now read "nobody"; F4/F6 dependencies rewritten; risk R1; §11.3 |
| 2 | **F1's "checker dependency: I3" was false.** All 19 gate tests end in `out.write_line("ok")`, an inherent method call; `type-checker.md` §13 puts R43/R46 in **I4** | critical | §4.2 rewritten, D3 corrected to I4, F1's dependency line corrected. F0 remains genuinely dependency-free and is the one increment shippable today |
| 3 | **ch05 R5's five alias sources: three are unrepresented, and §3.7 said brands are "erased".** R5 calls the arena brand id "compile-time IR metadata"; split-token provenance has no carrier at all. OIR cannot recover either | critical | new **§3.4a** (`AliasSeed` pool, one `u64` per memory-producing instruction) with F0 gate tests; §3.7 and §1.2 reworded |
| 4 | **`ub: aliasing` would have fired on legal code.** A single-tag Stacked-Borrows pops a shared item on the next read, but **ch01 R7 makes two overlapping `let` accesses legal**; a `ub:` report exits 70, so this fails the corpus | critical | §5.2's row rewritten with SharedRO groups; E14; two *positive* gate tests added to F6 and to risk R5's negative corpus |
| 5 | **ch05 R6a/R6b were owned by nobody.** §1.1 asserted R6b "makes it a static error" without saying whose error; no increment, table row or datum covered it | major | new **§3.11**, two §8 rows, datum **D13**, eight ch05 conformance names added to F0's gate |
| 6 | **The closed intrinsic table could not express ch10 R42 / ch04 R13**, yet F9 gates on two comptime file-read tests; and `std/io.fors`'s `write_line` is a `{}` stub, so every `run-ok` test would print nothing | major | `@input_read` added (ten intrinsics, comptime-only); §5.8 now states F1 writes the five `write_*` bodies **in Fors** over `@fd_write`, with the buffer and latch as ordinary fields |
| 7 | **Three gate tests cannot pass the README's literal expectation kinds.** `main-raises-after-defer-run-error`'s stderr carries the deferred line *before* `detail`; the two trap/defer tests need the interpreter's own trap line distinguished from the program's `Stderr` | major | new **§7.2a** pins what the runner compares per kind, and surfaces the ch05 R17 backtrace conflict as owner **Q7** |
| 8 | **Host dependence: `usize`/`isize`/`rawptr` are the *target* pointer width (ch09 R3), endianness is observable through `@memcpy`, and the comptime memo key omitted the target** | major | `Target` added as an explicit input (§5.1), `target_hash` added to the memo key, CI grep for `usize` in `value.rs`/`arith.rs`, determinism list extended to `HashSet`/`RandomState` |
| 9 | **`frem` is a libm call in Rust** (`f64 % f64` → `fmod`), contradicting §5.6(4) "no libm"; and §5.6(2) "never touches FPCR" contradicted §5.6(5)'s "aarch64 gives it under DN=1" | major | §5.5 specifies an in-crate exact `fmod` (E13) with a reference-table test; §5.6(2) now separates the interpreter's software canonicalisation from M2's backend obligation, and (5) states plainly that canonicalising is a departure from IEEE's *recommendation* |
| 10 | **F6 gated on `vec-deinit-empty-nonempty-trap`, whose `Vec.new`/`push`/`deinit_empty` bodies F7 writes** (and whose `a.create(1)?` is I4's method-on-bound); F2's "lowering-side default" cannot produce `.off` for `contract-off-no-check-run-ok` | major | the test moved to F7's gate; F6 re-gated on `arena-generation-trap` plus hand-written FMIR; E11 records that `fors-lower` reads the `contracts:` line itself until I10 |
| 11 | **ch04 R14's per-declaration budget is not a build budget**: 200 comptime-heavy declarations at `2^20` is 7× §10.1's own 1 s allowance | major | `COMPTIME_BUILD_STEP_BUDGET` added to §6 and raised as owner **Q6**; comptime `ptr_to_int` pinned to a synthetic deterministic address so ch04 R12 holds while R15 only bars tier-up |
| 12 | **Honesty sweep.** "62 opcodes" did not match §3.10's own table; §8 cited `vec-deinit-empty-nonempty-trap` as corpus evidence for a *linear leak* when it traps on a contract; §0 promised every `[HOLE-n]` is collected in §11 while HOLE-1, -2 and -7 were not | minor | opcode count corrected to 71 with the mode-field convention stated; the R22d row marked **GAP**; **§11.3** collects the loose holes |
| 13 | **Two corpus tests look self-inconsistent** — `sigpipe-ignored-write-latches-run-ok` puts `else \|e\|` on a total method and expects exit 0 where R40(d) says 2 | minor | **LEFT OPEN**: owner **Q8**; §8.1 gap 7; F2's gate reduced to seven tests until it is resolved |

**Checked and found sound** (recorded so they are not re-litigated): the `reduce` expansion of §3.9 reproduces ch03 R11/R13 exactly,
including the partial-lane tail, the empty-lane rule and the odd block carried up — it derives the corpus's own n = 1, 7, 8, 9 and
257 values by hand; `defer` inlining on exit edges with no runtime stack is R23a's own words and makes R23f ("a trap runs no defer")
a consequence; there are **no implicit drops** in Fors, so there is no defer/errdefer/drop ordering question to get wrong — R22d
makes every discharge an explicit move; the implicit `sink self` receiver move lowering to `move_from` matches ch01 R2; all 64
runtime tests are named by some increment gate; §10.1's budget arithmetic checks out; [HOLE-4] is accurate against the code
(`CheckOutput` at `crates/fors-check/src/lib.rs:37` carries no per-expression type, callee map or tape, and there is no `facts.rs`).
