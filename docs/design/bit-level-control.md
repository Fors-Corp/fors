# Bit-level control — RFC-ready draft (design, non-normative)

> **Status: design draft, 2026-09-22. Branch `feat/spec-bitlevel`.**
> This document is an RFC-ready draft ONLY. It proposes surface syntax,
> typing, layout, and checking rules for the full bit-level set. It is
> **not normative**: no change to `docs/spec/` lands unless an approved RFC
> adopts it. Where this draft cites a spec rule, the spec wins on any
> conflict; conflicts are flagged as open owner questions (§9).
>
> **Owner directive:** language as close as possible to binary. Every
> construct below names its bytes, its bits, and its cost. Nothing here
> hides a fence, a zeroing pass, a reordering, or an implicit conversion.

## 0. Sources and vocabulary

Read first (all citations below refer to these):

- `docs/spec/03-numerics-determinism.md` — integer widths (Rules 1-6),
  strict IEEE default, D1 determinism (Rule 10), `reduce` shape.
- `docs/spec/01-ownership.md` Rules 10-18 — `iso`/`imm` (10-13), `secret`
  orthogonality (14), brands/arenas/`Own` (15-18); scoped return (19-19d);
  `Shared` + `atomic[T]` position (21-21d); linearity + `defer` (22-23f).
- `docs/spec/09-types.md` — type universe, `Copyable`, layout **delegated
  to ch05** (Rules 3, 6; "Not owned" table); closed operator set (Rule 21).
- `docs/design/fmir-interpreter.md` §3.7, §4.1 [HOLE-6], §11.1 Q1 —
  arenas/generations, D12 (layout unowned), the Q1 layout rule proposal.
- `docs/spec/10-std.md` — `Layout`/`MEM_MAX_ALIGN` = 16 + S0013, S0011
  (linearity list), S0028 (`@unsafe` inventory precedent).
- `docs/spec/07-grammar.md` — what syntax exists today (§1 below).
- `docs/spec/05-ir-contract.md` (ch05) — R5 (alias classes, five sources +
  `unknown`), R6/R6a/R6b (secret), R15 (CT verifier), R16 (pass
  propagation), R17 (bit-for-bit agreement), R18 (DWARF companion),
  R19 (asm opaque regions).
- `docs/spec/04-authority.md` (ch04) — `@unsafe(invariant:)` is a
  **declaration attribute only** (Rule 10); sealed capabilities
  `syscall`/`asm`/`ffi` (Rules 2-2b); `needs` (Rule 1); root capabilities
  (Rules 7-8, 21); asm preconditions (Rules 22-27).
- `docs/spec/02-failure.md` (ch02) — trap-kind set is **closed at eight**
  (Rule 15): `contract`, `bounds`, `overflow`, `div-zero`, `shift`,
  `checked-conversion`, `arena-generation`, `empty-reduce`. No ninth kind
  may be invented by this draft.

**Layout vocabulary.** There is no `crates/fors-layout` in this worktree
(checked 2026-09-22: `crates/` holds `fors-asm`, `fors-check`, `fors-cli`,
`fors-diag`, `fors-fir`, `fors-fmir`, `fors-fmt`, `fors-index`,
`fors-lex`, `fors-lsp`, `fors-query`, `fors-resolve`, `fors-syntax`).
This draft therefore reuses the Q1 vocabulary without duplicating any
decision: **size, align, offset; declaration order; natural alignment; no
reordering; `align ≤ MEM_MAX_ALIGN` (16, ch10 S0013); enum discriminant
is the smallest unsigned type fitting the variant count.** "Q1" below
means exactly that proposal (`fmir-interpreter.md` §11.1 Q1). Adopting
this draft's layout rules REQUIRES adopting Q1 first; every section notes
this dependency once and does not re-argue it.

**Cross-check keys used in every section.** Q1 (layout rule above); R6 =
ch05 secret bit + R6a propagation + R6b rejection; R15 = post-regalloc CT
verifier; R16 = passes propagate secret/`ct_region` unchanged, no reorder
across `ct_region` boundaries; R17 = bit-for-bit agreement
(interp/dev/release/`--serial-elide`) on programs without `@fastmath` /
`reduce.fast`; R18 = DWARF companion artifact (unsigned, never changes
the signed image hash). ch01 R15-R18 (brands) are cited where addressable
memory meets arena discipline. The **no-hidden-cost principle**: every
operation's machine cost (fence, RMW cycle, trap check, zeroing) is
visible in its spelling; defaults that smuggle a fence, a branch, or an
allocation are rejected in favor of explicitness.

## 1. What syntax exists today (ch07 inventory)

None of this draft's surface exists in the grammar. Attested facts that
constrain every proposal:

- `field = [ "pub" ] ident ":" type ;` — struct fields have no width,
  offset, or attribute slot beyond `pub` (ch07 `struct_decl`). Adding
  per-field control needs a grammar change; attributes already exist as
  `attribute = "@" ident [ "(" ... ")" ] ;` on declarations, and
  `attr_block_stmt = attribute block ;` for blocks.
- `type = { qualifier } type_core ;` with qualifiers `iso | imm |
  secret` only. A `volatile` or `atomic`-ordering qualifier is a new
  reserved word (ch07 reserved list is closed; `set` is the cautionary
  tale for staying contextual).
- The operator table is closed and the bitwise tier is flat with
  mandatory parentheses on mixing (ch07 D4). Pointer arithmetic MUST NOT
  reuse `+`/`-` on pointers: ch09 Rule 21's operator-trait set is closed
  and homogeneous (`Self x Self -> Self`), so `ptr + int` has no trait to
  resolve to. Pointer movement needs method calls or named forms.
- `asm_expr` exists with `in`/`out`/`clobber` items and at least one
  string item (parse error otherwise). `extern "c" fn` declarations
  exist. There is NO `extern` block, NO link-section attribute, NO naked
  attribute, NO bit-field width suffix, NO `pad`/`reserved` field form.
- `const` declarations and const generic arguments exist
  (`Array[T, N]`, `N: usize`); widths and paddings can therefore be
  const expressions, evaluated by comptime (ch04 Rules 11-14).
- `attribute` args are `[label:] (literal | path)` — never `expr`. An
  ordering or section spelled as an attribute argument MUST be a literal
  or path, not a computed expression. This rules out
  `@link_section(prefix + ".x")`; section names are string literals.

Consequence stated once: **every section below needs a ch07 grammar
delta**, each flagged `GRAMMAR:` with an LL(2) note. None is claimed as
parseable today.

## 2. Bit-fields

### 2.1 Proposed surface syntax

A bit-field is a struct field with a `:` width suffix. The width is a
const expression (0 < W ≤ base width in bits),
evaluated at comptime:

```ebnf
field = [ "pub" ] ident ":" type [ ":" const_arg ] ;
```

`const_arg` is ch07's existing non-terminal (a bare path or `add_expr`
without calls). Examples:

```fors
needs { };

struct Ipv4Flags {
    reserved: u8:1,
    df: u8:1,
    mf: u8:1,
}

struct Packed {
    a: u8:3,
    b: u8:5,
    tag: u16,
    c: u8:2,
    d: u8:6,
}
```

```fors
needs { };

struct Reg {
    enable: u32:1,
    mode: u32:2,
    status: u32:4,
    count: u32:9,
}

fn set_mode(inout r: Reg, let m: u32) {
    r.mode = m;      // field assignment; whole-unit read-modify-write
}
```

GRAMMAR: `field` gains one optional `":" const_arg`. Disambiguation is
LL(2): after the field's `type`, `:` followed by `,`/`}` continues as
today (no width); `:` followed by a const-arg start (number, `-`, ident)
is the width. `Array[T, N + 1]`-style arithmetic inside a width is
rejected exactly like ch09 Rule 13 rejects it in type position (same
rationale: the range error could surface only after instantiation).
`soa struct` fields MAY carry widths (SoA of bit-fields is layout §2.2
applied per lane column; codegen lowers to the same unit RMW).

### 2.2 Typing / layout rules

1. **Base type.** The type before `:` MUST be an unsigned integer
   primitive (`u8`/`u16`/`u32`/`u64`; ch03 Rule 1 — no 128-bit, no signed
   bases, no `bool`, no `usize`). Signed bit-fields are rejected: sign
   extension on extraction is a second semantics to pin for zero benefit;
   sign-extend explicitly with `as` after extraction. The field's
   **value type** is the base type (reads zero-extend into it, writes take
   it and trap-or-wrap per §2.5 on overflow of the width).
2. **Runs and storage units.** A maximal run of consecutive bit-field
   fields with the SAME base type packs into consecutive storage units of
   that base type ("unit" = one `sizeof(base)` cell, naturally aligned).
   Within a unit, fields allocate **LSB-first in declaration order**:
   the first field occupies bits `[0, W)`, the next `[W, W+W')`, and so
   on; a field that does not fit the current unit starts the next unit
   (no splitting across units in v0.1). Across units, units follow
   declaration order = address order (Q1, little-endian v0.1 targets).
   A field with a different base type, or any normal field, ENDS the run:
   the current unit is closed (leftover bits become compiler-reserved
   padding, unobservable, never a named value) and the next field starts
   at the next offset satisfying its natural alignment.
3. **Q1 conformance.** Bit-fields obey Q1 with one refinement: Q1's
   "fields in declaration order, no reordering" holds at unit
   granularity; bit order inside a unit is the LSB-first rule above,
   which is part of the adopted layout algorithm, not a per-target
   deviation. `Layout.of[T]().size` for a bit-field struct is therefore
   computable from the declaration alone — a program can branch on it,
   which is exactly why Q1 is an owner decision and why this rule is
   normative-shaped rather than "implementation-defined".
4. **Mixing.** Normal fields keep their Q1 offset/size/alignment
   unchanged; a run never absorbs a normal field and a normal field
   never splits a unit. `align` of the struct is the max of member
   aligns (base types of runs), capped by `MEM_MAX_ALIGN` (S0013).
5. **No addressable sub-unit.** A bit-field is NOT a `place` (ch07
   `place = ident { "." ident | bracket }` still parses, but ch01/ch09
   reject `&x.field`, `&out x.field`, `move x.field` on a bit-field):
   there is no address of 3 bits. Reads copy the value out; writes are a
   unit read-modify-write. Assignments `a.b = e;` typecheck with `e`
   checked against the base type (ch09 Rule 31 shape).
6. **Zero-width runs and `:0`.** `f: u8:0` (force next unit) is
   **out of v0.1** (§2.7). Close the run with a normal `pad` field (§3)
   instead; one spelling for alignment control.
7. **Endianness.** v0.1 targets are little-endian only
   (`aarch64-apple-darwin`, `x86_64-*`; `fmir-interpreter.md` §5.1 pins
   `endian = Little`). The LSB-first rule IS the little-endian rule.
   Big-endian targets are out of v0.1; when one arrives, declaration
   order = address order is kept and the intra-unit bit numbering is
   re-pinned by RFC (candidate: MSB-first, matching C on BE). Layout
   hashes cover `Target{endian}` so no recorded oracle output silently
   changes meaning.

### 2.3 Alias-class interaction (ch05 R5)

A bit-field access aliases the WHOLE storage unit's class, never a
sub-unit class: the alias seed of `r.mode` is the seed of the unit
(`Conv`/`Own`/`Arena`/`Split`/`SoA-field` per the base place, §3.4a
carriers). Two bit-fields in the same unit ALWAYS alias each other;
disjointness sets never distinguish them. Consequence: a `parallel for`
varying-index store through a bit-field (ch01 Rule 9) is rejected —
`out[i].flag = x` varies the unit as well as the index — unless the
index expression denotes disjoint UNITS (whole-unit granularity), which
the checker decides syntactically from the base place alone. No new
alias source is added; bit-fields reuse R5's five plus `unknown`
(Rule 19 for asm-derived pointers).

### 2.4 Secret / CT interaction

ch05 R6a: `secret` on an aggregate covers every field and the
discriminant — bit-fields included, with no per-field opt-out. A
`secret` struct's bit-field read yields `secret` base-typed value;
writing a non-secret value into a `secret` struct's bit-field is
rejected (R6a "MUST NOT be stored to ... a non-secret type", direction
preserved). R6b applies to the lowered unit op: a bit-field read/write
whose unit op would be a trapping conversion or a branch on the value
is rejected when secret; the value-range narrowing of §2.5 MUST use the
`wrap_` form (never the trapping form) for secret operands. Whole-unit
RMW on secret data is allowed (it is data-independent: fixed mask,
fixed shift, no branch) and stays inside the value's `ct_region`; the
CT verifier (R15) sees one masked RMW, never a branch. `declassify`
follows R6a unchanged (inside `@unsafe` only, in the audit inventory).

### 2.5 Capability / `unsafe` interaction

- **Declaration needs no capability and no `unsafe` by itself.**
  Bit-fields are pure layout + integer ops; they confer no authority
  (ch04 Rule 1: nothing used outside the process).
- **MMIO use needs `@unsafe`.** A struct used to drive hardware (a
  bit-field struct overlaid on a register via §6 pointer casts or volatile
  §4) MUST carry `@unsafe(invariant: "...")` on the struct declaration or the mapping
  function, listed in the unsafe inventory (ch10 S0028 precedent). The
  bit-field syntax itself stays safe; the *overlay* is the unsafe act.
- **No sealed capability** (`asm`/`syscall`/`ffi`) is implied or required
  by bit-fields. A driver that touches ports still needs `asm` for its
  `asm` blocks (ch04 Rule 22) — orthogonal facts, both recorded.

### 2.6 Trapping vs compile-error behavior

- **Compile errors** (all statically decidable): base type not unsigned
  integer; width ≤ 0 or width > base width; width not a closed const
  expression (ch09 Rule 13 shape); `&`/`&out`/`move` of a bit-field
  (not a place); bit-field of linear type (ch01 Rule 22b shape —
  `Array`/`vector`/`atomic` reasoning extended one step: an element can
  leave only by partial move, forbidden by ch01 Rule 4a(c)); bit-field
  in a `Shared`-checked position that breaks ch01 Rule 21a (the base
  integer is neither `atomic` nor `imm` — a bit-field field
  disqualifies a `Shared` impl unless the field is `imm`, same as any
  plain integer field).
- **Traps** (dynamic): writing a value that does not fit the width.
  Default is the CHECKED rule, mirroring ch03 Rule 6 (`as` traps unless
  exactly representable): `r.mode = v` traps `checked-conversion` when
  `v ≥ 2^W`. Non-trapping writes use explicit method forms on the
  field place — `r.mode.wrap_set(v)` (truncate), `r.mode.sat_set(v)`
  (clamp) — field-assignment forms with the statement-level shape of
  ch09 Rule 21's `a op= b` (the field place is evaluated once, the value
  narrowed with wrap/saturate semantics, no trap), the exact analog of
  ch03 Rule 4's `wrap_`/`sat_` methods.
  No silent truncation anywhere: this is the no-hidden-cost principle
  applied to narrowing. Reading never traps.
- No new trap kind: `checked-conversion` is reused (ch02 Rule 15 closed
  list respected).

### 2.7 What stays explicitly out of v0.1

Signed bases; split-across-unit fields; `:0` unit forcing; bit-fields of
`signed`/`bool`/`usize`/`f32`; `volatile` bit-fields (§4 covers volatile
fields; the combination `volatile` + width is rejected — take the whole
unit volatile instead); `atomic` bit-fields (rejected — atomics operate
on whole cells, §5); bit-field-to-bit-field assignment across different
widths without an explicit `wrap_`/`sat_` step; `pub` bit-level
offset guarantees beyond `Layout.of` (no ABI promise, ch10 S0009:
binary layout is not stable across versions); C-compat `#pragma pack`
equivalents (explicit `pad` + Q1 covers it).

## 3. Explicit padding + reserved bytes

### 3.1 Proposed surface syntax

Two named field forms, both part of the struct declaration (new
alternatives of ch07 `field`):

```ebnf
field = [ "pub" ] ident ":" type [ ":" const_arg ]
      | "pad" "[" const_arg "]"                 (* unnamed padding *)
      | "reserved" "[" const_arg "]" ;          (* zero-checked spare *)
```

Concrete spelling (attribute-free, keyword-led, so no new `@`-form is
needed and ch07's LL(2) bound holds — `pad`/`reserved` become contextual
in field position only, exactly like `set` is contextual in parameter
position):

```fors
needs { };

struct DmaDesc {
    addr: u32,
    pad[4],
    len: u16,
    flags: u16,
    reserved[8],
}
```

```fors
needs { };

struct Header {
    magic: u32,
    version: u16:4,
    kind: u16:4,
    pad[2],
    total: u32,
}

fn wire_size() -> usize {
    return Layout.of[Header]().size;   // 12: padding is observable, Q1
}
```

GRAMMAR: `pad`/`reserved` are contextual keywords in field position
(LA 1: current token `pad`/`reserved` + next `[` selects the padding
alternative; any other field starts with `pub` or an identifier). A
binding, member, or path segment MAY still be named `pad` or `reserved`
outside field position (ch07 Rule 10 precedent: `out`, `set`, `grain`).
`N` in `pad[N]`/`reserved[N]` is a `const_arg` (closed const expression
or bare const parameter; no `N + 1` arithmetic, ch09 Rule 13).

### 3.2 Typing / layout rules (interaction with Q1 no-reorder)

1. `pad[N]` occupies exactly `N` bytes at its declaration position. It
   has no name, no type, no value: it cannot be read, written, borrowed,
   moved, matched, or iterated. Any use of it as an expression is a
   compile error naming the struct ("`pad` bytes have no value").
2. `reserved[N]` occupies exactly `N` bytes at its declaration position
   AND carries the zero invariant: every value of the struct, on every
   construction path (literal, comptime, deserialization write), MUST
   have all-zero `reserved` bytes. Reads of `reserved` bytes are a
   compile error (same as `pad`); the invariant is enforced at
   construction (§3.6), not by hiding reads.
3. **Q1 interaction (the point of this section).** Q1 fixes declaration
   order + natural alignment + no reordering. Explicit `pad`/`reserved`
   are how the programmer CONTROLS what Q1's alignment would otherwise
   insert silently:
   - The compiler MUST still insert Q1's natural-alignment padding where
     a member's alignment requires it; that padding is compiler-owned,
     unobservable except through `Layout.of[T]().size`, and MUST be
     minimal (no target-specific over-alignment below `MEM_MAX_ALIGN`).
   - A `pad[N]`/`reserved[N]` NEVER merges with compiler alignment
     padding and is never removed, shrunk, or reordered, at any opt
     level: it is a declared member for layout purposes. Redundant
     padding (a `pad` exactly where alignment padding would already fall)
     is legal and kept — explicitness over cleverness.
   - `align ≤ MEM_MAX_ALIGN` (S0013) applies to the struct as a whole;
     a `pad`/`reserved` larger than 16 bytes is fine (it is size, not
     align). A requested over-alignment (`align(N)` attribute) is **out
     of v0.1** (§3.7).
4. `pad`/`reserved` are invisible to genericity: they take no type or
   brand argument, contribute no `lin` component (ch01 Rule 22a descent
   skips them — they hold no value), and contribute no `Copyable`/`Shared`
   obligation. A struct that is otherwise all-`Copyable` stays
   `Copyable`.
5. Zero-size forms: `pad[0]`/`reserved[0]` are legal no-ops (useful for
   generic `pad[N]` with `N = 0`). Accepted, not warned on.

### 3.3 Alias-class interaction (ch05 R5)

Padding has no alias class because it has no value and no addressable
name: no load/store ever names it, so no OIR memory op carries a class
for it. `memcpy`/`memset` over the whole struct (intrinsics,
`fmir-interpreter.md` §5.8) copy padding bytes as untyped data — this is
the one place padding moves, and it needs no alias seed beyond the
base place's own. A split-token (`split_at`, ch01 Rule 19b) MUST NOT
split inside a `pad`/`reserved` span: split boundaries that land inside
padding are compile errors (the halves' provenance would be
unstatable). SoA-field identity (§3.4a) treats `pad`/`reserved` as
non-columns: they occupy no lane storage.

### 3.4 Secret / CT interaction

R6a: padding is not a value, so it is never `secret`-typed and never
carries the secret bit. Consequences, all verifier-checked:

- `memcpy` of a struct containing `secret` fields copies their bytes
  (including any adjacent `pad`) as secret-tainted destination bytes;
  the `pad` bytes themselves gain no taint of their own — taint attaches to
  values, and padding is not a value. The lowering MUST NOT copy a
  secret field's bytes through a temporary typed non-secret
  (R6a storage rule).
- Secret-spill zeroization (ch05 Rules 7-8) covers whole spill slots
  including any padding inside them; padding MUST NOT be used as an
  excuse to skip zeroization of a slot ("the secret field is only 3
  bytes of a 4-byte slot" is not an argument the CT verifier accepts).
- `reserved` zero invariant + secret: a `secret` struct's `reserved`
  bytes are still all-zero (zero is not secret information; writing
  zeros into `reserved` is always allowed, reading them is still a
  compile error). No branch on `reserved` contents exists anywhere, so
  R6b's branch-on-secret rejection is untouched.

### 3.5 Capability / `unsafe` interaction

- **Declaration needs no capability and no `unsafe`.** Padding is pure
  layout.
- **`reserved` misuse is a program bug, not an authority breach**: no
  sealed capability involved. The zero invariant is enforced by
  construction checks (§3.6), and violations are traps, not
  capability errors.
- FFI structs with `pad`/`reserved` used across `extern` calls need
  `ffi` in the calling module (ch04 Rule 2a) — but that comes from the
  `extern` call, never from the padding itself.

### 3.6 Trapping vs compile-error behavior

- **Compile errors:** use of `pad`/`reserved` as a value (read, borrow,
  move, match binding, `&out` target); split boundary inside padding
  (§3.3); `pad[N]`/`reserved[N]` with non-closed or negative `N`;
  `reserved` bytes given a nonzero value in a struct literal
  (`reserved` has no literal syntax at all — there is nothing to write,
  so this error fires only for comptime-constructed or transmute-built
  values reaching verification with nonzero reserved... see traps).
- **Traps:** a `reserved` invariant violation detected at run time traps
  `contract` (ch02 Rule 15; it is a violated `invariant`, exactly what
  the kind is for). Constructions that the compiler can prove zero
  (literals — nothing to write; `alloc_zeroed` paths) carry no check
  (ch02 Rule 10's proof-discharge shape, future prover; today: the check
  is emitted wherever the value is built by non-literal means, e.g. an
  `@memcpy` from wire bytes followed by a `validate` call — the VALIDATE
  step is an explicit std call, never an implicit check: no hidden cost).
  Plain `pad` bytes have no invariant and never trap.
- Reading padding can never trap because it cannot be written.

### 3.7 What stays explicitly out of v0.1

`align(N)` / packed(`packed`) attributes; `union` (the overlay itself —
§6 covers casts, not unions); `pad` with a runtime length; named
padding (name it a real `[u8; N]` field instead); nonzero-fill reserved
patterns (`reserved_fill(0xFF)` — wire formats that need it can write
explicit fields); bit-granularity `pad_bits[N]` (use `:W` runs + normal
`pad`); static assertions on offsets BEYOND `Layout.of` in `pre`
clauses (already expressible: `pre Layout.of[Header]().size == 12` —
that stays the mechanism, no new `static_assert` item).

## 4. Volatile access

### 4.1 Proposed surface syntax

Volatility is a field attribute plus explicit access functions. The
attribute form covers the MMIO-register case (every access volatile);
the function form covers one-shot volatile access to a normal place:

```fors
needs { };

struct Uart {
    @volatile
    data: u8,
    @volatile
    status: u32,
}

fn poll(inout u: Uart) -> u8 {
    while (u.status & 1) == 0 {
    }
    return u.data;
}
```

```fors
needs { };

fn ring_bump(let mmio: rawptr[u32]) {
    let h: u32 = volatile_load(mmio);   // one volatile read, exact width
    volatile_store(mmio, h.wrap_add(1)); // one volatile write
}
```

Full spelling:

- Field attribute: `@volatile` on a struct field (a fixed-size scalar
  integer/`bool` field; never a bit-field, never an aggregate —
  §4.7). Every read/write of that field through any path is volatile.
- Functions (prelude or `std.mem`, exact home an std RFC's call):
  `volatile_load(let p: rawptr[T]) -> T`,
  `volatile_store(let p: rawptr[T], let v: T)` for `T` a scalar
  integer/`bool`. Taking `rawptr[T]` (not `&T`) is deliberate: volatile
  access is by address, and ch07 gives `&` only to `arg_value`
  convention markers — a volatile borrow marker would collide with that
  grammar.
- `volatile_copy(dst: rawptr[u8], src: rawptr[u8], len: usize)` (byte
  loop, every byte volatile both sides) is **out of v0.1** (§4.7); call
  `volatile_load`/`volatile_store` in a loop.

GRAMMAR: `@volatile` needs no grammar change (attributes exist). The two
functions need none either (ordinary declarations). The ONLY grammar
delta is a validity rule, not a production: `@volatile` on anything but
a scalar-typed struct field is rejected in the checker (attribute-target
check, ch04 Rule 10 shape).

### 4.2 Typing / layout rules

1. `@volatile` changes NO type, NO size, NO alignment, NO offset. A
   `Uart` with volatile fields has the same `Layout.of` as without —
   volatility is an access property, and Q1 computes layout without
   reading attributes. `Copyable` is unaffected (a volatile `u32` field
   is still `Copyable` data); `Shared` is unaffected (a volatile field
   is neither `atomic` nor `imm` — a `Shared` struct with a volatile
   field is rejected exactly like one with a plain integer field,
   ch01 Rule 21a; MMIO blocks are NOT `Shared`).
2. A volatile field MUST have type `i8..i64`, `u8..u64`, or `bool` (a subset
   of the ch09 Rule 3 primitives: no floats, no `isize`/`usize`/`rawptr`).
   Floats, pointers, aggregates,
   slices, bit-fields: rejected. Rationale: exactly-width access (§4.3)
   is definable only for fixed small widths; pointer-width volatility
   invites provenance confusion (§6).
3. `volatile_load`/`volatile_store` take `rawptr[T]` with `T` scalar
   integer/`bool`; any other `T` is a compile error. The `rawptr[T]`
   MUST be non-null, aligned, and in-bounds at the call (§4.6 traps).
4. Volatile access is NOT `let`/`inout` borrowing: it does not create an
   exclusivity access under ch01 Rules 6-7 (it cannot — the hardware may
   change the value concurrently). Consequence: volatile fields are
   exempt from the exclusivity conflict check (two volatile accesses
   never conflict with each other or with `let` reads), AND volatile
   accesses grant no no-alias fact to the backend (ch01 Rule 7's note
   extended: a volatile path MUST NOT be annotated `noalias`).

### 4.3 Alias-class interaction (ch05 R5) + what the optimizer may/must not do

This is the normative-shaped core of the section:

- Volatile accesses keep the base place's R5 seed (`unknown` is NOT reused:
  it is Rule 19's asm-input class). Split provenance and arena brands still
  verify) but are marked with a non-optional `volatile: bool` operation
  flag (the same "field that cannot be absent" shape as R6's secret bit).
  `--verify-each` rejects a volatile-flagged op missing its flag the
  same way it rejects a missing alias class.
- **The optimizer MUST NOT:** eliminate a volatile access as dead
  (even `volatile_load` whose result is unused); CSE/hoist/sink a
  volatile access across any other volatile access to the same address,
  across an `asm` block (ch05 R19), or across a `ct_region` boundary
  (R16); narrow, widen, or split a volatile access (an `u32` volatile
  read is exactly one 4-byte access — never two `u16`, never a
  bitfield-extract on a wider load); invent a volatile access (no
  speculative volatile reads on any path, including after `if`
  branches — a volatile access the source does not execute MUST NOT be
  executed); reorder a volatile access with another volatile access in
  the same thread (program order preserved; no compiler reordering —
  hardware reordering is the fence's business, §5, and volatile implies
  NO fence).
- **The optimizer MAY:** reorder non-volatile accesses around volatile
  ones (subject to R5 disjointness as usual); keep a non-volatile cached
  copy of a volatile field's value ONLY within the single expression
  that read it (no caching across statements — each source-level read is
  one hardware read).

### 4.4 Secret / CT interaction

A `secret` value MUST NOT be read or written through a volatile access,
and a `@volatile` field MUST NOT be `secret`-typed. Reason: a volatile
access is observable by definition (bus, MMIO side effect, timing), and
R6b already rejects secret-to-capability (I/O) flows; volatile MMIO is
that flow without the capability wrapper. Two narrow exceptions, both
audited: (a) inside a declaration carrying BOTH `@unsafe(invariant:)`
AND `@ct_audited(by:)`, volatile access to secret is allowed and enters
the constant-time inventory (ch05 Rule 20 shape; ch04 Rule 26 gate);
(b) `volatile_store` of the literal `0` (scrubbing, ch05 Rule 8's
zeroize-before-epilogue lowered by hand) is always allowed. The CT
verifier (R15) treats any volatile op on a secret operand outside (a)/(b)
as a failure, not a diagnostic — it is a backend check on already
accepted IR. R16: volatile ops never cross `ct_region` boundaries by
construction (they are generated inside the region that contains the
source access).

### 4.5 Capability / `unsafe` interaction

- **`@volatile` field declaration: `@unsafe(invariant:)` REQUIRED.**
  The invariant names the mapping ("this struct overlays UART0
  registers at 0x..."). Recorded in the unsafe inventory (ch04 Rule 9's
  ledger; ch10 S0028 precedent). Rationale: volatile means "the value
  can change without program action" — the compiler's entire value
  analysis is suspended for that field, which is exactly the class of
  claim `@unsafe` exists to publish.
- **`volatile_load`/`volatile_store` calls: `unsafe` + sealed capability
  needed? NO to both — with one boundary.** The functions are ordinary
  safe declarations (their unsafety is in the ADDRESS, obtained via §6
  casts which are themselves `@unsafe`). No `needs` entry: volatility is
  not authority (ch04 Rule 1's test — no bytes leave the process that
  the address itself did not already grant). The boundary: a module that
  maps MMIO addresses with inline `asm` still needs `asm` for THOSE
  blocks (ch04 Rule 22), and a module that reaches ports via `svc` needs
  `syscall` (ch04 Rule 23) — orthogonal, composable facts.
- Recommendation recorded as OPEN (§9, Q-BIT-3): if the owner
  wants volatile-MMIO fenced to driver packages the way `syscall` is
  fenced to holders, add a sealed `mmio` capability in a follow-up RFC.
  This draft does NOT propose it (no new sealed capability in v0.1 —
  ch04 Rule 21's root list and Definitions' sealed list are both closed).

### 4.6 Trapping vs compile-error behavior

- **Compile errors:** `@volatile` on a non-scalar field, on a
  bit-field, on a local/parameter (fields only); `volatile_load/store`
  with non-scalar `T`; volatile access to a linear place (ch01 Rule 22d
  — a volatile read copies, which would duplicate-or-drop an obligation;
  rejected, consume linearly first); null `rawptr` literal as the
  address argument (statically known null).
- **Traps:** null, misaligned, or out-of-bounds address at the access
  traps `bounds` (one kind covers all three — the address names no
  object the program may touch; ch02 Rule 15 reused, no new kind).
  Uninitialized-memory read through volatile is NOT a distinct condition:
  MMIO reads what the hardware gives; the `init` bitmap (Miri side,
  `fmir-interpreter.md` §5.2) treats volatile reads as always-initialized:
  in the interpreter, a volatile access to unmapped memory is
  `ub: uninit-read`-exempt and yields the device model value; on real
  hardware it is the bus value).
- Volatile access itself never traps on the VALUE (no overflow/convert
  check — the width is exact by §4.2(2)).

### 4.7 What stays explicitly out of v0.1

Volatile bit-fields; volatile aggregates/slices; `volatile_copy`;
volatile + `atomic` on one field (rejected — pick one); volatile
parameters/locals (fields + explicit functions cover it); ordering
guarantees beyond same-address program order (that is §5's fences, never
implied by volatile — stated normatively-shaped because C/C++ confusion
here is the most likely defect); MMIO address-space typing (no
`MMIO[T]` wrapper type — `rawptr[T]` + `@unsafe` invariant is the whole
mechanism); a sealed `mmio` capability (see §4.5 open question).

## 5. Atomic ordering spelling

### 5.1 Proposed surface syntax

Position fixed first: `atomic[T]` appears ONLY as a field of a
`Shared`-implementing type (ch01 Rules 21-21d — not negotiable, not
re-proposed). This section owns ONLY the operations and their ordering
spelling. Ordering is a required trailing argument of enum type — no
default (no-hidden-cost: a default would smuggle either a fence or a
data race into silent code):

```fors
needs { };

struct Counter {
    n: atomic[u64],
}
impl Shared for Counter {}

fn bump(let c: Counter) {
    c.n.fetch_add(1, order: .seq_cst);
    let v: u64 = c.n.load(order: .acquire);
}
```

```fors
needs { };

struct Flag {
    ready: atomic[bool],
}
impl Shared for Flag {}

fn publish(let f: Flag) {
    f.ready.store(true, order: .release);
}

fn consume(let f: Flag) -> bool {
    return f.ready.load(order: .acquire);
}

fn try_claim(let f: Flag) -> bool {
    // compare_exchange: expected by inout, desired by value
    var expected: bool = false;
    return f.ready.compare_exchange(&expected, true, order: .acq_rel);
}
```

Full spelling:

- Ordering values are enum dot-literals of a prelude enum `Order`
  (`relaxed`, `acquire`, `release`, `acq_rel`, `seq_cst`) — ch07
  `dot_lit` in CHECK position against `Order` (ch03 Rule 21 precedent
  for CHECK-mode dot literals; no new literal form).
- Operations (methods on `atomic[T]`, receiver `let self` — ch01 Rule
  21d: atomic ops take the cell by `let`):
  `load(order:) -> T`;
  `store(let v: T, order:)` — `T: Copyable` required, so the value is
  copied in (no second owner can be minted); `swap`, `fetch_add`,
  `fetch_sub`, `fetch_and`, `fetch_or`, `fetch_xor` (integer `T` only,
  mirroring ch09 Rule 22's integer-trait table; each takes
  `(let rhs: T, order:) -> T` returning the PREVIOUS value);
  `compare_exchange(inout expected: T, let desired: T, order:) -> bool`
  (on failure writes the observed value back through `expected` —
  hence `inout`, the one `inout` in this surface).
- `order:` is a REQUIRED named argument (ch07 named-arg `ident ":"`
  form; ch09 Rule 37: labels must match). Omitting it is a compile
  error ("an ordering is required; there is no default"), never a
  defaulted fence.
- Which orderings on which ops (compile-error table otherwise):
  `load`: `relaxed | acquire | seq_cst`;
  `store`: `relaxed | release | seq_cst`;
  RMW (`swap`, `fetch_*`): `relaxed | acquire | release | acq_rel |
  seq_cst`;
  `compare_exchange`: `relaxed | acquire | release | acq_rel | seq_cst`
  (single ordering in v0.1 — separate success/failure orderings are
  §5.7). Anything else (e.g. `load` with `.release`,
  `store` with `.acquire`) is a compile error naming the op and the
  illegal ordering.

GRAMMAR: no production change (method calls + dot literals exist). The
`Order` enum is a prelude addition (ch08 Rule 17 mechanism; ch10 S0002
precedent for std-contributed prelude names — this one would be
language-known like `Option`, with its defining module nominated as
`std.mem`).

### 5.2 Typing / layout rules

1. `atomic[T]` with non-`Copyable` `T` is a compile error at the field
   (atomics copy the payload through registers on every op; a linear or
   non-`Copyable` payload could neither be copied nor moved out — ch01
   Rules 4a(c), 22b shape). In practice `T` is an integer or `bool`;
   `rawptr` atomics are **out of v0.1** (§5.7 — provenance +
   atomicity needs its own RFC).
2. Layout: `atomic[T]` has the size and alignment of `T` (natural
   align, Q1; `align ≤ 16`). Atomicity is a codegen contract (locked op /
   single-copy atomic instruction), never extra bytes. `Layout.of`
   agrees with `T`'s — observable and pinned (R17: the interpreter's
   emulated atomic and both backends agree bit-for-bit on the VALUE;
   timing may differ, values may not).
3. `atomic[T]` is never `Copyable` as a cell (moving the cell would
   duplicate the synchronization point)... precisely: the CELL is not
   copied; ops take it by `let` (ch01 Rule 21d) and mutate through the
   shared path — the one exception to Rules 11/20. The PAYLOAD `T`
   moves by copy semantics per op signature above.
4. Ordering arguments are comptime-known enum values (dot literals or
   `const`s of type `Order`); a runtime-computed ordering is a compile
   error (codegen must select the fence sequence statically —
   no-hidden-cost again: dynamic ordering would hide a branch-then-fence
   or force the strongest fence always).

### 5.3 Alias-class interaction (ch05 R5)

Atomic ops carry the base place's R5 seed with an `atomic: bool` op flag
(same shape as §4.3's volatile flag). The optimizer treats atomic ops
as opaque-region boundaries for memory reordering (ch05 R19 shape
applied by analogy, but WITHOUT the `unknown` class — the seed is kept,
so `split_at` halves through atomics still verify). Compiler reordering
is constrained operationally for the two backends:

- `seq_cst` ops: no memory op moves across them in either direction
  (compiler fence; hardware fence per target lowering).
- `acquire` (load/RMW/CAS): no later memory op hoists above.
- `release` (store/RMW/CAS): no earlier memory op sinks below.
- `relaxed`: atomicity only (no tearing, single total order per
  location... precisely: the op is indivisible; cross-location ordering
  is exactly none) — but still no elimination, no CSE across, no
  invented atomic accesses (same "no invention" rule as volatile §4.3).
- Exclusivity (ch01 Rules 6-7): atomic ops take the cell by `let` and
  therefore never conflict under the exclusivity check — same exemption
  as §4.2(4), and likewise grant no `noalias` fact.

### 5.4 Secret / CT interaction

Secret + atomic is REJECTED in v0.1: an `atomic[T]` field MUST NOT be
`secret`-typed, and no atomic op accepts a `secret` operand. Reasons:
(a) atomic RMW exposes timing (contention, CAS-failure loops branch on
the value — R6b's "branch on secret" fires on every CAS retry loop);
(b) the CT verifier's denylist (R15) for variable-latency instructions
covers locked ops on the v0.1 targets until measured
(ch05 Open question 1's conservative-ban default applies). Path forward
is an owner question (§9): audited lock-free CT primitives could arrive
as `@ct_audited` std primitives, but the spelling here stays closed.
`declassify` before the atomic op is the available (audited) escape.

### 5.5 Capability / `unsafe` interaction

- **No `unsafe`, no capability, no `needs` entry.** Atomics on `Shared`
  state are the SAFE concurrency primitive — that is ch01 Rule 21's
  entire point (safe sequential subset + `Shared` + atomics = the only
  interior mutability). Requiring `@unsafe` would invert the design:
  every `Shared` counter would be an audit item. The `Shared` field
  check (Rule 21a, same-module, or `@unsafe` escape hatch Rule 21c for
  the struct, not the op) is the complete gate.
- Sealed capabilities: none. Atomics emit locked instructions, not
  syscalls; ch04 Rule 4's scan sees no syscall-class encoding in them.

### 5.6 Trapping vs compile-error behavior

- **Compile errors:** omitted `order:`; illegal ordering for the op
  (§5.1 table); non-comptime ordering; non-`Copyable`/linear `T`;
  `atomic` outside a `Shared` impl field (ch01 Rule 21 — existing);
  atomic bit-field (rejected, §2.7); `Order` value used in non-atomic
  position (type error, `Order` is closed).
- **Traps:** none from the atomic op itself. Atomic ops do not trap on
  any value (wrapping/failure are data, not bugs: `fetch_add` wraps
  like `wrap_add` — two's complement, never `overflow`; CAS failure
  returns `false` + updates `expected`, never traps). Misuse that WOULD
  trap elsewhere (null cell address) cannot arise: cells are fields,
  not pointers. A data race on NON-atomic access to the same location
  is a checker exclusivity error (compile error, ch01 Rules 6-7/21d),
  not a trap — races never reach runtime in accepted programs.
- R17 note: `seq_cst` total order is per-execution; D1 determinism
  (ch03 Rule 10) does NOT promise identical racy outcomes across thread
  counts — it promises the PROGRAM's computed values are fixed, and a
  program whose output depends on a race is already outside D1's
  "fixed binary and input" contract only insofar as scheduling varies.
  Flagged in §9 as needing one owner sentence (not a contradiction, a
  scope line).

### 5.7 What stays explicitly out of v0.1

Fences as standalone ops (`fence(.seq_cst)`); success/failure split
orderings on CAS; `consume` ordering; release sequences as a named
concept; mixed-size atomics; `rawptr` atomics; double-width / 128-bit
atomics (ch03 Rule 1 already bans 128-bit); atomic + volatile on one
field; wait/notify (futex) surface (needs `syscall` + blocking design —
ch10 S0010(c) already defers blocking synchronization); `Order` values
computed at runtime; default ordering (deliberately absent — §5.1).

## 6. Pointer arithmetic rules

### 6.1 Proposed surface syntax

No operators (ch09 Rule 21 closed; §1). Movement is methods on
`rawptr[T]`, bounds come from the allocation the pointer was derived
from, and every derivation is explicit:

```fors
needs { };

fn sum(inout buf: Slice[i32]) -> i32 {
    let p: rawptr[i32] = buf.as_raw();      // base + bound captured once
    var acc: i32 = 0;
    var i: usize = 0;
    while i < buf.len {
        let q: rawptr[i32] = p.add(i);     // traps `bounds` if out of range
        acc = acc + q.read();
        i = i + 1;
    }
    return acc;
}
```

```fors
needs { };

@unsafe(invariant: "base..base+len is a mapped MMIO window for this target")
fn mmio_at(let base: rawptr[u8], let len: usize, let off: usize) -> rawptr[u32] {
    let b: rawptr[u8] = base.add(off);          // bounds-checked step
    return b.cast[u32]();                        // align-checked cast
}
```

Full method table on `rawptr[T]` (inherent impl, defining module
`std.mem` per ch10 S0002's nomination precedent):

- `add(let off: usize) -> rawptr[T]` — total signature (traps `bounds`
  when out of range; §6.6). A `raises BoundsError` alternative is REJECTED:
  bounds violations are ch02 Rule 15's `bounds` trap, and a `raises` form
  would let callers swallow a bug as data. There is no `?` handler anywhere
  in this section — a trap is not an error value (ch02 Rule 7 vs Rules 1-5).
- `offset(let n: isize) -> rawptr[T]` — signed back-step; same trap.
- `sub(let other: rawptr[T]) -> isize` — distance in ELEMENTS between
  two pointers into the SAME allocation; traps `bounds` otherwise
  (different allocations, or either dangling — §6.2 provenance).
- `read() -> T` / `write(sink v: T)` — `T: Copyable` only (same
  second-owner argument as ch10 S0022's `Own.get` — a `read()` of
  non-`Copyable T` would mint a second owner; the rawptr form is
  `exchange(inout p, sink v: T) -> T`.
- `cast[U]() -> rawptr[U]` — retype; traps `contract` on misalignment
  of the address for `U` (§6.6); provenance and bounds transfer
  unchanged (same allocation, byte range re-expressed).
- `as_raw()` constructors: `Slice[T].as_raw() -> (rawptr[T], usize)`
  (base, length in elements — Fors has tuples, so both come out in one
  value). `Array` likewise.
  `Block.bytes_raw` (ch10 S0015) already yields scoped slices; going
  from there through `as_raw` keeps one unsafe inventory entry per
  step (S0028 shape).

GRAMMAR: none (method calls with total signatures exist; no new production).

### 6.2 Typing / layout rules + provenance

1. `rawptr[T]` is sized one word (ch09 Rule 3: target pointer width),
   `Copyable`, never holding an obligation (ch01 Rule 22a lists it
   non-linear). Pointer arithmetic counts ELEMENTS of `T` (stride
   `sizeof(T)`), never bytes — byte stepping is `cast[u8]()` first (explicit
   and cost-visible: the stride multiplication is a real multiply, and
   overflow of `off * sizeof(T)` traps `overflow`, ch03 Rule 2 shape
   applied to the lowering's address computation).
2. **Provenance (the rule).** Every `rawptr[T]` value carries, at run
   time in the interpreter (Miri-class: `ProvId` in `Slot`,
   `fmir-interpreter.md` §5.1) and as compile-time metadata in OIR, a
   triple `(alloc-id, base-offset-range, T)`: the allocation it was
   derived from, the valid element range `[0, len)` captured at
   derivation (`as_raw` time), and its current type. `add`/`offset`
   preserve the triple, changing only the index. `cast[U]` preserves
   `(alloc-id, byte-range)` and re-expresses the index in `U` units
   (length = floor(bytes / sizeof(U)); a remainder is fine — the tail
   bytes are simply unaddressable as `U`, and `add` past them traps).
   Pointer INTEGER casts (`as usize` / from `usize`): **out of v0.1**
   (§6.7), with one `@unsafe`-only entry point:
   `rawptr.from_addr(addr: usize, len: usize) -> rawptr[u8]`, usable only
   inside a declaration carrying `@unsafe(invariant:)` (that declaration
   carrying the invariant), creating provenance-fresh `(alloc-id =
   unknown-external, [0, len))` — the `unknown` class (ch05 R19) at the
   value level. Integer-to-pointer without `@unsafe` is a compile error.
3. **Bounds.** Valid indices are `[0, len]` inclusive of one-past-end
   (`len` itself): forming the one-past-end pointer is legal, `read` /
   `write` through it traps `bounds`. `add`/`offset` producing an index
   outside `[0, len]` traps `bounds` AT THE ARITHMETIC, not lazily at
   dereference (eager — matches "anything a compiled program would get
   silently wrong, the interpreter names", §5.2's detection list; lazy
   OOB would let an OOB pointer be laundered through `cast` and back).
   `sub` requires same `alloc-id` and both indices in `[0, len]`; else
   traps `bounds`.
4. Null: `rawptr[T]` has no null literal in v0.1 (no `Option`-shaped
   pointer, no null constructor — absence is expressed as
   `Option[rawptr[T]]` (`Option` of a `Copyable` is `Copyable`, so
   `none` is the null-equivalent; there is no zero address value).
   never mapped — holds on both v0.1 targets; pinned per-target fact).
5. Brands (ch01 R15-R18): pointers derived from arena storage
   (`Arena[T, A]` bodies, `Block[A]` bytes) keep their brand in the TYPE
   system only while typed (`Ref`, `Slice`); once lowered to `rawptr`
   the brand is an OIR alias seed (`Arena(BrandId)`, §3.4a), and
   generation checks (ch01 Rule 17, `arena_deref` traps
   `arena-generation`) apply at the `Ref`/slice level BEFORE `as_raw`.
   A `rawptr` does not itself generation-check (it has no generation
   field — 8 bytes, one word, no fattening: no-hidden-cost). Use-after-
   `reset` through a stale `rawptr` is therefore `ub: use-after-free` in
   the interpreter (Miri diagnostic, exit 70 — NOT a program trap, §5.2
   shape) and undefined in compiled code. Stated loudly because it is
   the sharpest edge in this section: `rawptr` outlives the safety
   system by construction; the `@unsafe` inventory entry says so.

### 6.3 Alias-class interaction (ch05 R5)

`rawptr`-derived accesses carry seeds per R5 with two additions:

- Pointers from `as_raw` inherit the source's seed (`Split` side,
  `Arena` brand, `Own` root, or `Conv`).
- Pointers from `from_addr` (external/MMIO) carry `unknown` (ch05
  Rule 19: exactly the class for "pointers an opaque region receives";
  extended here to "pointers no typed derivation explains"). `unknown`
  aliases EVERYTHING: any memory op through an `unknown` pointer blocks
  reordering of every memory op across it (R19's "no pass MUST reorder
  a memory operation across the block", generalized to the access).
  This is conservative and deliberate — MMIO-adjacent code does not get
  clever scheduling.
- `read`/`write` through `rawptr` are ordinary OIR memory ops with
  alias-class + disjointness-set operands (R4); `--verify-each` rejects
  any lacking them. No exemption.

### 6.4 Secret / CT interaction

`read` of a `secret`-typed location yields `secret` (R6a propagation
through the only clearing-free load); `write` of a `secret` value
through a non-`secret`-typed `rawptr[U]` is rejected (R6a storage
rule — the POINTER's type carries the qualifier: `rawptr[secret u8]`
vs `rawptr[u8]`, qualifiers already compose on any type per ch09
Rule 9, so no new type form is needed). Pointer INDICES and offsets
(`off`, `n`, `len`) MUST NOT be `secret` (R6b: index/address from
secret — `p.add(secret_idx)` is a compile error; launder through
`declassify` inside `@unsafe` if the caller can prove data-independence,
 audited). `cast` preserves qualifiers (dropping `secret` in a cast is
a compile error; adding it is allowed... precisely: `rawptr[u8]` →
`rawptr[secret u8]` allowed (tainting up is safe), reverse rejected).
R15/R16: pointer-derived secret accesses join the surrounding
`ct_region` like any memory op; passes propagate unchanged.

### 6.5 Capability / `unsafe` interaction

- **`as_raw`, `add`, `offset`, `sub`, `read`, `write`, `cast`: safe
  declarations, NO `@unsafe`, NO capability.** They trap rather than
  lie (§6.6): bounds-checked arithmetic on a provenanced pointer cannot
  forge access to unowned memory, so it needs no audit entry. (This
  mirrors the `Slice` indexing precedent: `a[i]` traps `bounds`, needs
  no unsafe.)
- **`from_addr`: `@unsafe(invariant:)` REQUIRED** (declaration form,
  ch04 Rule 10; in the inventory). It invents provenance — the single
  unsafe act in this section.
- **Sealed capabilities: none required by pointer arithmetic itself.**
  `ffi` enters only when the pointer crosses to/from `extern` code
  (ch04 Rule 2a attributes that use to the calling module — orthogonal).
  `asm` enters only for `asm` blocks (Rule 22). No new sealed capability
  proposed.

### 6.6 Trapping vs compile-error behavior

- **Compile errors:** `add`/`offset`/`sub` with wrong operand types
  (non-`usize`/`isize`); `read`/`write` of non-`Copyable T` (use
  `exchange`); pointer-to-int / int-to-pointer casts outside `@unsafe`;
  `from_addr` outside `@unsafe`; `sub` across statically-distinct
  allocations where provable (e.g. two `as_raw` bases of different
  slices in one function — the checker rejects what it can prove, the
  runtime traps the rest); pointers to `atomic` cells: rejected
  (atomics move only by op, §5).
- **Traps:** OOB `add`/`offset` result → `bounds`; `sub` across
  allocations or on dangling indices → `bounds`; `read`/`write` through
  one-past-end or OOB → `bounds`; `cast[U]` on misaligned address →
  `contract` (alignment is an invariant of `U`, ch02 Rule 9 shape);
  `off * sizeof(T)` overflow in address computation → `overflow`
  (ch03 Rule 2 applied to the lowering — the multiply is a real op);
  `from_addr(0, _)` → `bounds`. All eight-kind-closed (ch02 R15).
- Interpreter (Miri side): provenance violations the compiled code
  cannot see (stale-after-`reset`, wrong-alloc `sub` with in-range
  indices) are `ub:` diagnostics (exit 70), never program traps —
  `fmir-interpreter.md` §5.2's split preserved.

### 6.7 What stays explicitly out of v0.1

Pointer-integer casts in safe code; fat pointers (slices stay
`(ptr, len)` tuples at this level — the built-in `Slice[T]` type is
unchanged, ch03 Rule 24); `sub` across allocations yielding garbage
(C-style UB — we trap); pointer comparison operators (`<` on pointers
is a compile error — use `sub` + integer compare; avoids provenance-
ordered-comparison semantics entirely); function-pointer arithmetic
(`fn` values are opaque, ch09 Rule 7); `rawptr` to `atomic` cells;
untagged `unknown`-to-typed narrowing without `cast` (every retype is
spelled); provenance freezing / `expose_addr` equivalents (no
pointer-identity observation at all — helps ch04 Rule 15's
no-address-observation tier-up proof).

## 7. Link sections + symbol visibility

### 7.1 Proposed surface syntax

One attribute for placement, existing `pub` for visibility (ch08
Rule 11), existing `extern` for language linkage:

```fors
needs { };

@link_section("RESET")
fn reset_handler() {
    loop_forever();
}
```

```fors
needs { };

@link_section("__DATA,__persistent")
var boot_count: u32 = 0;

@link_section(".noinit")
var frame_buf: Array[u8, 262144];
```

Full spelling:

- `@link_section("SPEC")` on `fn` declarations and on module-level
  `let`/`var`/`const` bindings with a fixed-size type. (`static` does not
  exist as a keyword: a module-level `let` with an initializer IS the
  static. Module-level `var` is allowed ONLY with `@link_section` — the
  one legal form of mutable statics — and access from functions is an
  ordinary place use checked by ch01 Rules 6-7 with the static treated as
  rooted at the module (lives forever, never moves). The alternative (no
  module-level `var` at all) is flagged OPEN in §9, Q-BIT-6, with this
  form as the recommendation.)
- SPEC grammar: if the string contains a comma, it is a Mach-O
  `segment,section` pair (`"__DATA,__persistent"`); otherwise it is an
  ELF section name (`".noinit"`, `"RESET"`). The compiler lowers per
  target (§7.2 mapping). Malformed SPEC (empty, leading/trailing comma,
  NUL bytes) is a compile error.
- Visibility: `pub` (existing) = global/external linkage; absent =
  module-local (hidden visibility, one
  object). No new keyword. `extern "c"` (existing `extern_fn_decl`)
  keeps its meaning (C language linkage + unmangled-or-target-mangled
  symbol); combined `@link_section` + `extern "c"` is legal (placed AND
  exported).

GRAMMAR: no production change (`attribute` exists; string-literal args
exist). One validity rule: `@link_section` on anything but a `fn` or a
module-level `let`/`var`/`const` is a compile error.

### 7.2 Typing / layout rules + Mach-O/ELF mapping

1. The attributed item's TYPE is unchanged (sections are not types).
   Fixed-size requirement: the item's size must be comptime-known
   (`Array[T, N]` with closed `N`, scalars, structs of fixed size —
   `Slice`, `Vec`, `Own`, `dyn` rejected on statics; a `Slice`-typed
   static would be a fat pointer to nowhere — compile error).
2. Initializer rules: `const` in a section must have a comptime
   initializer (ch04 Rules 11-14 — already required); module-level `let`
   likewise; `var` with `@link_section(".noinit")`-shaped SPEC
   (a SPEC denoting a NOBITS section, §7.2(3)) MUST have NO initializer
   (writing one is
   a compile error — initializers in NOBITS are silently dropped by
   linkers, the exact silent-wrong this draft forbids); `var` in a
   PROGBITS section MUST have one.
3. Mapping table (normative-shaped, per target):
   - ELF (`x86_64-*` Linux, and any future ELF target): SPEC used
     verbatim as the section name; flags derived: `fn` →
     `SHF_ALLOC|SHF_EXECINSTR`; `const`/`let` → `SHF_ALLOC`
     (+ `SHF_WRITE` iff mutable `var`); NOBITS iff the SPEC is `.noinit`
     or begins `.bss` — else PROGBITS. Entry in
     `.symtab` iff `pub`, else `LOCAL`.
   - Mach-O (`aarch64-apple-darwin`): SPEC must contain the comma
     (`segment,section`); a comma-less SPEC on a Mach-O target is a
     compile error suggesting the pair form ("did you mean
     `__DATA,__...`?"). `fn` in `__TEXT,__text`-default otherwise as
     given; mutability and NOBITS derived the same way (NOBITS iff the
     section component is `__bss`, `__common`, or starts `__noinit`).
     `pub` → global
     (`N_EXT`), else static.
   - Unknown target / unknown SPEC shape: compile error (never silent
     default section — a misplaced vector table that silently lands in
     `.text` is the failure mode being designed out).
4. Q1: section placement never changes size/align/offset of the item
   (Q1 computes layout; the linker places it). `Layout.of` unaffected.
5. R18: section contents are covered by the signed image hash like any
   bytes; DEBUG-ONLY sections (`__DWARF,...` / `.debug_*`) are never
   produced from `@link_section` (debug info stays in the companion
   artifact, R18 — `@link_section(".debug_x")` is a compile error).

### 7.3 Alias-class interaction (ch05 R5)

Statics in custom sections are ROOTS: a distinct alias seed per static
(`Own`-analogous root — same "an `Own[T, A]` root is its own seed"
shape, §3.4a table extended one row: `Static(DefId)`). Two different
statics never alias; a static never aliases an arena brand, a split
half, or a parameter convention class — EXCEPT `unknown`-class accesses
(§6.3), which alias everything including statics. `asm` blocks naming a
static's address take it as an `in` pointer operand (ch05 R19: declared
effect, `unknown` class for the pointer itself — the static's own seed
is not laundered through the block).

### 7.4 Secret / CT interaction

A `secret`-typed static is REJECTED (`secret` at fixed addresses +
linker-visible layout = silent exposure; R6a's storage rule
generalized: secret values live in the secret spill class (ch05
Rule 7) chosen by the allocator at spill time, never at a
linker-fixed address the image discloses). `secret` CODE (functions
handling secrets) in a custom section: allowed, keeps its secret bit
and `ct_region` (R6/R16 propagate through section placement
unchanged). No additional rule attaches to section names — section
names are not secret metadata. But: whole-image secret scrubbing
(Rule 8 zeroize-before-
epilogue) covers stack spills, not statics — a function that leaves
secret material in a custom-section static is a DEFECT in that function
(the CT inventory notes it; R15 cannot see the store's intent, which is
why the static-secret ban above is a checker rule, not a verifier one).

### 7.5 Capability / `unsafe` interaction

- **`@link_section`: `@unsafe(invariant:)` REQUIRED on the item.**
  Placing bytes at linker-controlled addresses breaks the compiler's
  placement assumptions (dead-stripping, ordering, NOBITS zero-fill) —
  publish the claim. In the unsafe inventory (ch04 Rule 9).
- **No sealed capability.** Sections are not authority (nothing
  executable is authorized by naming where it sits; ch04 Rule 4's scan
  still applies to every emitted byte regardless of section — holding
  `asm` does not exempt, lacking `syscall` still fails on syscall-class
  encodings WHEREVER they sit, vector table included).
- `needs`: no entry required by sections alone.

### 7.6 Trapping vs compile-error behavior

- **Compile errors (all of it — sections are fully static):**
  malformed SPEC; comma-less SPEC on Mach-O; `@link_section` on a local,
  parameter, field, or generic function (monomorphized copies in
  multiple sections would duplicate the symbol — generics + sections
  rejected; the error suggests a non-generic wrapper); non-fixed-size
  static type; missing/present initializer mismatch on NOBITS/PROGBITS
  (§7.2(2)); `pub` + `extern` + section conflicts the target cannot
  represent (named per target); duplicate symbol from two items lowered
  to one name in one section (linker would also fail — fail first, with
  the source sites); `@link_section` on a `main` function (entry symbol
  placement is the runtime's, not the program's).
- **Traps: none.** Section errors cannot be dynamic — anything here that
  survives to runtime is a compiler bug (`ub:`-class in the interpreter,
  exit 70).

### 7.7 What stays explicitly out of v0.1

Alignment-in-section (`align(N)` — with §3.7); section-relative
symbols / linker scripts / `KEEP()` / overlays; explicit symbol
versioning; `hidden`/`protected` visibility words (two-linkage model:
`pub` = global, absent = local — the complete v0.1 story);
`link_name` / rename attributes (symbol names are declaration names +
target mangling, fixed); `used`/`retain` anti-GC attributes (nothing is
stripped that is reachable; `@link_section` items are roots by
definition — stated so nobody files it as a bug); TLS / thread-local
statics (needs the threading model M3 has not built); mutable statics
without `@link_section` (see §7.1 open point — the ONLY mutable-static
form is section-placed, or none at all if the owner rejects `var`).

## 8. Naked functions

### 8.1 Proposed surface syntax

`@naked` on a `fn` declaration: no prologue, no epilogue, no frame, no
implicit spill — the body IS the machine state contract:

```fors
needs { asm };

@unsafe(invariant: "saves r0-r3 and cpsr before branching; restores on return")
@naked
fn irq_entry() {
    asm(aarch64) {
        "sub lr, lr, #4",
        "srsdb sp!, #31",
    };
}
```

```fors
needs { asm };

@unsafe(invariant: "forwards x0/x1 to supervisor call 7; preserves x2-x7 per AAPCS64")
@naked
fn trampoline(let a: u64, let b: u64) -> u64 {
    asm(aarch64) {
        in(x0) = a,
        in(x1) = b,
        out(x0),
        "svc #7",
    };
}
```

Full spelling: `@naked` composes with the existing attribute list
(order-free). A naked function keeps its `fn` signature (checked by
ch09 unchanged — conventions, `raises`, contracts all still parse and
all still constrain CALLERS). The body SHOULD be a single `asm` block
(possibly guarded by `comptime` target tests, ch04 Rule 24); anything
else is constrained per §8.2.

GRAMMAR: no production change. Validity is checker-side (attribute-
target + body-shape checks, ch04 Rule 10/22 shape).

### 8.2 Typing / layout rules — constraints, no-prologue contract

1. **No-prologue contract (the definition).** Codegen for a `@naked`
   function MUST emit: the symbol, then the body's instructions, then
   nothing. No stack-pointer adjustment, no frame record, no callee-
   saved spill, no return-address signing, no `check_pre`/`check_post`
   instrumentation inline (contracts are FORBIDDEN on naked declarations,
   §8.6: `pre`/`post` on a `@naked fn` is a compile error, since the check
   would need emitted code the contract forbids), no failure-ABI tag setup
   beyond what the
   body's own `asm` declares, no DWARF frame description beyond an
   "no-frame" marker (R18 companion stays truthful).
2. **Body constraints (compile errors, each named):**
   - No `defer`/`errdefer` (needs emitted pending bodies — there is no
     exit-edge emission in a naked body).
   - No `?`, no `raise`, no handler (`else |e|`) — error paths need ABI
     code the contract forbids. A naked function MUST NOT be declared
     `raises` (checker rejects the signature, not just the body).
   - No `spawn`/`parallel`/`parallel for`/`simd for` (need region setup).
   - No linear locals or `sink` parameters (obligations need discharge
     code; ch01 Rule 22h has nothing to attach to). Concretely: every
     parameter MUST be `let` of `Copyable` scalar/pointer type; `sink`,
     `inout`, `set` parameters are rejected; locals MUST all be
     `Droppable` (rigid-parameter bodies rejected — naked functions MUST
     NOT be generic, same ban as ch04 Rule 2a's sealed-op-in-generic
     rule, same reason: bytes must be emitted once, in the holder).
   - No `with arena`/`with allocator` (needs brand binding + scope code).
   - Calls to non-naked functions: REJECTED (a call needs the caller's
     frame to exist — it does not). Calls to other `@naked` functions,
     including tail-branch form, are likewise REJECTED (§8.7). The
     reachable callee set of a naked body is: `asm` blocks and nothing
     else.
   - `return expr;` with a value: allowed ONLY as the body's tail and
     lowered as "value already in the return register per the body's
     `asm out` contract" — the compiler emits no move. (A `return`
     anywhere else, or a tail value that is not exactly the `asm`
     block's `out`, is a compile error.)
3. **Signatures still check.** Parameter/return types obey ch09; the
   CALLER side is fully normal (argument conventions, `raises` mismatch
   — naked callees never raise so `?`/`else` on the call is a compile
   error, ch02 Rule 1 shape). `Layout.of` of the signature is unchanged.
4. **Q1:** naked functions have no frame layout to compute; Q1 untouched.

### 8.3 Alias-class interaction (ch05 R5)

A naked body contains only `asm` blocks, so R19 governs entirely: each
block is opaque with declared `in`/`out`/`clobber`, pointer inputs are
`unknown`, and no memory op is reordered across a block. The naked
function contributes no alias seed of its own (it owns no memory); its
CALLERS' seeds are unaffected by the call (a call to a naked function
is a compiler barrier for memory but NOT an `unknown`-taint source:
since the body can only touch memory through declared `asm` pointer
operands, and those are `unknown`, the call aliases everything reachable
through the pointer arguments passed in, and nothing else — same rule
as any `asm` call site, no special case).

### 8.4 Secret / CT interaction

A `secret`-typed parameter, return, or `asm in` of a naked function is
rejected UNLESS the declaration also carries `@ct_audited(by: "...")`
(ch04 Rule 26 + ch05 Rule 20 inventory, the same gate as ch04 Rule 26's
asm-secret rule). Reason: hand-written prologue-free code is unauditable
by the CT verifier's instruction-pattern rules (no spill slots to
classify, no frame zeroize point — Rules 7-8 have no purchase), so the
human audit (inventory entry keyed by declaration + architecture) is the
ONLY control. R15 still runs over the body's machine instructions where
patterns apply (branch-on-secret denylist inside the emitted bytes);
R16 propagation is trivial (one region, no boundary crossing).

### 8.5 Capability / `unsafe` interaction — is `unsafe` + sealed capability needed?

YES to both, and this is the strictest gate in the draft:

- **`@unsafe(invariant:)` REQUIRED** — the no-prologue contract suspends
  every codegen invariant the safe language relies on. No exception.
- **Sealed `asm` capability REQUIRED in the module's own `needs`**
  (ch04 Rules 1, 22 + Rule 2a's emission-in-holder ban: a naked function
  MUST NOT appear in a generic, cross-module-inlinable, or escaping-
  closure position, for the same per-object scan reason). The Rule 4
  machine-code scan covers naked bodies like any emitted bytes
  (syscall-class instruction without `syscall` in `needs` = build error,
  even — especially — in a vector table written naked).
- `needs { asm }` names the CAPABILITY (ch04 Rule 21's independence
  note: `use std...` for names, `needs` for authority — both written).
- Rationale stated once: naked is the one construct here that removes a
  COMPILER guarantee rather than adding a PROGRAM capability, so it
  takes the strongest gate. Any relaxation (e.g. naked without `asm`
  for pure-`extern`-jump stubs) is a follow-up RFC, not a silent
  carve-out.

### 8.6 Trapping vs compile-error behavior

- **Compile errors: everything in §8.2(2)** plus `@naked` on a generic
  function, on a trait method (required or provided), on `main`, on a
  closure; `@naked` without `@unsafe`; `@naked` in a module lacking
  `asm`; `pre`/`post`/`invariant` clauses on a naked declaration; wrong-
  architecture `asm` without a `comptime` target guard (ch04 Rule 24 —
  reused, and load-bearing here: a naked x86_64 stub compiled for
  aarch64 would assemble the wrong bytes with no frame to catch it).
- **Traps: none from the naked contract itself.** A naked body contains
  no compiler-emitted checks (that is the point), and nothing in v0.1's
  allowed body shape can trap: asm has no trap semantics — an `svc` that
  faults is a hardware exception, not a ch02 trap. The distinction is
  recorded because conflating them would corrupt R17 differential testing:
  hardware exceptions are outside the oracle's alphabet.

### 8.7 What stays explicitly out of v0.1

Naked-to-naked calls (even tail); naked methods (`self` needs a
receiver convention with frame assumptions — free functions only);
naked closures; naked generic functions; interrupt-handler argument
 ABI sugar (`@interrupt` with automatic state save — the invariant
string + hand-written asm IS the v0.1 story); naked + `raises`;
naked + contracts; naked + linearity; naked + `defer`; stack-probing /
red-zone control (no stack model is exposed at all — consistent with
there being no `alloca` surface); CFI / landing-pad interaction (no
unwinder exists, ch02 round-5 D4 — nothing to interact with).

## 9. Open owner questions (with recommendations)

Numbered Q-BIT-n. Each names the conflict, the recommendation, and what
blocks on it.

1. **Q-BIT-1 — Bit order on future big-endian targets (§2.2(7)).**
   No v0.1 conflict (both targets LE). RECOMMENDATION: adopt this draft
   with the LE rule pinned and the BE rule explicitly deferred; cover
   `Target{endian}` in the layout hash now (one line, `fors-fmir`
   `target_hash` already covers `Target` per §5.1/`fmir` §11 table).
   Blocks: nothing in v0.1.
2. **Q-BIT-2 — `reserved` zero-check shape (§3.6).** Conflict check vs
   R17: an implicit per-construction check would differ between
   `--serial-elide`/interp (which sees the construction) and release
   (which might fold it) — UNLESS the check is explicit source. This
   draft already resolves it by making validation an explicit std
   `validate` call (no implicit check = no divergence). RECOMMENDATION:
   confirm explicit-only; never add implicit reserved-checks even under
   `--secure`. Blocks: std `validate` API (follow-up, not this draft).
3. **Q-BIT-3 — Volatile: new sealed `mmio` capability? (§4.5).**
   Conflict check vs ch04 Definitions (sealed list closed at three) and
   R6b (secret-to-I/O already rejected without it). RECOMMENDATION: NO
   new sealed capability in v0.1 — `@unsafe` + inventory is sufficient;
   revisit only with evidence of driver-package confusion. Blocks:
   nothing.
4. **Q-BIT-4 — Secret + atomics ban (§5.4).** Conflict check vs R6 (no
   direct conflict — R6 permits the checker to reject MORE than the
   minimum; the minimum is branch/index/trapping-op rejection, and a
   CAS-retry loop IS a branch on the value, so the ban is R6b's
   consequence, not an extension). RECOMMENDATION: keep the ban; audited
   CT lock-free primitives arrive as `@ct_audited` std items later.
   Blocks: nothing in v0.1.
5. **Q-BIT-5 — D1 scope line for atomics (§5.6).** Apparent tension with
   ch03 Rule 10 (D1: bit-identical across thread counts): a program that
   races has schedule-dependent VALUES, which is not a compiler
   nondeterminism but reads like one. RECOMMENDATION: one owner sentence
   in ch03 ("D1 applies to the values of race-free programs; racy
   outcomes may vary by schedule and are outside the differential
   corpus") — no rule change, programs with races stay compilable but
   leave the oracle corpus (R17's "every accepted program" needs the
   same qualifier (either qualify R17 the same way or add racy programs
   to the differential corpus with schedule recorded — this draft
   recommends the qualifier; recording schedules is M3+ work). Blocks:
   M3 differential-corpus admission criteria.
6. **Q-BIT-6 — Module-level `var`: only with `@link_section`,
   or not at all? (§7.1).** Conflict check vs ch01 (no rule forbids
   module-level bindings today because none exist in the grammar —
   `decl` has no static form; this is really a ch07/ch08 question) and
   vs S0010(c) (no locks/channels — mutable statics without them invite
   races the checker cannot see... though `Shared`-gating was sketched
   and then withdrawn in §7.1 for simplicity). RECOMMENDATION: allow
   module-level `var` ONLY with `@link_section` (so every mutable
   static is placed, named, and audit-listed), with plain place-use
   access; revisit `Shared`-gating if M3's race checker wants it. Blocks:
   ch07 `decl` + ch08 items (follow-up RFC owns the grammar delta).
7. **Q-BIT-7 — Q1 vs bit-field intra-unit order: is LSB-first a Q1
   violation?** Strict reading of Q1 ("fields in declaration order")
   could be taken to mean bit order too — in which case §2.2(3)'s
   refinement ("Q1 holds at unit granularity") needs Q1's text to say
   so. RECOMMENDATION: one sentence in Q1's adoption ("within a
   bit-field storage unit, bit order is LSB-first in declaration order
   on little-endian targets") — no semantic change, removes the
   ambiguity a reviewer will otherwise file. Blocks: Q1 adoption text
   (this draft is consistent either way once the sentence exists).
8. **Q-BIT-8 — R6 vs §2.4's secret-RMW claim.** R6a says aggregate
   secret covers every field; whole-unit RMW on a secret struct touches
   adjacent-field bits in one masked op — is that "an operation with a
   secret operand" whose fixed mask leaks field-boundary TIMING? No
   branch exists, so R6b does not fire; R15 sees a fixed-latency masked
   op. RECOMMENDATION: confirm allowed (this draft's stance); the CT
   denylist (ch05 Open question 1's conservative default) remains free
   to ban variable-latency masked ops per target without touching this
   rule. Blocks: nothing (denylist is measurement-gated anyway).
9. **Q-BIT-9 — `from_addr` and ch04 Rule 15 (no address observation for
   comptime tier-up).** A `from_addr` inside comptime-evaluated code
   observes an address by construction. RECOMMENDATION: comptime
   evaluation reaching `from_addr` is a build error (same shape as
   ch04 Rule 2a's "comptime reaching a sealed operation" — extend the
   predicate one entry, no new mechanism). Blocks: nothing in v0.1
   (comptime + MMIO is nonsense code; the error just says so early).
10. **Q-BIT-10 — Naked + R17 differential testing.** Naked bodies are
    target-asm; the interpreter CANNOT execute them bit-identically
    (no oracle). Conflict check vs R17 ("both backends and the
    interpreter MUST produce bit-for-bit identical output on every
    accepted program..."). RECOMMENDATION: qualify R17 with "programs
    containing `@naked` functions or `asm` blocks with
    target-specific behavior are excluded from the differential corpus
    beyond --verify-each acceptance" (asm already needs this qualifier
    in practice — naked only makes it explicit). Blocks: M2 R17 gate
    wording.

Count: **10 open questions**, all with recommendations. No Q1/R6
contradiction found that this draft does not already resolve in-text;
Q-BIT-5, Q-BIT-7, Q-BIT-10 are scope/wording qualifications on ch03-R10,
Q1, ch05-R17 respectively — flagged as questions (not silent edits)
because each touches normative text only an approved RFC may change.

## 10. Conformance-test sketches (non-normative, for the RFC's test plan)

- `bitfield_layout_matches_q1`: `Layout.of[Packed]()` size/align equal
  hand-computed Q1+§2.2 values; field reads/writes round-trip.
- `bitfield_overflow_traps`: `r.mode = 1u32 << 4` on a `:2` field traps
  `checked-conversion`; `wrap_set` yields truncation, never traps.
- `bitfield_not_a_place`: `&r.mode`, `&out r.mode`, `move r.mode`
  rejected naming the field.
- `bitfield_secret_cover`: secret struct's bit-field read is secret;
  storing non-secret into it rejected; secret narrowing uses `wrap_`.
- `pad_kept_not_merged`: struct with `pad[4]` where alignment needs 0
  still has `Layout.size` including all 4; `--verify-each` accepts.
- `reserved_zero_invariant`: nonzero `reserved` via wire-copy +
  missing `validate` → later `contract` trap at the explicit check
  site, never silent; reading `reserved` rejected in the checker.
- `volatile_exactly_once`: one source read = one hardware-width access
  (backend counter test); dead `volatile_load` not eliminated; no
  speculative volatile read on untaken branch.
- `volatile_secret_rejected`: secret-typed volatile field / secret
  through `volatile_load` rejected without `@ct_audited`.
- `atomic_ordering_required_and_checked`: omitted `order:` rejected;
  `load` with `.release` rejected naming op + ordering.
- `atomic_no_trap_wraps`: `fetch_add` past max wraps (never
  `overflow`); CAS failure returns `false` + updates `expected`.
- `ptr_add_traps_bounds`: `p.add(len)` forms one-past-end (legal);
  `p.add(len + 1)` traps `bounds`; deref of one-past-end traps.
- `ptr_sub_cross_alloc_traps`: `sub` across two slices' bases traps
  `bounds` at runtime (or rejected statically where provable).
- `ptr_cast_misaligned_traps_contract`: misaligned `cast[U]` traps
  `contract`.
- `link_section_elf_names`: `@link_section(".noinit")` ELF object has
  the symbol in `.noinit` NOBITS, LOCAL unless `pub`.
- `link_section_macho_pair`: comma-less SPEC on Mach-O target rejected
  with the pair-form hint.
- `naked_no_prologue_bytes`: object bytes of a `@naked` fn contain no
  frame setup (target-specific byte check, dev backend only).
- `naked_rejects_high_level_body`: `?`, `defer`, `spawn`, generic,
  `raises` on naked each rejected with its own diagnostic.
- `naked_requires_unsafe_and_asm`: missing `@unsafe` or missing `asm`
  in `needs` each rejected.

## 11. What this draft does NOT do (v0.1 boundary, consolidated)

Unions; `:0`; signed bit-field bases; split-unit fields; `align(N)` /
`packed`; named padding; `pad_bits`; volatile bit-fields/aggregates/
`volatile_copy`; standalone fences; CAS split orderings; `consume`;
`rawptr` atomics; 128-bit atomics; futex/wait-notify; safe int↔ptr
casts; pointer comparisons; `link_name`; visibility beyond
pub/local; linker scripts; TLS; `@interrupt` sugar; naked calls,
methods, generics, `raises`, contracts, linearity. Each item names its
section above; none is implied "later" beyond being listed here.
