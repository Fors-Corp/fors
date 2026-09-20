# Fors spec-in-context pack

GENERATED FILE — do not hand-edit; run `tools/specpack/gen.py --write` to
regenerate. Source: `docs/spec/*.md` (normative), `tests/conformance/`
(corpus) and `std/**/*.fors` (standard library).

Language version: 0.5.0 (`docs/spec/VERSION`)
Inputs SHA-256: 2e695cf11a733348fe7c9eedc145c31ae3e1b89e5e9effb93626e8616e766ade

This pack exists because no model has seen Fors before: guessing from
Rust/Zig/Swift/C is wrong more often than it is right. Read section 1 first.
`fors check` is the arbiter of what compiles, never this file.

## Contents

1. Orientation
2. Grammar
3. Rule index
4. Standard-library surface
5. Complete examples
6. Common mistakes
7. Tools

## 1. Orientation

Fors is a systems language with explicit ownership conventions, capability-based
authority, and a single-pass type checker (no solver, no implicit conversions,
no overloading). It looks nearest to Rust/Zig/Swift on the surface but differs
in the ways below; every quote is a real, contiguous span of an ACCEPTED file
under `tests/conformance/`, never invented. `fors check` is the arbiter, not this pack.

**Semicolons are mandatory; there is no ASI.** `let`/`var`, assignment, expression,
`return`, `raise`, `break`, `continue`, `discard`, `consume` and `spawn` statements each end in `;`.
A statement whose body is a block — `if`, `match`, `for`, `while`, `with`, `parallel`, a bare block,
`defer { }`/`errdefer { }` — takes NO `;`, and writing one is a parse error.
<!-- from: tests/conformance/01-ownership/conv-move-present-accepted.fors -->
```fors
fn consume_box(sink b: Box) {
    discard b;
}
```
**A pattern binds a name only via `let name`; a bare name in a pattern is always a reference, not a binding.** `some(let v)` binds `v`; `none` below is the prelude value, referenced (and may repeat across arms).
<!-- from: tests/conformance/08-names/pattern-prelude-value-reference-accepted.fors -->
```fors
    match a {
        none => 0,
        some(let v) => match b {
```
**Every function parameter declares a convention — `let`, `inout`, `sink`, `set` — and a call site marks a non-`let` argument to match: `&x` (inout), `move x` (sink), `&out x` (set); a method receiver alone never carries a marker.**
<!-- from: tests/conformance/01-ownership/conv-move-present-accepted.fors -->
```fors
fn use_it(sink b: Box) {
    consume_box(move b);
}
```
**Generic parameters go in `[...]`, never `<...>`.**
<!-- from: tests/conformance/07-grammar/bracket-roles-accept-2.fors -->
```fors
struct A[T] { v: T }
```
**A std module needs an explicit `use std.<name>;`; the prelude holds only types, values and traits, never a module** — `io.Stdout` is unreachable without importing `std.io` first.
<!-- from: tests/conformance/04-authority/needs-declared-accepted-run-ok.fors -->
```fors
needs { io.stdout };
use std.io;
```
**Heap-allocating std types take an explicit allocator value — there is no ambient allocator — and the root heap arrives as a parameter of `main`.**
<!-- from: tests/conformance/10-std/main-heap-parameter-accepted.fors -->
```fors
fn main(inout heap: mem.Heap) raises AllocError {
    var b: Own[i64, heap] = heap.create(7)?;
    heap.deinit(move b);
}
```
**Authority (`io`, `fs`, `net`, ...) enters ONLY as typed parameters of `main`, never an ambient "world" value; a module using a capability declares it in `needs { ... };`.**
<!-- from: tests/conformance/04-authority/main-signature-correct-accepted-run-ok.fors -->
```fors
needs { io.stdout };
use std.io;

fn main(inout out: io.Stdout) {
```
**No shadowing, anywhere — except a function-local binding may shadow a prelude name.** A local named `none` is legal and denotes the local, not the prelude value, inside its scope.
<!-- from: tests/conformance/08-names/local-shadows-prelude-value-accepted.fors -->
```fors
fn f() -> i32 {
    let none: i32 = 7;
    return none;
}
```
**An unsuffixed integer literal defaults to `i32`; indexing (Bracket, range, `Slice`) is `usize`-only regardless of that default.**
<!-- from: tests/conformance/03-numerics/slice-range-index-accepted.fors -->
```fors
    let s: Slice[i64] = data[0 ..< 3];
```
**Operators are homogeneous: `Add`/`Sub`/... take and return the SAME type, with no `Output` associated type and no mixed-type arithmetic.**
<!-- from: tests/conformance/09-types/operator-via-impl-accepted.fors -->
```fors
fn f(let a: V2, let b: V2) -> V2 { return a + b; }
```
**Bitwise `&`/`|`/`^` sit on their own flat tier: mixing one with arithmetic, comparison, or a DIFFERENT bitwise operator needs explicit `( )`** (a same-operator chain like `a | b | c` needs none).
<!-- from: tests/conformance/07-grammar/bitwise-accept-parenthesized.fors -->
```fors
    let r1 = (a + b) & c;
    let r2 = a | b | c;
    let r3 = (a & m) != 0;
```
**Failure is `raises T` on the signature, postfix `?` to propagate, and `raise expr;` to throw — no exception type, no `try`/`catch`. A trap aborts the whole process; nothing catches it.**
<!-- from: tests/conformance/10-std/main-raises-exit-status-one-run-error.fors -->
```fors
fn main() raises Error {
    raise Error.boom;
}
```
**A `Linear` value MUST be consumed on every path out of its scope — moved, or cleaned up, commonly via `defer`/`errdefer`, which run in reverse order at scope exit (`errdefer` only on an error exit).**
<!-- from: tests/conformance/01-ownership/defer-runs-on-return-run-ok.fors -->
```fors
    defer out.write_line("cleanup");
    out.write_line("body");
    return 1;
```
**Iterator adaptors and consumers are ordinary PROVIDED METHODS of `Iterator`, so they chain like `it.map(f).take(3)`; there is no free-function `map`/`filter`/`take`.**
<!-- from: tests/conformance/10-std/adaptor-chain-accepted.fors -->
```fors
fn f[A: brand](let v: Vec[i32, A]) -> usize {
    return v.iter().map(double).filter(small).take(3).count();
}
```
**`x.finish()` on a `sink self` method moves the named receiver `x` with no marker — the one call site that never writes `move`.**
<!-- from: tests/conformance/09-types/implicit-receiver-move-accepted.fors -->
```fors
fn f(sink b: Builder) -> i64 { return b.finish(); }
```

## 2. Grammar

### Keywords — reserved (never identifiers)

`module use pub fn struct enum trait impl const extern let var inout sink
if else match for in while break continue return raise raises with
parallel simd spawn comptime move consume discard defer errdefer as and or
not true false
iso imm secret dyn asm type` and `_`. (`type` is reserved since owner decision
2026-09-19, round 4: it introduces an associated type inside a `trait` or
`impl` body and has no other production; no field, binding, path segment or
label may be spelled `type`.) Reserved without a production (future use):
`import recover spmd kernel`.

Reserved-unused words, in one place (they lex as their own token and are
rejected wherever an `ident` is expected — binding, field, member, path
segment, label, module name — but no production mentions them):

| Word | Status | Why reserved now |
|---|---|---|
| `import` | reserved-unused | `use` is the import keyword; un-reserving later is compatible, reserving later is not |
| `recover` | reserved-unused | ch01 open question 2: a possible future *ownership qualifier* (a Pony-style `recover` that promotes to `iso`, which ch01 Rejected alternatives dropped). It has NOTHING to do with trap recovery: ch02 Rule 7 (round 5, D4) reserves no domain-recovery boundary of any kind |
| `spmd` | reserved-unused | the SPMD region of ch01/ch03 (M6); owner decision 2026-09-19, round 5, D2 |
| `kernel` | reserved-unused | the device-kernel region of ch01/ch03 (M9); owner decision 2026-09-19, round 5, D2 |

Not reserved, ordinary identifiers resolved by the checker: `reduce`
(`reduce(...)`, `reduce.serial`), `unsafe` and every other attribute name,
`self`, `some`, `none`, `identity`, `order`, capability names, primitive
type names (`u8`, `vector`, `mask`, `rawptr`).

### Keywords — contextual

Each is an identifier token everywhere; it acts as a keyword only in the
one slot listed. "LA" is the number of tokens inspected, counting the
current one.

| Word | Slot | How it is recognised | LA |
|---|---|---|---|
| `contracts` | file header, before any `decl` | a `decl` never starts with an identifier other than `soa`; identifier here = header clause | 1 |
| `needs` | file header, before any `decl` | same | 1 |
| `inputs` | file header, after `needs`, before any `use_decl`/`decl` | same | 1 |
| `soa` | start of a `decl` | same; must be followed by `struct` | 1 |
| `set` | first token of a `param` / `fparam` | a convention is mandatory there, so the first token is always the convention | 1 |
| `set` | first token of a closure `cparam` | convention iff the next token is an identifier or `_` | 2 |
| `brand` | `gparam` bound, right after `:` | that slot means the kind; a trait named `brand` cannot be a bound | 1 |
| `scoped` | start of a `ret_type` (element) | prefix iff next token is `(`; a type path is never followed by `(` | 2 |
| `arena`, `allocator` | right after `with` | `with` has no other form | 1 |
| `pre`, `post`, `invariant` | signature tail (after `params`/`ret_type`/`raises` clause); `invariant` also struct header tail | an identifier cannot follow a complete type or expression, so an identifier there is the clause word | 1 |
| `grain` | after the iterable of `parallel for` | same argument | 1 |
| `out` | right after the marker `&` at the start of an `arg_value` | set-marker iff the token after `out` is an identifier; `&out)`, `&out.f`, `&out[i]` are the inout marker on a binding named `out` | 2 |
| `out`, `clobber` | start of an `asm_item` | Disambiguation 16: current token `in` selects the `in(...)  = expr` item; `out`/`clobber` followed by `(` selects that item; otherwise the item is a `string_lit` | 2 |

`identity`, `order` and `invariant` inside `@unsafe(invariant: "...")` are
plain labels of a named argument (`ident ":"`), not keywords.

## Operator table

Highest binding first. Every operator used in ch01-06 appears here.

| Level | Operators | Assoc | Operands |
|---|---|---|---|
| 1 postfix | call `f(...)` with optional `else \|e\| { }` handler, Bracket `x[...]`, `.name`, `?` | left | primary |
| 2 prefix | `-`, `move` | right | level 1-2 |
| 3 | `as Type` | left | level 2 |
| 4 | `*` `/` `%` | left | level 3 |
| 5 | `+` `-` | left | level 4 |
| 6 | `..<` `..=` | none (single use) | level 5 |
| 7a | `==` `!=` `<` `>` `<=` `>=` | none (no chaining) | level 6 |
| 7b | `&`, `\|`, `^`: chain of ONE repeated operator; `<<`, `>>`: single use | flat | level 3 only |
| 8 prefix | `not` | right | level 7-8 |
| 9 | `and` | left | level 8 |
| 10 | `or` | left | level 9 |

Levels 7a and 7b are alternatives, not a ladder: a bitwise expression is
never an operand of levels 4-7a, and its own operands are level 3, so any
mix of a bitwise operator with arithmetic, range, comparison or a
*different* bitwise operator needs `( )`. This is `cmp_expr`/`bit_expr` in
the EBNF, not a checker rule. Not expression operators: `=` and the
compound assignments (statement only, not chainable); the call-site markers
`&` and `&out` (start of an `arg_value` only); `->`, `=>`, `:`, `@`.

```ebnf
(* ---- file ---- *)
file            = [ module_hdr ] [ contracts_clause ] [ needs_clause ]
                  [ inputs_clause ] { use_decl } { decl } ;
module_hdr      = "module" path ";" ;
contracts_clause= "contracts" ":" dot_lit ";" ;
needs_clause    = "needs" "{" [ needs_item { "," needs_item } [ "," ] ] "}" ";" ;
needs_item      = path | "asm" ;   (* the capability `asm` is spelled with the
                                      reserved word; legal only as a whole item *)
inputs_clause   = "inputs" "{" [ string_lit { "," string_lit } [ "," ] ] "}" ";" ;
use_decl        = [ "pub" ] "use" use_item { "," use_item } ";" ;
use_item        = path [ "as" ident ] ;
path            = ident { "." ident } ;
dot_lit         = "." ident ;

(* ---- declarations ---- *)
decl            = { attribute } [ "pub" ]
                  ( fn_decl | extern_fn_decl | struct_decl | enum_decl
                  | trait_decl | impl_decl | const_decl ) ;
attribute       = "@" ident [ "(" [ attr_arg { "," attr_arg } [ "," ] ] ")" ] ;
attr_arg        = [ ident ":" ] ( literal | path ) ;

fn_decl         = fn_sig block ;
fn_sig          = "fn" ident [ generics ] params [ "->" ret_type ]
                  [ "raises" type ] { contract } ;
extern_fn_decl  = "extern" string_lit fn_sig ";" ;
generics        = "[" gentry { "," gentry } [ "," ] "]" ;
gentry          = gparam | gconstraint ;        (* Disambiguation 19 *)
gparam          = ident [ ":" ( "brand" | bounds ) ] ;
gconstraint     = ident "." ident ":" bounds ;  (* introduces no name *)
bounds          = type { "+" type } ;
params          = "(" [ param { "," param } [ "," ] ] ")" ;
param           = convention ident ":" type
                | convention "self" ;          (* Disambiguation 21 *)
convention      = "let" | "inout" | "sink" | "set" ;
contract        = ( "pre" | "post" | "invariant" ) expr_ns ;

struct_decl     = [ "soa" ] "struct" ident [ generics ]
                  { "invariant" expr_ns }
                  "{" [ field { "," field } [ "," ] ] "}" ;
field           = [ "pub" ] ident ":" type ;
enum_decl       = "enum" ident [ generics ]
                  "{" evariant { "," evariant } [ "," ] "}" ;
evariant        = ident [ "(" type { "," type } [ "," ] ")"
                        | "{" field { "," field } [ "," ] "}" ] ;
trait_decl      = "trait" ident [ generics ] "{" { trait_item } "}" ;
trait_item      = { attribute } fn_sig ( block | ";" )
                | assoc_type_decl ;             (* Disambiguation 20 *)
assoc_type_decl = "type" ident [ ":" bounds ] ";" ;
impl_decl       = "impl" [ generics ] type [ "for" type ]
                  "{" { impl_item } "}" ;
impl_item       = { attribute } [ "pub" ] fn_decl
                | assoc_type_def ;              (* Disambiguation 20 *)
assoc_type_def  = "type" ident "=" type ";" ;
const_decl      = "const" ident ":" type "=" expr ";" ;

(* ---- statements ---- *)
block           = "{" { stmt } [ expr ] "}" ;
stmt            = let_stmt | if_expr | match_expr | comptime_block
                | for_stmt | while_stmt | break_stmt | continue_stmt
                | return_stmt | raise_stmt | with_stmt | parallel_stmt
                | parallel_for_stmt | simd_for_stmt | spawn_stmt
                | consume_stmt | discard_stmt | defer_stmt | errdefer_stmt
                | attr_block_stmt | block
                | assign_stmt | expr_stmt ;
let_stmt        = ( "let" | "var" ) binding [ ":" type ] [ "=" expr ] ";" ;
binding         = ident | "_" | "(" binding { "," binding } [ "," ] ")" ;
assign_stmt     = expr assign_op expr ";" ;     (* left side: Disambiguation 9 *)
assign_op       = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|="
                | "^=" | "<<=" | ">>=" ;
expr_stmt       = expr ";" ;
for_stmt        = "for" binding "in" expr_ns block ;
while_stmt      = "while" expr_ns block ;
break_stmt      = "break" ";" ;
continue_stmt   = "continue" ";" ;
return_stmt     = "return" [ expr ] ";" ;
raise_stmt      = "raise" expr ";" ;
with_stmt       = "with" ( "arena" | "allocator" ) ident ":" type block ;
parallel_stmt   = "parallel" block ;
parallel_for_stmt = "parallel" "for" binding "in" expr_ns
                  [ "grain" expr_ns ] block ;
simd_for_stmt   = "simd" "for" binding "in" expr_ns block ;
spawn_stmt      = "spawn" expr ";" ;
consume_stmt    = "consume" place ";" ;
discard_stmt    = "discard" place ";" ;
defer_stmt      = "defer" ( block | expr ";" ) ;
errdefer_stmt   = "errdefer" ( block | expr ";" ) ;
attr_block_stmt = attribute block ;

(* ---- expressions ---- *)
expr            = or_expr ;
or_expr         = and_expr { "or" and_expr } ;
and_expr        = not_expr { "and" not_expr } ;
not_expr        = "not" not_expr | cmp_expr ;
cmp_expr        = bit_expr
                | range_expr [ cmp_op range_expr ] ;
cmp_op          = "==" | "!=" | "<" | ">" | "<=" | ">=" ;
bit_expr        = cast_expr ( "&" cast_expr { "&" cast_expr }
                            | "|" cast_expr { "|" cast_expr }
                            | "^" cast_expr { "^" cast_expr }
                            | ( "<<" | ">>" ) cast_expr ) ;
range_expr      = add_expr [ ( "..<" | "..=" ) add_expr ] ;
add_expr        = mul_expr { ( "+" | "-" ) mul_expr } ;
mul_expr        = cast_expr { ( "*" | "/" | "%" ) cast_expr } ;
cast_expr       = unary_expr { "as" type } ;
unary_expr      = ( "-" | "move" ) unary_expr | postfix_expr ;
postfix_expr    = primary_expr { postfix_op } ;
postfix_op      = "?" | "." ident | call | bracket ;
call            = "(" [ arg { "," arg } [ "," ] ] ")" [ handler ] ;
handler         = "else" "|" ident "|" block ;
bracket         = "[" [ bracket_arg { "," bracket_arg } [ "," ] ] "]" ;
bracket_arg     = kw_type | expr ;              (* Disambiguation 11 *)
arg             = [ ident ":" ] arg_value ;
arg_value       = "&" [ "out" ] place | bare_op | expr ;
place           = ident { "." ident | bracket } ;
bare_op         = "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<"
                | ">>" | cmp_op | "and" | "or" ;

primary_expr    = literal | struct_lit | path | tuple_or_paren | array_lit
                | closure | if_expr | match_expr | comptime_block | asm_expr ;
literal         = number | string_lit | multiline_str | dot_lit
                | "true" | "false" ;
struct_lit      = path [ bracket ] "{" [ finit { "," finit } [ "," ] ] "}" ;
finit           = ident ":" expr ;
tuple_or_paren  = "(" [ expr { "," expr } [ "," ] ] ")" ;
array_lit       = "[" [ expr ( ";" expr | { "," expr } [ "," ] ) ] "]" ;
closure         = "|" [ cparam { "," cparam } [ "," ] ] "|" ( block | expr ) ;
cparam          = [ convention ] ( ident | "_" ) [ ":" type ] ;
if_expr         = "if" expr_ns block [ "else" ( if_expr | block ) ] ;
match_expr      = "match" expr_ns "{" { arm } "}" ;
arm             = pattern "=>" ( block | expr ) [ "," ] ;
                  (* the "," may be omitted only after a block body or
                     before the closing "}"; a body starting with "{" is
                     always a block *)
comptime_block  = "comptime" block ;
asm_expr        = "asm" "(" ident ")" "{" asm_item { "," asm_item } [ "," ] "}" ;
asm_item        = "in" "(" ident ")" "=" expr
                | "out" "(" ident ")"
                | "clobber" "(" ident { "," ident } ")"
                | string_lit ;                  (* Disambiguation 16 *)

pattern         = "_" | [ "-" ] number | string_lit | "true" | "false"
                | dot_lit [ payload ] | path [ payload ] | "let" ident
                | "(" [ pattern { "," pattern } [ "," ] ] ")" ;
payload         = "(" pattern { "," pattern } [ "," ] ")"
                | "{" fpat { "," fpat } [ "," ] "}" ;
fpat            = ident ":" pattern | "let" ident ;

(* ---- types ---- *)
type            = { qualifier } type_core ;
kw_type         = type ;       (* a type whose first token is iso, imm,
                                  secret, fn or dyn *)
qualifier       = "iso" | "imm" | "secret" ;
type_core       = type_app | tuple_type | fn_type | dyn_type ;
type_app        = path [ "[" targ { "," targ } [ "," ] "]" ] ;
targ            = type | const_arg ;            (* Disambiguation 11 *)
const_arg       = add_expr ;
tuple_type      = "(" [ type { "," type } [ "," ] ] ")" ;
fn_type         = "fn" "(" [ fparam { "," fparam } [ "," ] ] ")"
                  [ "->" type ] [ "raises" type ] ;
fparam          = convention type ;
dyn_type        = "dyn" type_app ;
ret_type        = [ "scoped" "(" ident ")" ] { qualifier }
                  ( type_app | fn_type | dyn_type
                  | "(" [ ret_type { "," ret_type } [ "," ] ] ")" ) ;
```

## 3. Rule index

One line per numbered rule of chapters 01-06 and 08-10 (chapter
07's grammar is reproduced verbatim in section 2 instead): the
diagnostic-code-shaped citation, two spaces, its first sentence
truncated at 220 characters.

```
O0001  Every parameter MUST declare exactly one convention.
O0002  A call site MUST mark a non-`let` argument: `&x` (inout), `move x` (sink), `&out x` (set); `let` carries no marker.
O0003  A `let` parameter MUST NOT be assigned to or moved from.
O0004  A `sink` parameter MUST be moved-from or deinitialized on every path, unless `Copyable`.
O0004a  Moves and liveness (the rule the implicit receiver move of Rule 2 leans on; it applies identically to `move p` and to `p.m()` with `m` a `sink self` method).
O0005  A `set` parameter MUST be fully initialized on every return path.
O0006  Exclusivity is one forward dataflow pass per function over projection paths, no fixpoint, no interprocedural analysis; a callee's effect on an argument is exactly its declared convention.
O0007  Two simultaneous overlapping accesses MUST be rejected if either is `inout`, `sink`, or `set`.
O0008  At a CFG merge every path MUST agree on each local's liveness; disagreement MUST be an error, resolved by explicit `consume x` / `discard x` (no drop flags).
O0009  Inside a region with induction variable `i`, a varying store to an `inout` slice at index `e` MUST be accepted iff `e` is `i` or an affine `a*i+b` with compile-time-constant, nonzero `a`; any other index MUST be rejec...
O0010  There are exactly two sharing qualifiers, `iso` and `imm`; `mut`/`ro` MUST NOT exist — `inout`/`let` already cover them.
O0011  Reading a field of an `imm` value MUST yield `imm` (deep immutability).
O0012  An `iso` binding MUST be extracted only by `move`; the source MUST then be dead.
O0013  Sendability (the one rule).
O0014  `secret` MUST NOT be a sharing qualifier and MUST NOT join with `iso`/`imm`; it composes orthogonally (`iso secret T` is legal).
O0015  `with arena x: Arena[T] { ... }` and `with allocator x: Alloc { ... }` are statements (they yield no value).
O0015a  `Arena[T, A]` and every allocator type MUST have no constructor: a value of such a type exists only as the binding of a `with` block.
O0015b  The omitted brand argument (`Arena[Node]`, `PageAllocator`) is legal only in the `with` header; every other use of a branded type MUST write its brand argument.
O0015c  A `with` block re-entered (loop, recursion) reuses the same static brand.
O0015d  A generic parameter MAY have the kind bound `brand` (`fn insert[A: brand](...)`, `struct Tree[A: brand] { root: Ref[Node, A] }`).
O0015e  Brands are erased after checking: a brand argument MUST NOT be part of an instantiation shape or cache key, MUST NOT cause a separate monomorphized body, and has no witness table or witness-table slot (ch03 Rules 16-17).
O0016  `Ref[T, A]` MUST be usable only against an `Arena[T, A]` with the equal brand `A` (plain type equality, checked per call, no interprocedural analysis); any other use MUST be a compile error.
O0017  Every arena MUST carry a generation counter bumped on `reset`; every `Ref` dereference MUST be generation-checked in every build mode, never elided by optimization level.
O0018  `Own[T, A]` MUST record its producing allocator's brand `A`; `deinit` with an allocator whose brand differs from `A` MUST be a compile error.
O0019  A function MAY return a scoped value iff every scoped derivation in that return flows from exactly one designated parameter `p`, named by a `scoped(p)` return-type prefix; `p` MUST have convention `let` or `inout` (ne...
O0019a  At the call site, the access to the designated argument (with `p`'s convention) MUST extend to the end of the lexical scope of the binding that receives the scoped result (or to an earlier explicit `discard`).
O0019b  Two range/index projections of the same path are treated as overlapping by Rule 7 regardless of their bounds; disjoint sub-views exist only as results of stdlib split primitives, which are `@unsafe(invariant: "...")`...
O0019c  **Scope inheritance through a call** (round 6, O3; generalised by the round-6 verification).
O0019d  **Closure captures** (round-6 verification; closes Open question 5).
O0020  The safe sequential subset MUST NOT provide interior mutability: mutating through a `let` or `imm` path MUST be rejected outside arena subscripts.
O0021  `atomic[T]` MUST appear only as a field of a type implementing `Shared` (Rule 21a); on any other type it MUST be a compile error.
O0021a  `impl Shared for T {}` MUST be checked field-wise: every field of `T` MUST be `atomic[U]`, `imm`, or a type that itself implements `Shared`; otherwise it MUST be a compile error naming the first non-conforming field.
O0021b  `Shared` MAY be used as a generic trait bound (`fn bump[T: Shared](let c: T)`), restricting instantiation to types that implement it, exactly like any other trait bound.
O0021c  The Rule 21a field check MAY be skipped only by `@unsafe(invariant: "...") impl Shared for T {}` (ch04 Rule 10's attribute form), which MUST appear in the published unsafe inventory (ch04 Rule 9's ledger).
O0021d  `atomic[U]`'s operations take the cell by `let` and are the only exception to Rules 11 and 20: an `imm` or `let` path to a `Shared` value still reaches its atomic cells mutably, and reaches nothing else mutably — whic...
O0022  **`Linear`, the declared base** (round 6, O1).
O0022a  **`lin`, the inferred propagation.** For a normalised type (ch09 Rule 20), `lin(T)` is true iff one of: (a) `T`'s head has an `impl Linear` (found by ch09 Rule 12's lookup; by Rule 22 there are no bounds to check); (b...
O0022b  **Arrays and inline buffers.** `lin(Array[T, N])` = `lin(vector[T, N])` = `lin(T)`.
O0022c  **Rigid types, and `Droppable`** (ch09 Rule 57's amendment).
O0022d  **The obligation, and exactly what discharges it.** A live binding of linear type — a local, a `sink` parameter, a pattern binding; never the binding of a `with` block, which Rule 15a governs — carries a cleanup oblig...
O0022e  **`Copyable`.** `impl Copyable for T` MUST be rejected when `lin(T)` is true, and `X: Copyable` implies `X: Droppable`.
O0022f  **Erasure.** A linear value MUST NOT be coerced to `dyn Tr` (ch09 Rule 10(c), beside "brand-mentioning or scoped"): the obligation would become invisible to every later rule.
O0022g  **Containers, enum payloads, closures, `spawn` and `with` blocks.** A linear value inside a container, a struct field, an enum payload or a tuple makes that aggregate linear (Rule 22a(b)), and the aggregate's own cons...
O0022h  **The scope-exit check.** At every point where control leaves a scope — a block's `}` (a function body, a `with`, a `parallel`, a loop body, an arm block, a closure body), `return`, `raise`, the error exit of a `?` (c...
O0022i  **The diagnostic** (normative content, not wording).
O0023  **`defer` and `errdefer`: placement** (round 6, O2; the syntax is ch07 `defer_stmt`/`errdefer_stmt`).
O0023a  **When a `defer` body runs.** The body runs when control leaves `B` by ANY exit — reaching `B`'s `}` by fall-through or a tail value, `return`, `raise`, the error exit of a `?`, a `break` or a `continue` that leaves `...
O0023b  **When an `errdefer` body runs.** An `errdefer` body runs on the ERROR exits of `B` (ch02 Rule 16) that follow its statement, and NEVER on a normal exit.
O0023c  **What a body may contain.** A body MUST NOT contain `return`, `raise`, `?`, or a `break`/`continue` whose target loop lies outside the body (a loop written INSIDE the body may use them freely).
O0023d  **Captures, ownership and consumption.** A body mentions places of the enclosing scopes.
O0023e  **Loops, `main`, and `comptime`.** The body block of `for`, `while`, `parallel for` and `simd for` is exited at the end of every iteration and on `break`/`continue`, so a `defer` written inside it runs once per iterat...
O0023f  **Traps.** A trap runs NO deferred body, and a trap is not an exit: ch02 Rule 7 states it and states the consequence.
F0001  A function that may fail MUST declare `raises E`; `E` MUST NOT be inferred from the body.
F0002  Postfix `?` MUST propagate an error unmodified when the enclosing function's declared error type equals the callee's, else via Rule 3; `?` MUST NOT be legal on a non-`raises` expression.
F0003  Where caller raises `F` and callee raises `E != F`, `?` MUST perform exactly one `ErrorFrom[E, F]` lookup and apply it, MUST NOT chain a second conversion, and MUST be a compile error if none exists.
F0004  The failure ABI classifier has two outcomes by payload size only: (a) `<= FAILURE_INLINE_MAX`: payload in result general-purpose registers (aarch64: x0..x2), tag in `FAILURE_TAG_REG` (aarch64: `x9`), a register the ta...
F0005  `else |e| { }` MUST bind `e: E` only directly after a call expression of static type `raises E`; it MUST NOT apply to a multi-statement block.
F0006  A trap MUST lower to one breakpoint-class instruction (aarch64: `brk #imm`) plus a static read-only pc-to-info side-table entry (site id, kind, span); it MUST NOT allocate or call.
F0007  A trap is a WHOLE-PROCESS ABORT.
F0008  A backtrace crossing a fiber boundary MUST recognize the fiber-switch sentinel frame (parent fiber id, parent frame pointer, spawn-site pc) and continue through it, else report a truncated trace rather than reading un...
F0009  `pre`/`post`/`invariant` MUST be part of the declaration they annotate and MUST be runtime-checked whenever the module's policy is `.runtime` (default).
F0010  A contract check MUST be removable only by (a) a proof-engine discharge (future verification chapter) or (b) the module's explicit `.off` policy; MUST NOT be removed by `-O` level; a module's policy MUST behave identi...
F0011  The OIR range-and-dominance pass MUST be the only pass permitted to delete a bounds or overflow check; no other stage or tier MUST delete one, even if it can locally prove safety.
F0012  Any module or build with `.off` policy or a checks-disabling flag MUST be tagged internal/instrumentation and MUST be rejected by `fors build --release` and by the registry's publish check.
F0013  An `extern "c"` function MUST NOT declare `raises`; a Fors error MUST NOT cross that boundary un-mapped (mapping table: future C-interop chapter).
F0014  A C++ exception crossing an `extern "cxx"` boundary MUST be stopped there; catching it, if enabled, MUST happen only inside a separately prebuilt `@catches_cxx` C++ object file — the Fors compiler itself MUST NOT emit...
F0015  The trap-kind identifier set is exactly: `contract`, `bounds`, `overflow`, `div-zero`, `shift`, `checked-conversion`, `arena-generation`, `empty-reduce`.
F0016  **Error exit** (the definition `errdefer` keys on; ch01 Rules 23-23f are its only consumer in v0.1).
F0017  **An error raised out of `main`.** If `main` is declared `raises E` (ch04 Rule 8) and an error `e: E` propagates out of it, then, after `main`'s own `defer` and `errdefer` bodies have run (ch01 Rule 23e): (a) the runt...
D0001  Integers are fixed-width (`i8..i64`, `u8..u64`; no 128-bit in v1); any other width MUST be rejected.
D0002  `+ - * / %` and shifts MUST trap on overflow, div-by-zero, or shift-by-≥-width, in every mode including release.
D0003  No build flag or mode MAY disable trapping for plain operators; non-trapping paths exist only via Rule 4.
D0004  Every trapping op MUST have `wrap_<op>`, `sat_<op>`, `unchecked_<op>` counterparts (method form, `x.wrap_add(y)`); `unchecked_<op>` MUST NOT appear outside a declaration carrying `@unsafe(invariant: "...")` (ch04 Rule...
D0005  No implicit numeric conversion (widening, int↔float, float↔float) is allowed; type `A` MUST NOT stand in for `B` unless identical.
D0006  `as Type` MUST be checked and trapping (traps if not exactly representable); lossy conversion MUST use `wrap_as`/`sat_as`/`trunc_as`.
D0007  Floats default to strict IEEE-754: no FMA contraction, no reassociation, in every mode.
D0008  Rule 7 relaxes only inside lexical `@fastmath(flags) { ... }`, `flags ⊆ {reassoc, contract, nsz, finite, recip}`; no relaxed transform MAY escape the block's lexical extent.
D0009  `comptime_int`/`comptime_float` are arbitrary-precision, comptime-only; escaping to runtime without an explicit conversion to a fixed-width type MUST be rejected.
D0010  Default determinism is D1: bit pattern MUST NOT change with thread count, steal pattern, core class mix, or locale count alone.
D0011  `reduce(op, xs)` is a distinct primitive.
D0011a  For `n = 0`: `reduce(op, xs)` MUST trap (kind: empty-reduce, ch02); `reduce(op, xs, identity: e)` MUST return `e`.
D0012  `reduce` MUST lower to this explicit tree in FMIR **before** parallel lowering, so `--serial-elide` is bit-exact against any parallel execution of the same tree.
D0013  Tail rules: (a) no identity-padding — a partial block uses the same 8-lane shape over only its present elements; a lane shorter than its neighbours simply stops, and an empty lane contributes nothing: it is skipped in...
D0014  `reduce.serial`/`reduce.fast`/`reduce.exact` are separate named primitives, never selected implicitly by optimization level; only unqualified `reduce` carries D1.
D0015  A scalar accumulator loop MUST NOT be auto-parallelized or auto-`reduce`d at any level; the compiler MUST emit a diagnostic naming the loop and stating that explicit `reduce` is required.
D0016  Monomorphize when instantiation shape is scalar, ≤ `MONOMORPHIZE_SIZE_MAX` (16) bytes, or the body's instruction count is below the named constant `MONOMORPHIZE_INSTR_THRESHOLD`; otherwise lower via witness table (lay...
D0017  Monomorphized instantiations MUST be deduplicated via a content-addressed cache keyed on `(declaration hash, argument type shape hashes)`.
D0018  `@specialize` is compiler-enforced inside `simd`/`spmd`/`kernel` regions: an unspecialized witness-table call there MUST be a compile error with its own diagnostic code, never a silent indirect call.
D0019  `vector[T,N]` (fixed, comptime power-of-two `N`) and `mask[N]` are distinct types; masked-off lanes MUST NOT fault or trap regardless of underlying data.
D0020  `SVec[T]` is reserved: rejected as a struct/tuple field, heap element type, or generic container argument; legal only as a local/parameter inside `simd`/`spmd` bodies, and only where hardware support is enabled — othe...
D0021  An array literal (`array_lit`, ch07) is typed by the expected type (CHECK mode) when there is one: against `vector[T, N]`, `mask[N]`, or `Array[T, N]`, the literal's element count MUST equal `N` — a mismatch MUST be a...
D0022  With no expected type (SYNTH mode), an array literal is typed `Array[T, N]`: `T` is synthesised from the first element and every other element MUST check against that `T`; `N` is the element count.
D0023  `vector[T, N].splat(x)` and `mask[N].splat(b)` MUST construct a value with every lane equal to `x` (resp. every bit equal to `b`); these are the broadcast constructors this chapter names.
D0024  A `Slice[T]` value MUST be obtainable only by range-indexing an array or another slice (`data[0 ..< 3]`); no other constructor for `Slice[T]` exists.
D0024a  The repeat form `[x; n]` follows Rules 21-22 with element count `n`, which MUST be a comptime-constant `usize`; `x` is checked against the element type (CHECK) or synthesises `T` (SYNTH) and MUST be `Copyable`.
D0025  Modes.
A0001  A module MUST declare every capability it uses, or constructs a capability value from, in `needs { ... };` in its header (after `module` and any `contracts:` line, before `use`); an undeclared use MUST be a module-gra...
A0002  Checked requirement of a module = its own `needs` ∪ the *exported* requirements of its imports, over the acyclic module graph (a cyclic graph MUST be rejected before this check runs).
A0002a  A sealed operation is a use of its sealed capability by the module in whose source text it appears (Rule 1).
A0002b  The manifest policy MUST name, per sealed capability, each PACKAGE permitted to hold it (`std` is permitted by default; no wildcard).
A0003  The build MUST fail unless checked requirement ⊆ policy for every module and target (sealed capabilities checked per Rule 2b); this MUST be checked once at build time over the full graph and again at link time against...
A0004  A module whose own `needs` lacks `syscall` MUST have every byte the compiler emits for it into an executable section — including inline-assembly bytes and constants placed in text — scanned for syscall-class instructi...
A0004a  The scan cannot see foreign objects.
A0005  A module lacking `asm` MUST NOT contain inline assembly; this MUST be rejected before codegen.
A0006  `asm` and `syscall` are declared under Rule 1 and sealed under Rules 2-2b; they MUST NOT be implied by, or imply, `@unsafe`.
A0007  Every root-capability type (Rule 21) MUST have no constructor: it is opaque (no struct literal, no field access, not `Copyable`, no default/zero value) in every module, std included; only the runtime entry shim, which...
A0008  `main` is the function named `main` declared in the build's root module; it MUST NOT be generic, `extern` or `comptime`, and a function named `main` in any other module is an ordinary function to which the runtime sup...
A0009  A module holding `ffi` MUST be marked `unguaranteed`; every transitive importer MUST inherit that mark in the audit ledger, `fors audit` and the published unsafe/FFI inventory.
A0010  `@unsafe(invariant: "...")` MUST be a declaration attribute only, never a block/statement form, with a non-empty invariant string.
A0011  Comptime MUST run on exactly one engine, the FMIR interpreter; no second comptime path (macro expander, separate constant-folder) MAY exist.
A0012  Comptime MUST be pure and deterministic: no capability value, clock, RNG, env read, or ambient I/O MAY be reachable.
A0013  Every comptime file read MUST be declared in the module header's `inputs { "path", ... };` clause (ch07 header grammar, after `needs` and before `use`) and enter the build graph, and the reproducibility hash, as a con...
A0014  Every comptime evaluation MUST be charged against a step and an allocation budget (manifest-declared, else the named constants `COMPTIME_STEP_BUDGET` / `COMPTIME_ALLOC_BUDGET`, whose numeric values are set by measurem...
A0015  A comptime body MAY tier up to native code only if the compiler proves no address observation (no ptr-to-int cast, no cross-allocation pointer comparison, no reachable `rawptr`); otherwise it MUST run interpreted.
A0016  The build graph MUST be declarative data with no executable step; a manifest/lockfile entry naming a script or command to run MUST be rejected.
A0017  Resolution MUST use minimal-version selection; the lockfile MUST pin each dependency's resolved version, capability set, and sealed holdings (package, module, capability).
A0018  A resolved capability set or sealed holding not within the locked one (including a dependency that newly holds a sealed capability after an update, even if the manifest already permits its package) MUST fail the build...
A0019  A security-release channel MAY widen a capability set without `fors grant` only with a recorded signer identity and reason; an unapproved widening MUST be rejected identically to Rule 18.
A0020  A dynamic Fors module MUST carry a signed interface declaring its capability set (exported requirement and sealed holdings); the loader MUST refuse one whose set exceeds the host's grant (a load-time integrity check,...
A0021  The root-capability type set is closed and owned by this chapter, so that no two root capabilities ever share a type.
A0022  Inline assembly (`asm_expr`, ch07 grammar) MUST appear only inside a declaration marked `@unsafe(invariant: "...")` (Rule 10) in a module whose own `needs` holds the sealed `asm` capability (Rules 1-2); an `asm_expr`...
A0023  An `asm_expr` instruction of syscall class (`svc`, `syscall`, `sysenter`, `int`) additionally requires the module's own `needs` to hold the sealed `syscall` capability, and MUST be found by the Rule 4 machine-code sca...
A0024  An `asm_expr` whose architecture (the `IDENT` naming it, ch07 grammar) is not the current build target MUST be a compile error, unless the block is lexically guarded by a `comptime` test on the build target that exclu...
A0025  Every register named in an `asm_expr`'s `in`, `out` or `clobber` items MUST be a valid register name for the block's architecture; the register sets named by `out` and `clobber` MUST be disjoint; either violation MUST...
A0026  A `secret`-typed value MUST NOT be supplied as an `asm_expr` `in` input unless the enclosing declaration also carries `@ct_audited(by: "...")`, in which case the block MUST appear in the constant-time inventory (ch05)...
A0027  The value of an `asm_expr` is its `out` register: unit `()` with no `out` item, the register's value with one, a tuple in `out`-item declaration order with several.
ch05 R1  The compiler MUST implement exactly tokens → AST → FIR → FMIR → OIR → LIR → atoms; no pass MUST touch a level out of order.
ch05 R2  FIR MUST be the only serialized binary module interface; downstream compiles MUST NOT re-parse an imported module's source text.
ch05 R3  FMIR MUST be the sole input to the interpreter, comptime VM, race checker and contract prover.
ch05 R4  Every OIR memory op MUST carry an alias-class + disjointness-set operand; `--verify-each` MUST reject any lacking one.
ch05 R5  An alias class MUST derive only from parameter convention, affine ownership, arena brand id, split-token provenance, or SoA field identity; one untraceable to these five MUST fail verification, except the `unknown` cl...
ch05 R6  Every FMIR/OIR/LIR value MUST carry a secret bit and `ct_region` id as non-optional fields; `--verify-each` MUST reject any lacking them.
ch05 R6a  Secret propagation is a local FMIR type rule: the result of any operation with a secret operand is secret; `secret` on an aggregate covers every field and its discriminant; a secret value MUST NOT be stored to, passed...
ch05 R6b  FMIR checking MUST reject, with a source diagnostic: a branch, loop bound, or `match` on secret; an index, slice bound or address from secret; any trapping operation on a secret operand (plain `+ - * / %`, shifts, che...
ch05 R7  The allocator MUST expose a distinct spill class for secret values; one spilled outside it MUST fail verification.
ch05 R8  A secret spill store MUST be exempt from dead-store elimination and store-forwarding and MUST be zeroized before the epilogue; either omission MUST fail the CT verifier (rule 15).
ch05 R9  `detach` MUST carry an explicit typed capture list as an IR operand; no pass MUST reconstruct it from alias classes.
ch05 R10  FMIR `spawn`/`sync` MUST lower to OIR `detach`/`reattach`/`sync`; rewriting every `detach` to a branch MUST stay a legal, verifier-accepted rewrite for every verifying program.
ch05 R11  A value defined in a detached region MUST NOT be used after its `sync` except through memory that region owns, checked as dominance.
ch05 R12  `tile.*` MUST appear only in FMIR; the device pipeline MUST fork from FMIR before OIR lowering; a `tile.*` op found in OIR or LIR MUST fail verification.
ch05 R13  The optimizer MUST be CFG-SSA with an acyclic e-graph (dedup-on-insert, no fixed-point saturation); sea-of-nodes MUST NOT be used anywhere.
ch05 R14  The autovectorizer MUST fire only on a countable loop with trusted-length or affine access and no cross-iteration dependence disproved by alias classes; otherwise it MUST NOT transform the loop.
ch05 R15  A post-regalloc CT verifier MUST run in both backends and MUST reject a function whose `ct_region` has: a branch on secret; an address/index from secret; a denylisted instruction on a secret operand; a synthesized `@c...
ch05 R16  Constant folding, CSE, inlining and PGO/layout passes MUST propagate `ct_region`/secret unchanged, MUST NOT consume secret-derived profile data, and MUST NOT reorder across a `ct_region` boundary.
ch05 R17  Both backends and the interpreter MUST produce bit-for-bit identical output (including which trap site fires) on every accepted program that contains no `@fastmath` block and no `reduce.fast` (ch03), for identical inp...
ch05 R18  Dev-tier debug info MUST live only in an unsigned companion artifact; a debug-info-only edit MUST NOT change the signed image's CodeDirectory hash.
ch05 R19  To every optimizer pass, an inline-`asm` block (ch07 `asm_expr`, ch04 Rules 22-27) MUST be an opaque region: it reads exactly its `in` operands, writes exactly its `out` operands, and clobbers exactly its declared `cl...
ch05 R20  An asm block whose enclosing declaration carries `@ct_audited(by: "...")` (ch04 Rule 26) MUST be entered in the constant-time inventory, keyed by declaration and architecture, alongside the CT-verified code the invent...
ch05 R20a  Secret taint through an asm block is register-syntactic, like Rule 7's spill class.
ch06 R1  No performance/security claim MUST be published without a committed harness run producing it (results JSON + commit hash).
ch06 R2  Tier A/B MUST be frozen tables in this document; a numeric exit gate MUST NOT cite an unenumerated kernel set.
ch06 R3  Kernels MUST only be ADDED, each with a labelled addition date; none MUST be removed or re-tuned once a published result depends on it.
ch06 R4  Every published number MUST record the source commit of the kernel and baseline sources.
ch06 R5  Every baseline implementation MUST be published next to every number it produced.
ch06 R6  Exact compiler versions/flags MUST live in `bench/langs/*.toml`, copied verbatim into every results file.
ch06 R7  Strict-IEEE (`c`) and compiler-default-contraction (`c-fma`) columns MUST both be published wherever contraction affects output; the Fors column is compared against `c` because Fors's float default is strict IEEE (ch0...
ch06 R8  Parallel baselines (Rayon, OpenMP, OpenCilk, Kokkos) MUST publish naive and tuned columns, tuned sources cited by upstream commit where one exists.
ch06 R9  A language measured on fewer kernels than the current tables MUST NOT share a geomean with a fully-measured one; partial coverage MUST be labelled and excluded from ranking.
ch06 R10  Compile-speed MUST be wall-clock including link time; lines-per-second MUST NOT be published.
ch06 R11  Every cold-build claim MUST name which of the three cold variants (§Definitions) it uses; compared languages MUST use the same variant.
ch06 R12  The incremental benchmark MUST report p50/p95 over the declared edit-class distribution, never a single chosen edit, with a named comparator row per toolchain.
ch06 R13  Daemon incremental numbers MUST be published beside a `--no-daemon` row for the same edit; daemon RSS and first-build-after-start MUST also be reported.
ch06 R14  Edit-to-test-result latency MUST be reported alongside raw build time wherever incremental numbers are published.
ch06 R15  Parallel efficiency (speedup/cores) MUST only gate kernels marked compute-bound in the Tier A table.
ch06 R16  Bandwidth-bound kernels MUST be gated on fraction of measured roofline; their scaling MUST be reported as a curve, not one ratio.
ch06 R17  Performance-core and efficiency-core points MUST NOT be merged into one scaling curve.
ch06 R18  Every scaling figure MUST state its capacity-normalised denominator.
ch06 R19  The noise floor MUST be measured and published per metric before any comparison uses it; a difference below it MUST NOT be reported as a result.
ch06 R20  Benchmarks MUST run only on the pinned box, never concurrently with other workloads, never on battery.
ch06 R21  Every run set MUST interleave a fixed thermal-canary kernel at least every N measurements (N stated in the results file); drift beyond its own noise floor marks the run contaminated and unpublishable as clean.
ch06 R22  The confinement suite MUST draw from an external malicious-package corpus with per-case provenance; an in-house-only suite MUST NOT back a confinement claim.
ch06 R23  No "100%" confinement claim MUST be published before a red-team round has run against that suite.
ch06 R24  Every confinement claim MUST publish, beside the pass rate, the attack classes the model does not stop (ch04, "Attack classes this model does not stop").
ch06 R25  Safety cost MUST be measured against the internal checks-off instrumentation build (ch02 Rule 12: unshippable) and reported separately from any competitiveness-vs-C claim; the two MUST NOT be conflated.
N0001  Each `.fors` file under a package's source root MUST define exactly one module.
N0002  Which module is the root module is decided by the build (ch04 Rule 8), never by a file name or by which module declares a `main`.
N0003  A `use` item takes exactly the forms of ch07's `use_decl`: `use p;`, `use p as c;`, `use p1, p2, ...;` (any comma-separated mix of the two), each optionally prefixed `pub`.
N0004  A `use` path `s1. ... .sn`, optionally followed by `"as" c`, resolves as follows and binds exactly one name — `c` if an alias is given, else `sn` — in the importing module's scope.
N0005  `pub use` additionally makes each name it binds — `sn`, or its alias `c` when `"as" ident` is given — a `pub` module-scope name of the importing module, denoting the same entity (item or module).
N0006  Imports are not transitive: a name module `M` binds by `use` (aliased or not) is in `M`'s scope only.
N0007  The module graph has one edge per `use` path, and NO other edge: to the module itself in Rule 4(a), to `M` in Rule 4(b).
N0008  A `use` path whose edge (Rule 7) targets the module it appears in — `use m;` or `use m.item;` inside `m` — is a cycle of length one and MUST be a compile error naming the module.
N0009  Module scope is order-independent: an item MAY be referred to anywhere in its module regardless of textual order, including from `const` initialisers and signatures (a cyclic `const` dependency is a comptime error, ch...
N0010  An item is private to its defining module unless marked `pub`.
N0011  Member visibility.
N0012  The signature of a `pub` item MUST NOT name a non-`pub` item of its own module.
N0013  A module scope holds each identifier at most once.
N0014  A name is looked up through the scopes enclosing its use, innermost first: bindings of enclosing blocks, match arms, closures, loops, `with` statements and handlers of the same function; the function's parameters; its...
N0015  Two imports (of one module or of different modules) that bind the same name — `sn` or an `"as" ident` alias — to different entities MUST be a compile error at the second `use` path, naming both, whether or not the nam...
N0016  A multi-segment `path` resolves left to right.
N0017  The prelude is a closed list, present in every module scope, and it contains NO modules (owner decision 2026-09-19, round 5, D3).
N0018  No shadowing, with one exception.
N0019  `with arena a: T { ... }` and `with allocator a: T { ... }` introduce one binding `a`, in scope in the header type `T` and in the block (ch01 Rule 15 owns the use of `a` as a brand in type position, and its open quest...
N0020  The identifier in `scoped(p)` (ch07 `ret_type`) is looked up only among the parameters of the same `fn_sig`, not by Rule 14; anything else MUST be a compile error.
N0021  An `impl_decl` introduces no name: it is never a `use` target and never in a scope.
N0022  Deferred to the checker, because each needs a type: every deferred segment of Rule 16; every postfix `.name` whose operand is not a `path` continuation (`f().x`, `a[i].x`, `x?.y`); method names and receiver dispatch;...
N0023  The following identifiers are not names: they are never looked up, never bind, and never conflict with a scope.
N0024  File names.
N0025  Patterns.
N0026  Scope of each binding.
N0027  Member tables.
T0001  The checker MUST type a function body in one left-to-right pass in which each CST node is visited once, in one mode.
T0002  Signatures are the only interface between declarations.
T0003  Primitive types and sizes in bytes: `i8 u8 bool` 1; `i16 u16` 2; `i32 u32 f32` 4; `i64 u64 f64` 8; `isize usize rawptr` the target pointer width.
T0004  `()` is the unit type (one value, size 0).
T0005  Built-in generic types: `Array[T, N]` (`N: usize`; the type of `[x; n]` and array literals, ch03 Rules 21-24a; there is no `[T; n]` type syntax), `Slice[T]` (ch03 Rule 24), `vector[T, N]` and `mask[N]` (ch03 Rule 19;...
T0006  `struct`, `soa struct` and `enum` declarations introduce nominal types: two declarations are never equal whatever their fields.
T0007  Function types are written as ch07's `fn_type` and are equal iff conventions, parameter types, result type and `raises` type are pairwise equal (a missing result is `()`; a missing `raises` is distinct from every `rai...
T0008  There is no type-alias declaration (ch07).
T0009  Type equality.
T0010  There is no subtyping.
T0011  A `type_app` MUST supply exactly as many arguments as its item declares parameters, each of the declared kind: a type for a type parameter, a constant for a const parameter, a brand for a `brand` parameter (kind misus...
T0012  Bounds MUST hold at every use: for each argument `X` given to a parameter `P: Tr1 + ... + Trk`, `X` MUST implement every `Tri`.
T0013  A generic parameter whose bound is a type (Rule 15) is a const parameter; that type MUST be an integer type or `bool`.
T0014  A type of infinite size MUST be rejected.
T0015  A `gparam` is classified from its bound alone: `brand` (ch01 Rule 15d); no bound — an unbounded type parameter; otherwise every `+`-joined bound is resolved, and they MUST be either all traits (a bounded type paramete...
T0016  A `trait` declares methods and associated types (ch07 `trait_item`).
T0017  `impl Tr[As] for S` MUST define every required method of `Tr`, MAY redefine provided ones, MUST define every associated type of `Tr` exactly once (`type A = T;`; a second definition in the same impl is ch08 Rule 27's...
T0018  In an `impl_decl` with `for`, the first type MUST be a trait and the second MUST NOT be one; without `for` the type MUST be a struct or enum.
T0019  Overlap.
T0020  Normalisation.
T0021  The operator-trait set is closed; no other operator is overloadable and no other trait is consulted by an operator.
T0022  Not overloadable, and typed only by this chapter's fixed rules: `and`, `or`, `not` (operands `bool`); `=`; `?` and the `else` handler (ch02); `move`, `&`, `&out` (ch01 Rule 2); `as` (numeric primitives only, ch03 Rule...
T0023  `Copyable` is a checked marker trait with no methods.
T0024  A marker trait (`Shared`, `Copyable`, and from round 6 `Linear` and `Droppable`) has no methods and contributes no operation to a generic body; as a bound it only restricts instantiation (ch01 Rule 21b).
T0025  `dyn Tr` is well-formed iff `Tr` is dyn-capable: it declares no associated type (so `dyn Iterator` does not exist in v0.1; there is no `dyn Tr[Item = T]` form), it has no generic methods, every method is a receiver me...
T0026  Every expression is typed by exactly one of `synth(e)` and `check(e, T)`; the position decides which (ch03 Rule 25).
T0027  Literals.
T0028  A `path` resolved by ch08 to a binding synthesises its declared type; to a `const`, its annotation; to a non-generic `fn`, Rule 7; to a unit variant, its enum with arguments by Rule 38.
T0029  Operators.
T0030  `not`/`and`/`or` operands and `if`/`while` conditions and contract clauses are synthesised and MUST be `bool`.
T0031  Statements.
T0032  `if` and `match`.
T0033  `never`.
T0034  Aggregates.
T0035  Closures.
T0036  `e?` and `call else |x| { ... }` require `e` to be a call of a `raises E` function (ch02 Rules 1-5).
T0037  `comptime { }` has the type and mode of its block (evaluation: ch04).
T0038  The generic arguments of a call, struct literal or variant construction are determined by this procedure and no other.
T0039  If a parameter is still undetermined after Rule 38(d) — a parameter that occurs only under projections (`fn g[I: Iterator](let x: I.Item)`) always is, unless given explicitly — the call MUST be rejected: "cannot infer...
T0040  Const parameters follow Rule 38 unchanged (bound by value or by the bare parameter).
T0041  A callable parameter `F: fn(...) -> R raises E` (Rule 15) accepts a closure type, `fn` item or `fn` value of that signature, and a value of type `F` may be called with it.
T0042  `e.name` not followed by a call or by instantiating brackets is a field access: `synth(e)` MUST have a struct head with a visible field `name` (ch08 Rule 11); the result is the field's type with the struct's arguments...
T0043  `e.name(args)`: `S = synth(e)`, qualifiers stripped for lookup.
T0044  More than one candidate in the tier that answered MUST be an error listing them; the call is rewritten in a qualified form (Rule 45).
T0045  Qualified forms (deferred segments, ch08 Rule 16).
T0046  Receivers.
T0047  A `bracket` after an expression instantiates iff its operand is a `path` the resolver bound to a generic `fn`, struct, enum, trait or prelude type, or is a `.name` that Rule 43/45 resolves to a method or associated fu...
T0048  Member clashes (left open by ch08 Rule 27) are errors at the later declaration: two inherent methods or associated functions of one head with the same name, in the same or different `impl` blocks; an inherent member n...
T0049  The checker enforces ch08 Rule 11 for every member it resolves, with ch08's diagnostic, and performs no scope lookup (ch08 Rule 22).
T0050  A pattern is checked against the scrutinee's type `S` (`synth` of the `match` head).
T0051  A `let n` binding has the type of the component it faces, with the enum's or struct's arguments substituted.
T0052  Refutable patterns occur only in `match` arms.
T0053  A `match` MUST be exhaustive.
T0054  An arm that is not useful with respect to the arms before it MUST be rejected as unreachable.
T0055  Why this is cheap, and the guard.
T0056  Range patterns, or-patterns and guards are absent from ch07 and MUST NOT be accepted.
T0057  A generic declaration is checked once, at its definition, with each type parameter rigid.
T0058  A brand parameter has no operations at all and occurs only as a brand argument (ch01 Rule 15d).
T0059  No error may depend on an instantiation.
T0060  The `raises` type of a signature is a type like any other (ch02 Rule 1): it MAY be a type parameter (`fn try_apply[T, U, E, F: fn(let T) -> U raises E](let x: T, let f: F) -> U raises E`), determined by Rule 38.
T0061  Projections.
T0062  Constraint entries.
S0001  The std module list is closed for v0.1 and is exactly ch08 Rule 17's ten names:
S0002  Std contributes exactly eight names to ch08 Rule 17's prelude, all types or traits, no modules and no values:
S0003  No std operation reads or writes anything outside the process, and no std operation allocates, except through a value the caller passed it: a capability value (ch04 Rule 21) for the outside world, an allocator value (...
S0004  Receiver conventions in std are fixed by what the operation does, not by taste: `let self` iff it only reads the receiver; `inout self` iff it mutates the receiver in place; `sink self` iff it consumes the receiver, a...
S0005  Naming is a contract, not a style: `*_into` is the caller-buffer form and allocates nothing; `try_*` is the fallible sibling of a higher-order function (Rule 8); `*_or` is the total variant of a fallible or partial op...
S0006  Failure discipline.
S0007  The std error types are closed and there is at most one per module: `mem.AllocError` (prelude `AllocError`), `mem.Utf8Error` (prelude `Utf8Error`), `io.Error`, `fs.Error`, `net.Error`, `net.TimeoutError` (Rule 43's de...
S0008  There is no effect polymorphism (owner decision, round 4), so a callable parameter of a std function MUST NOT be declared `raises`.
S0009  v0.1 interface stability.
S0010  Not in v0.1.
S0011  Linearity and leaks.
S0012  The allocator interface.
S0013  Layout, alignment, zeroing.
S0014  Reallocation.
S0015  `Block[A]`.
S0016  Freeing.
S0017  The process heap.
S0018  `PageAllocator`.
S0019  `mem.Bump`, the arena allocator: `with allocator a: mem.Bump { ... }` gets regions from the operating system, serves `alloc` by bumping a pointer, makes `free` a no-op that keeps linearity honest, and releases every r...
S0020  `mem.Fixed[N: usize, A: brand]`, the fixed-buffer allocator, whose brand argument is last so that the `with` header may omit it (ch01 Rule 15b): `with allocator f: mem.Fixed[65536] { ... }` serves allocations out of `...
S0021  `mem.Counting[N: usize, A: brand]`, the testing allocator: a `mem.Fixed[N]` that also counts.
S0022  `Own[T, A]`, the single heap value (ch01 Rule 18 owns its brand rule).
S0023  `Buffer[T, N: usize]`, the inline fixed-capacity buffer:
S0024  `Vec[T, A: brand]`, the growable array:
S0025  `Map[K, V, A: brand]`, the hash map:
S0026  `String[A: brand]` and `Str`.
S0027  `Option[T]` is ch09 Rule 5's built-in enum with `some(T)` and `none`, whose constructors the prelude binds as values (ch08 Rule 17); this chapter adds only `fn unwrap_or(sink self: Option[T], sink fallback: T) -> T` a...
S0028  `Slice[T]` and std's slice primitives.
S0029  `mem.Hash` is implemented by std for `Str`, every integer type, `bool` and `Slice[T]` where `T: Hash`; the hash function is fixed, documented as non-cryptographic, and MUST NOT depend on the target, the build or any a...
S0030  `Copyable` and `Shared` for std types.
S0031  Ordering.
S0032  The `Iterator` trait.
S0033  How a container yields an iterator, under the convention system, is exactly two forms in v0.1, plus indexing: (a) over `let` data: ONE iterator type, `SliceIter[T]` (`std.mem.seq`, `mem.SliceIter`), with `Item = T` an...
S0034  The adaptor set is closed for v0.1.
S0035  The consumer set is closed for v0.1 and is also PROVIDED METHODS of `Iterator`, each taking its source `sink self` (it is used up) and returning a plain value:
S0036  `for` over std.
S0037  Determinism of iteration.
S0038  For every capability module, the root-capability type `main` receives and the capability it pairs with are ch04 Rule 21's, unchanged: `io.Stdout`→`io.stdout`, `io.Stderr`→`io.stderr`, `io.Stdin`→`io.stdin`, `fs.Dir`→`...
S0039  `io`.
S0040  `io` buffering and what survives an abort.
S0041  `fs`.
S0042  The comptime file read.
S0043  `net`.
S0044  `proc`.
S0045  `time`.
S0046  `env`.
S0047  `rand`.
S0048  `gpu`.
S0049  `ffi`.
S0050  `spawn`, `parallel`, `parallel for`, `simd for` and `reduce` are LANGUAGE forms (ch01 Rule 13, ch03 Rules 11-13); std adds no scheduler, no task type and no thread handle.
S0051  Which std types are `Shared` (ch01 Rules 21-21d): `Str`, `Slice[T]` where `T` is `Shared`, `Layout`, `time.Instant`, `time.Wall`, `time.Duration`, `net.Addr`, `rand.Pcg` and every std error type — all of them field-wi...
S0052  Allocation inside a parallel region.
S0053  No ambient authority, and where the syscalls go.
S0054  No hidden allocation.
S0055  No trap for an expected condition (ch02 Rule 7).
S0056  No dependence on locale or environment.
S0057  The audit.
```

## 4. Standard-library surface

Every top-level declaration under `std/`, signatures only, bodies
elided as `{ ... }`, grouped by module in path order.

### std.env  (`std/env.fors`)
```fors
pub enum Error { ... }
pub struct Env { ... }
pub struct Args { ... }
impl Env {
    pub fn has(let self: Self, let name: Str) -> bool { ... }
    pub fn get_into(let self: Self, let name: Str, inout into: Slice[u8]) -> Option[usize] raises Error { ... }
}
impl Args {
    pub fn len(let self: Self) -> usize { ... }
    pub fn at(let self: Self, let i: usize) -> Option[Str] { ... }
}
```

### std.ffi  (`std/ffi.fors`)
```fors
pub enum Error { ... }
pub struct CStr { ... }
impl CStr {
    pub fn len(let self: Self) -> usize { ... }
    pub fn to_str(let self: Self) -> scoped(self) Str raises mem.Utf8Error { ... }
    pub fn from_bytes(let b: Slice[u8]) -> scoped(b) CStr raises Error { ... }
}
```

### std.fs  (`std/fs.fors`)
```fors
pub enum Error { ... }
pub enum Kind { ... }
pub struct Meta { ... }
pub struct Dir { ... }
impl Dir {
    pub fn open_dir(let self: Self, let name: Str) -> Dir raises Error { ... }
    pub fn read_into(let self: Self, let name: Str, inout into: Slice[u8]) -> usize raises Error { ... }
    pub fn write_all(let self: Self, let name: Str, let bytes: Slice[u8]) raises Error { ... }
    pub fn open(let self: Self, let name: Str) -> File raises Error { ... }
    pub fn create(let self: Self, let name: Str) -> File raises Error { ... }
    pub fn metadata(let self: Self, let name: Str) -> Meta raises Error { ... }
    pub fn remove(let self: Self, let name: Str) raises Error { ... }
    pub fn rename(let self: Self, let from: Str, let to: Str) raises Error { ... }
    pub fn entries(let self: Self) -> Entries raises Error { ... }
}
pub struct File { ... }
impl Linear for File {}
impl File {
    pub fn read_into(inout self: Self, inout into: Slice[u8]) -> usize raises Error { ... }
    pub fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error { ... }
    pub fn len(let self: Self) -> u64 raises Error { ... }
    pub fn close(sink self: Self) raises Error { ... }
}
impl io.Reader for File {
    fn read(inout self: Self, inout into: Slice[u8]) -> usize raises io.Error { ... }
}
impl io.Writer for File {
    fn write(inout self: Self, let bytes: Slice[u8]) -> usize raises io.Error { ... }
    fn write_all(inout self: Self, let bytes: Slice[u8]) raises io.Error { ... }
    fn flush(inout self: Self) raises io.Error { ... }
}
pub struct Entries { ... }
impl Linear for Entries {}
impl Entries {
    pub fn next_into(inout self: Self, inout name: Slice[u8]) -> Option[Meta] raises Error { ... }
    pub fn close(sink self: Self) { ... }
}
pub fn read_to_string(let path: Str) -> Str { ... }
```

### std.gpu  (`std/gpu.fors`)
```fors
pub enum Error { ... }
pub struct Device { ... }
pub struct Info { ... }
impl Device {
    pub fn info(let self: Self) -> Info { ... }
    pub fn sync(inout self: Self) raises Error { ... }
}
```

### std.io  (`std/io.fors`)
```fors
pub enum Error { ... }
pub trait Writer {
    fn write(inout self: Self, let bytes: Slice[u8]) -> usize raises Error;
    fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error;
    fn flush(inout self: Self) raises Error;
}
pub trait Reader {
    fn read(inout self: Self, inout into: Slice[u8]) -> usize raises Error;
}
pub struct Stdout { ... }
pub struct Stderr { ... }
pub struct Stdin { ... }
impl Stdout {
    pub fn write_line(inout self: Self, let s: Str) { ... }
    pub fn write_str(inout self: Self, let s: Str) { ... }
    pub fn write_int(inout self: Self, let v: i64) { ... }
    pub fn write_uint(inout self: Self, let v: u64) { ... }
    pub fn write_bytes(inout self: Self, let b: Slice[u8]) { ... }
    pub fn check(inout self: Self) raises Error { ... }
    pub fn clear_error(inout self: Self) { ... }
}
impl Stderr {
    pub fn write_line(inout self: Self, let s: Str) { ... }
    pub fn write_str(inout self: Self, let s: Str) { ... }
    pub fn write_int(inout self: Self, let v: i64) { ... }
    pub fn write_uint(inout self: Self, let v: u64) { ... }
    pub fn write_bytes(inout self: Self, let b: Slice[u8]) { ... }
    pub fn check(inout self: Self) raises Error { ... }
    pub fn clear_error(inout self: Self) { ... }
}
impl Stdin {
    pub fn read_line_into(inout self: Self, inout into: Slice[u8]) -> Option[usize] raises Error { ... }
}
impl Writer for Stdout {
    fn write(inout self: Self, let bytes: Slice[u8]) -> usize raises Error { ... }
    fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error { ... }
    fn flush(inout self: Self) raises Error { ... }
}
impl Writer for Stderr {
    fn write(inout self: Self, let bytes: Slice[u8]) -> usize raises Error { ... }
    fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error { ... }
    fn flush(inout self: Self) raises Error { ... }
}
impl Reader for Stdin {
    fn read(inout self: Self, inout into: Slice[u8]) -> usize raises Error { ... }
}
```

### std.mem.alloc  (`std/mem/alloc.fors`)
```fors
pub enum AllocError { ... }
pub struct Layout { ... }
impl Layout {
    pub fn of[T]() -> Layout { ... }
    pub fn array[T](let n: usize) -> Layout raises AllocError { ... }
}
pub struct Block[A: brand] { ... }
impl[A: brand] Linear for Block[A] {}
impl[A: brand] Block[A] {
    pub fn len(let self: Self) -> usize { ... }
    pub fn align(let self: Self) -> usize { ... }
    pub fn bytes_raw(inout self: Self) -> scoped(self) Slice[u8] { ... }
}
pub fn own_raw[T, A: brand](sink b: Block[A], sink v: T) -> Own[T, A] { ... }
pub fn disown_raw[T, A: brand](sink o: Own[T, A]) -> (Block[A], T) { ... }
pub trait Allocator[A: brand] {
    fn alloc(inout self: Self, let layout: Layout) -> Block[A] raises AllocError;
    fn alloc_zeroed(inout self: Self, let layout: Layout) -> Block[A] raises AllocError;
    fn grow(inout self: Self, inout b: Block[A], let layout: Layout) raises AllocError;
    fn shrink(inout self: Self, inout b: Block[A], let layout: Layout);
    fn free(inout self: Self, sink b: Block[A]);
    fn owns(let self: Self, let b: Block[A]) -> bool;
    fn create[T: Droppable](inout self: Self, sink v: T) -> Own[T, A] raises AllocError { ... }
    fn deinit[T](inout self: Self, sink o: Own[T, A]) -> T { ... }
}
```

### std.mem.hashmap  (`std/mem/hashmap.fors`)
```fors
pub trait Hash {
    fn hash(let self: Self, let seed: u64) -> u64;
}
impl Hash for u8 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for u16 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for u32 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for u64 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for usize {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for i8 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for i16 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for i32 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for i64 {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for isize {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for bool {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl Hash for Str {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
impl[T: Hash] Hash for Slice[T] {
    fn hash(let self: Self, let seed: u64) -> u64 { ... }
}
pub struct Map[K, V, A: brand] { ... }
impl[K, V, A: brand] Linear for Map[K, V, A] {}
impl[K: Eq + Hash, V, A: brand] Map[K, V, A] {
    pub fn new() -> Map[K, V, A] { ... }
    pub fn seeded(let seed: u64) -> Map[K, V, A] { ... }
    pub fn len(let self: Self) -> usize { ... }
    pub fn has(let self: Self, let k: K) -> bool { ... }
    pub fn insert[L: alloc.Allocator[A]](inout self: Self, inout a: L, sink k: K, sink v: V) -> Option[V] raises alloc.AllocError { ... }
    pub fn remove(inout self: Self, let k: K) -> Option[V] { ... }
    pub fn reserve[L: alloc.Allocator[A]](inout self: Self, inout a: L, let extra: usize) raises alloc.AllocError { ... }
    pub fn deinit_empty[L: alloc.Allocator[A]](sink self: Self, inout a: L) pre self.len() == 0 { ... }
}
impl[K: Eq + Hash, V: Droppable, A: brand] Map[K, V, A] {
    pub fn clear(inout self: Self) { ... }
    pub fn deinit[L: alloc.Allocator[A]](sink self: Self, inout a: L) { ... }
}
impl[K: Eq + Hash, V: Copyable, A: brand] Map[K, V, A] {
    pub fn get(let self: Self, let k: K) -> Option[V] { ... }
    pub fn get_or(let self: Self, let k: K, let fallback: V) -> V { ... }
}
impl[K: Eq + Hash, V, A: brand] Index[K] for Map[K, V, A] {
    type Output = V;
    fn at(let self: Self, let i: K) -> scoped(self) Self.Output { ... }
}
impl[K: Eq + Hash, V, A: brand] IndexMut[K] for Map[K, V, A] {
    fn at_mut(inout self: Self, let i: K) -> scoped(self) Self.Output { ... }
}
```

### std.mem.seq  (`std/mem/seq.fors`)
```fors
pub trait Iterator {
    type Item: Droppable;
    fn next(inout self) -> Option[Self.Item];
    fn map[U: Droppable](sink self, let f: fn(sink Self.Item) -> U) -> Mapped[Self, U] { ... }
    fn filter(sink self, let p: fn(let Self.Item) -> bool) -> Filtered[Self] { ... }
    fn take(sink self, let n: usize) -> Taken[Self] { ... }
    fn skip(sink self, let n: usize) -> Skipped[Self] { ... }
    fn enumerate(sink self) -> Enumerated[Self] { ... }
    fn zip[J: Iterator](sink self, sink other: J) -> Zipped[Self, J] { ... }
    fn by_ref(inout self) -> scoped(self) ByRef[Self] { ... }
    fn count(sink self) -> usize { ... }
    fn fold[B](sink self, sink init: B, let f: fn(sink B, sink Self.Item) -> B) -> B { ... }
    fn for_each(sink self, let f: fn(sink Self.Item)) { ... }
    fn all(sink self, let p: fn(let Self.Item) -> bool) -> bool { ... }
    fn any(sink self, let p: fn(let Self.Item) -> bool) -> bool { ... }
    fn find(sink self, let p: fn(let Self.Item) -> bool) -> Option[Self.Item] { ... }
    fn try_fold[B, E](sink self, sink init: B, let f: fn(sink B, sink Self.Item) -> B raises E) -> B raises E { ... }
    fn try_for_each[E](sink self, let f: fn(sink Self.Item) raises E) raises E { ... }
}
pub struct SliceIter[T] { ... }
impl[T: Copyable] Iterator for SliceIter[T] {
    type Item = T;
    fn next(inout self) -> Option[Self.Item] { ... }
}
pub fn iter[T: Copyable](let s: Slice[T]) -> scoped(s) SliceIter[T] { ... }
pub struct Mapped[I: Iterator, U: Droppable] { ... }
pub struct Filtered[I: Iterator] { ... }
pub struct Taken[I: Iterator] { ... }
pub struct Skipped[I: Iterator] { ... }
pub struct Enumerated[I: Iterator] { ... }
pub struct Zipped[I: Iterator, J: Iterator] { ... }
pub struct ByRef[I: Iterator] { ... }
impl[I: Iterator, U: Droppable] Iterator for Mapped[I, U] {
    type Item = U;
    fn next(inout self) -> Option[U] { ... }
}
impl[I: Iterator] Iterator for Filtered[I] {
    type Item = I.Item;
    fn next(inout self) -> Option[I.Item] { ... }
}
impl[I: Iterator] Iterator for Taken[I] {
    type Item = I.Item;
    fn next(inout self) -> Option[I.Item] { ... }
}
impl[I: Iterator] Iterator for Skipped[I] {
    type Item = I.Item;
    fn next(inout self) -> Option[I.Item] { ... }
}
impl[I: Iterator] Iterator for Enumerated[I] {
    type Item = (usize, I.Item);
    fn next(inout self) -> Option[Self.Item] { ... }
}
impl[I: Iterator, J: Iterator] Iterator for Zipped[I, J] {
    type Item = (I.Item, J.Item);
    fn next(inout self) -> Option[Self.Item] { ... }
}
impl[I: Iterator] Iterator for ByRef[I] {
    type Item = I.Item;
    fn next(inout self) -> Option[I.Item] { ... }
}
impl[I: Iterator] ByRef[I] {
    fn pull(inout self) -> Option[I.Item] { ... }
}
```

### std.mem.text  (`std/mem/text.fors`)
```fors
pub enum Utf8Error { ... }
pub struct String[A: brand] { ... }
impl[A: brand] Linear for String[A] {}
impl[A: brand] String[A] {
    pub fn new() -> String[A] { ... }
    pub fn len(let self: Self) -> usize { ... }
    pub fn as_str(let self: Self) -> scoped(self) Str { ... }
    pub fn push_str[L: alloc.Allocator[A]](inout self: Self, inout a: L, let s: Str) raises alloc.AllocError { ... }
    pub fn push_scalar(inout self: Self, let cp: u32) raises Utf8Error pre self.capacity - self.n >= 4 { ... }
    pub fn from_str[L: alloc.Allocator[A]](inout a: L, let s: Str) -> String[A] raises alloc.AllocError { ... }
    pub fn reserve[L: alloc.Allocator[A]](inout self: Self, inout a: L, let extra: usize) raises alloc.AllocError { ... }
    pub fn clear(inout self: Self) { ... }
    pub fn deinit[L: alloc.Allocator[A]](sink self: Self, inout a: L) { ... }
}
impl Str {
    pub fn len(let self: Self) -> usize { ... }
    pub fn at(let self: Self, let i: usize) -> u8 { ... }
    pub fn slice(let self: Self, let start: usize, let end: usize) -> scoped(self) Str raises Utf8Error pre start <= end and end <= self.len() { ... }
    pub fn eq(let self: Self, let rhs: Str) -> bool { ... }
    pub fn starts_with(let self: Self, let p: Str) -> bool { ... }
    pub fn find(let self: Self, let needle: Str) -> Option[usize] { ... }
    pub fn from_utf8(let bytes: Slice[u8]) -> scoped(bytes) Str raises Utf8Error { ... }
    pub fn bytes_raw(let self: Self) -> scoped(self) Slice[u8] { ... }
    pub fn scalars(let self: Self) -> scoped(self) Scalars { ... }
}
pub struct Scalars { ... }
impl Iterator for Scalars {
    type Item = u32;
    fn next(inout self: Self) -> Option[Self.Item] { ... }
}
```

### std.mem.vec  (`std/mem/vec.fors`)
```fors
pub struct Vec[T, A: brand] { ... }
impl[T, A: brand] Linear for Vec[T, A] {}
impl[T, A: brand] Vec[T, A] {
    pub fn new() -> Vec[T, A] { ... }
    pub fn len(let self: Self) -> usize { ... }
    pub fn cap(let self: Self) -> usize { ... }
    pub fn push[L: alloc.Allocator[A]](inout self: Self, inout a: L, sink v: T) raises alloc.AllocError { ... }
    pub fn pop(inout self: Self) -> Option[T] { ... }
    pub fn reserve[L: alloc.Allocator[A]](inout self: Self, inout a: L, let extra: usize) raises alloc.AllocError { ... }
    pub fn shrink_to_fit[L: alloc.Allocator[A]](inout self: Self, inout a: L) { ... }
    pub fn swap_remove(inout self: Self, let i: usize) -> T pre i < self.n { ... }
    pub fn items(let self: Self) -> scoped(self) Slice[T] { ... }
    pub fn items_mut(inout self: Self) -> scoped(self) Slice[T] { ... }
    pub fn deinit_empty[L: alloc.Allocator[A]](sink self: Self, inout a: L) pre self.len() == 0 { ... }
}
impl[T: Droppable, A: brand] Vec[T, A] {
    pub fn clear(inout self: Self) { ... }
    pub fn deinit[L: alloc.Allocator[A]](sink self: Self, inout a: L) { ... }
}
impl[T: Copyable, A: brand] Vec[T, A] {
    pub fn iter(let self: Self) -> scoped(self) seq.SliceIter[T] { ... }
}
impl[T, A: brand] Index[usize] for Vec[T, A] {
    type Output = T;
    fn at(let self: Self, let i: usize) -> scoped(self) Self.Output { ... }
}
impl[T, A: brand] IndexMut[usize] for Vec[T, A] {
    fn at_mut(inout self: Self, let i: usize) -> scoped(self) Self.Output { ... }
}
pub fn try_collect_into[I: Iterator, A: brand, L: alloc.Allocator[A]](sink it: I, inout dst: Vec[I.Item, A], inout a: L) raises alloc.AllocError { ... }
```

### std.mem  (`std/mem.fors`)
```fors
pub const MEM_MAX_ALIGN: usize = 16;
pub struct Heap[A: brand] { ... }
impl[A: brand] alloc.Allocator[A] for Heap[A] {
    fn alloc(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn alloc_zeroed(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn grow(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) raises alloc.AllocError { ... }
    fn shrink(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) { ... }
    fn free(inout self: Self, sink b: alloc.Block[A]) { ... }
    fn owns(let self: Self, let b: alloc.Block[A]) -> bool { ... }
}
pub struct PageAllocator[A: brand] { ... }
impl[A: brand] alloc.Allocator[A] for PageAllocator[A] {
    fn alloc(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn alloc_zeroed(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn grow(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) raises alloc.AllocError { ... }
    fn shrink(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) { ... }
    fn free(inout self: Self, sink b: alloc.Block[A]) { ... }
    fn owns(let self: Self, let b: alloc.Block[A]) -> bool { ... }
}
pub struct Bump[A: brand] { ... }
impl[A: brand] Bump[A] {
    pub fn reset(inout self: Self) { ... }
}
impl[A: brand] alloc.Allocator[A] for Bump[A] {
    fn alloc(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn alloc_zeroed(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn grow(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) raises alloc.AllocError { ... }
    fn shrink(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) { ... }
    fn free(inout self: Self, sink b: alloc.Block[A]) { ... }
    fn owns(let self: Self, let b: alloc.Block[A]) -> bool { ... }
}
pub struct Fixed[N: usize, A: brand] { ... }
impl[N: usize, A: brand] alloc.Allocator[A] for Fixed[N, A] {
    fn alloc(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn alloc_zeroed(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn grow(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) raises alloc.AllocError { ... }
    fn shrink(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) { ... }
    fn free(inout self: Self, sink b: alloc.Block[A]) { ... }
    fn owns(let self: Self, let b: alloc.Block[A]) -> bool { ... }
}
pub struct Counting[N: usize, A: brand] { ... }
impl[N: usize, A: brand] Counting[N, A] {
    pub fn bytes_live(let self: Self) -> usize { ... }
    pub fn allocs(let self: Self) -> u64 { ... }
    pub fn frees(let self: Self) -> u64 { ... }
    pub fn peak_bytes(let self: Self) -> usize { ... }
    pub fn assert_empty(let self: Self) pre self.used == 0 { ... }
}
impl[N: usize, A: brand] alloc.Allocator[A] for Counting[N, A] {
    fn alloc(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn alloc_zeroed(inout self: Self, let layout: alloc.Layout) -> alloc.Block[A] raises alloc.AllocError { ... }
    fn grow(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) raises alloc.AllocError { ... }
    fn shrink(inout self: Self, inout b: alloc.Block[A], let layout: alloc.Layout) { ... }
    fn free(inout self: Self, sink b: alloc.Block[A]) { ... }
    fn owns(let self: Self, let b: alloc.Block[A]) -> bool { ... }
}
impl[T: Copyable, A: brand] Own[T, A] {
    pub fn get(let self: Self) -> T { ... }
    pub fn set(inout self: Self, let v: T) { ... }
}
impl[T, A: brand] Own[T, A] {
    pub fn replace(inout self: Self, sink v: T) -> T { ... }
}
impl[T] Option[T] {
    pub fn unwrap_or(sink self: Self, sink fallback: T) -> T { ... }
    pub fn is_some(let self: Self) -> bool { ... }
}
pub struct Buffer[T, N: usize] { ... }
impl[T, N: usize] Buffer[T, N] {
    pub fn empty() -> Buffer[T, N] { ... }
    pub fn cap(let self: Self) -> usize { ... }
    pub fn push(inout self: Self, sink v: T) -> Option[T] { ... }
    pub fn pop(inout self: Self) -> Option[T] { ... }
    pub fn clear(inout self: Self) { ... }
    pub fn items(let self: Self) -> scoped(self) Slice[T] { ... }
    pub fn items_mut(inout self: Self) -> scoped(self) Slice[T] { ... }
    pub fn into_iter(sink self: Self) -> BufferIter[T, N] { ... }
}
impl[T: Copyable, N: usize] Buffer[T, N] {
    pub fn filled(let v: T) -> Buffer[T, N] { ... }
    pub fn iter(let self: Self) -> scoped(self) seq.SliceIter[T] { ... }
}
impl[T, N: usize] Index[usize] for Buffer[T, N] {
    type Output = T;
    fn at(let self: Self, let i: usize) -> scoped(self) Self.Output { ... }
}
impl[T, N: usize] IndexMut[usize] for Buffer[T, N] {
    fn at_mut(inout self: Self, let i: usize) -> scoped(self) Self.Output { ... }
}
pub struct BufferIter[T, N: usize] { ... }
impl[T: Droppable, N: usize] Iterator for BufferIter[T, N] {
    type Item = T;
    fn next(inout self: Self) -> Option[Self.Item] { ... }
}
pub fn fill[T: Copyable](inout s: Slice[T], let v: T) { ... }
pub fn swap[T](inout s: Slice[T], let i: usize, let j: usize) { ... }
pub fn copy_from[T: Copyable](inout dst: Slice[T], let src: Slice[T]) pre dst.len == src.len { ... }
pub fn eq[T: Eq](let a: Slice[T], let b: Slice[T]) -> bool { ... }
pub fn split_at[T](inout s: Slice[T], let mid: usize) -> (scoped(s) Slice[T], scoped(s) Slice[T]) pre mid <= s.len { ... }
pub fn sort[T: Ord + Copyable](inout s: Slice[T]) { ... }
pub fn try_sort_by[T: Copyable, E](inout s: Slice[T], let less: fn(let T, let T) -> bool raises E) raises E { ... }
pub fn binary_search[T: Ord + Copyable](let s: Slice[T], let key: T) -> Option[usize] { ... }
```

### std.net  (`std/net.fors`)
```fors
pub enum Error { ... }
pub enum TimeoutError { ... }
pub struct Net { ... }
impl Net {
    pub fn resolve_into(let self: Self, let host: Str, inout into: Slice[Addr]) -> usize raises Error { ... }
    pub fn connect(let self: Self, let a: Addr) -> Conn raises Error { ... }
    pub fn listen(let self: Self, let a: Addr) -> Listener raises Error { ... }
}
pub struct Addr { ... }
impl Addr {
    pub fn v4(let octets: Array[u8, 4], let port: u16) -> Addr { ... }
    pub fn v6(let octets: Array[u8, 16], let port: u16) -> Addr { ... }
    pub fn port(let self: Self) -> u16 { ... }
}
pub struct Conn { ... }
impl Linear for Conn {}
impl Conn {
    pub fn read_into(inout self: Self, inout into: Slice[u8]) -> usize raises Error { ... }
    pub fn write_all(inout self: Self, let bytes: Slice[u8]) raises Error { ... }
    pub fn wait_until(inout self: Self, let deadline: time.Instant) raises TimeoutError { ... }
    pub fn shutdown(sink self: Self) raises Error { ... }
}
impl io.Reader for Conn {
    fn read(inout self: Self, inout into: Slice[u8]) -> usize raises io.Error { ... }
}
impl io.Writer for Conn {
    fn write(inout self: Self, let bytes: Slice[u8]) -> usize raises io.Error { ... }
    fn write_all(inout self: Self, let bytes: Slice[u8]) raises io.Error { ... }
    fn flush(inout self: Self) raises io.Error { ... }
}
pub struct Listener { ... }
impl Linear for Listener {}
impl Listener {
    pub fn accept(inout self: Self) -> Conn raises Error { ... }
    pub fn close(sink self: Self) { ... }
}
```

### std.proc  (`std/proc.fors`)
```fors
pub enum Error { ... }
pub struct Exec { ... }
impl Exec {
    pub fn run(let self: Self, let prog: Str, let args: Slice[Str]) -> Child raises Error { ... }
}
pub struct Child { ... }
impl Linear for Child {}
impl Child {
    pub fn pid(let self: Self) -> u64 { ... }
    pub fn wait(sink self: Self) -> i32 raises Error { ... }
}
pub fn hardware_threads() -> usize { ... }
```

### std.rand  (`std/rand.fors`)
```fors
pub struct Rng { ... }
impl Rng {
    pub fn fill(inout self: Self, inout into: Slice[u8]) { ... }
    pub fn u64(inout self: Self) -> u64 { ... }
}
pub struct Pcg { ... }
impl Pcg {
    pub fn seeded(let seed: u64) -> Pcg { ... }
    pub fn u64(inout self: Self) -> u64 { ... }
    pub fn bounded(inout self: Self, let n: u64) -> u64 pre n > 0 { ... }
    pub fn fill(inout self: Self, inout into: Slice[u8]) { ... }
}
```

### std.time  (`std/time.fors`)
```fors
pub struct Clock { ... }
pub struct Instant { ... }
pub struct Wall { ... }
pub struct Duration { ... }
impl Clock {
    pub fn now(let self: Self) -> Instant { ... }
    pub fn wall(let self: Self) -> Wall { ... }
    pub fn sleep(let self: Self, let d: Duration) { ... }
}
impl Instant {
    pub fn since(let self: Self, let earlier: Instant) -> Duration pre earlier.nanos <= self.nanos { ... }
}
```

## 5. Complete examples

16 whole ACCEPTED programs: the smallest single-file test per listed chapter that adds new top-level keyword coverage, chosen deterministically by (byte size, path).

#### `tests/conformance/01-ownership/conv-convention-present-accepted.fors`
```fors
//! name: conv-convention-present-accepted
//! rule: 01.R1
//! expect: parse-ok
//! detail: n/a

needs { };

fn touch(let i: usize) {
    discard i;
}
```

#### `tests/conformance/01-ownership/defer-reverse-order-run-ok.fors`
```fors
//! name: defer_reverse_order_run_ok
//! rule: 01.R23a
//! expect: run-ok
//! detail: 3\n2\n1  -- R23a: the bodies pending in a block run in REVERSE textual order at its exit

module app;
needs { io.stdout };
use std.io;

fn main(inout out: io.Stdout) {
    defer out.write_line("1");
    defer out.write_line("2");
    defer out.write_line("3");
}
```

#### `tests/conformance/01-ownership/errdefer-skipped-on-return-run-ok.fors`
```fors
//! name: errdefer_skipped_on_return_run_ok
//! rule: 01.R23b
//! expect: run-ok
//! detail: normal  -- R23b: an `errdefer` body runs on ERROR exits only; a `return` is a normal exit and skips it

module app;
needs { io.stdout };
use std.io;

enum Err { boom }

fn work(inout out: io.Stdout) raises Err {
    errdefer out.write_line("undone");
    out.write_line("normal");
    return;
}

fn main(inout out: io.Stdout) {
    work(&out) else |e| { return; };
}
```

#### `tests/conformance/01-ownership/interior-mut-inout-field-accepted.fors`
```fors
//! name: interior_mut_inout_field_accepted
//! rule: 01.R20
//! expect: parse-ok
//! detail: n/a

needs { };

struct Box { val: i64 }

fn use_it(inout b: Box) {
    b.val = 1;
}
```

#### `tests/conformance/01-ownership/shared-generic-field-with-bound-accepted.fors`
```fors
//! name: shared_impl_generic_field_with_bound
//! rule: 01.R21a
//! expect: parse-ok
//! detail: the impl declares P: Shared, so field v: P conforms

module app;
needs { };

struct Cell[P] { n: atomic[u64], v: P }
impl[P: Shared] Shared for Cell[P] {}
```

#### `tests/conformance/02-failure/contract-non-secret-accepted.fors`
```fors
//! name: contract-non-secret-accepted
//! rule: 02.R9
//! expect: parse-ok
//! detail: n/a

needs { };

fn check(let key: i64)
    pre key > 0
{
}
```

#### `tests/conformance/02-failure/contract-off-no-check-run-ok.fors`
```fors
//! name: contract-off-uniform
//! rule: 02.R10
//! expect: run-ok
//! detail: (no output)

module app.calc;
contracts: .off;

fn half(let n: i64) -> i64
    pre n >= 0
{
    return n / 2;
}

fn main() {
    let r: i64 = half(-4);
}
```

#### `tests/conformance/02-failure/extern-c-no-raises-absent-accepted.fors`
```fors
//! name: extern-c-no-raises-absent-accepted
//! rule: 02.R13
//! expect: parse-ok
//! detail: n/a

needs { };

extern "c" fn compute(let n: i32);
```

#### `tests/conformance/02-failure/trap-overflow.fors`
```fors
//! name: trap-overflow
//! rule: 02.Definitions
//! expect: trap
//! detail: overflow

needs { };

fn main() {
    let a: i8 = 127;
    let b: i8 = a + 1;
}
```

#### `tests/conformance/03-numerics/comptime-int-explicit-conversion-accepted.fors`
```fors
//! name: comptime_int_explicit_conversion_accepted
//! rule: 03.R9
//! expect: run-ok
//! detail: ok

module m;
needs { io.stdout };
use std.io;

const N: comptime_int = 5;

fn f() -> i32 {
    var x: i32 = N as i32;
    return x;
}

fn main(inout out: io.Stdout) {
    var r: i32 = f();
    if r == 5 {
        out.write_line("ok");
    } else {
        out.write_line("fail");
    }
}
```

#### `tests/conformance/03-numerics/div-zero-trap.fors`
```fors
//! name: div_zero_traps
//! rule: 03.R2
//! expect: trap
//! detail: div-zero

module m;
needs { };

fn main() {
    var x: i32 = 10;
    var y: i32 = 0;
    var z: i32 = x / y;
}
```

#### `tests/conformance/04-authority/sealed-holder-std-default-permitted-accepted.fors`
```fors
//! name: sealed_holder_std_permitted_by_default
//! rule: 04.R2b
//! expect: parse-ok
//! detail: std is permitted to hold sealed capabilities with no manifest entry (chapter's own example, verbatim)

module std.fs;
needs { syscall, fs.read, fs.write };
```

#### `tests/conformance/08-names/constraint-entry-head-earlier-param-accepted.fors`
```fors
//! name: constraint_entry_head_earlier_param_accepted
//! rule: 08.R26
//! expect: check-ok
//! detail: the head I is declared earlier in the same list

module m;

fn f[I: Iterator, I.Item: Eq]() { }
```

#### `tests/conformance/08-names/constraint-entry-head-self-accepted.fors`
```fors
//! name: constraint_entry_head_self_accepted
//! rule: 08.R26
//! expect: check-ok
//! detail: `Self` may head a constraint entry inside a trait method

module m;

trait Src {
    type Item;
    fn both[Self.Item: Eq](let self, let other: Self) -> bool;
}
```

#### `tests/conformance/09-types/rigid-drop-with-copyable-accepted.fors`
```fors
//! name: rigid-drop-with-copyable-accepted
//! rule: 09.R57
//! expect: check-ok
//! detail: T0057 -- `Copyable` implies `Droppable`

needs { };

fn f[T: Copyable](sink x: T) { }
```

#### `tests/conformance/10-std/buffer-index-past-len-trap.fors`
```fors
//! name: buffer_index_past_len_trap
//! rule: 10.S23
//! expect: trap
//! detail: bounds

needs { };

fn main() {
    var buf: Buffer[i64, 4] = Buffer.empty();
    buf[10] = 1;
}
```

## 6. Common mistakes

The most frequent diagnostic codes across the REJECTED corpus,
each with the owning rule's first sentence and the smallest
rejected single-file example (at most 25 lines).

**T0026** (16 tests) — Every expression is typed by exactly one of `synth(e)` and `check(e, T)`; the position decides which (ch03 Rule 25).
<!-- tests/conformance/09-types/return-value-mismatch-rejected.fors -->
```fors
//! name: return_value_mismatch_rejected
//! rule: 09.R31
//! expect: check-error
//! detail: T0026 -- `return e;` checks e against the declared result type

module m;

fn f() -> i32 { return true; }
```

**T0043** (11 tests) — `e.name(args)`: `S = synth(e)`, qualifiers stripped for lookup.
<!-- tests/conformance/10-std/vec-clear-linear-element-rejected.fors -->
```fors
//! name: vec_clear_linear_element_rejected
//! rule: 10.S11c
//! expect: check-error
//! detail: T0043 -- R11c(ii): `Vec.clear` is declared in the `T: Droppable` impl block, so it does not exist for a linear element type

needs { };

fn f[A: brand](inout v: Vec[Own[i64, A], A]) {
    v.clear();
}
```

**T0061** (10 tests) — Projections.
<!-- tests/conformance/09-types/projection-unknown-assoc-type-rejected.fors -->
```fors
//! name: projection_unknown_assoc_type_rejected
//! rule: 09.R61
//! expect: check-error
//! detail: T0061 -- no bound of I declares an associated type `Elem`

module m;

fn f[I: Iterator](let x: I.Elem) { }
```

**T0057** (9 tests) — A generic declaration is checked once, at its definition, with each type parameter rigid.
<!-- tests/conformance/09-types/rigid-discard-without-droppable-rejected.fors -->
```fors
//! name: rigid-discard-without-droppable-rejected
//! rule: 09.R57
//! expect: check-error
//! detail: T0057 -- `discard`ing a value of rigid type is a drop

needs { };

fn f[T](sink x: T) { discard x; }
```

**T0011** (8 tests) — A `type_app` MUST supply exactly as many arguments as its item declares parameters, each of the declared kind: a type for a type parameter, a constant for a const parameter, a brand for a `brand` parameter (kind misus...
<!-- tests/conformance/09-types/type-arity-rejected.fors -->
```fors
//! name: type_arity_rejected
//! rule: 09.R11
//! expect: check-error
//! detail: T0011 -- Option declares one parameter, two arguments are supplied

module m;

fn f(let x: Option[i32, i32]) { }
```

**T0017** (7 tests) — `impl Tr[As] for S` MUST define every required method of `Tr`, MAY redefine provided ones, MUST define every associated type of `Tr` exactly once (`type A = T;`; a second definition in the same impl is ch08 Rule 27's...
<!-- tests/conformance/09-types/assoc-type-in-inherent-impl-rejected.fors -->
```fors
//! name: assoc_type_in_inherent_impl_rejected
//! rule: 09.R17
//! expect: check-error
//! detail: T0017 -- an inherent impl must not contain a `type` item

module m;

struct Counter2 { n: i64 }
impl Counter2 {
    type Item = i64;
}
```

**T0039** (7 tests) — If a parameter is still undetermined after Rule 38(d) — a parameter that occurs only under projections (`fn g[I: Iterator](let x: I.Item)`) always is, unless given explicitly — the call MUST be rejected: "cannot infer...
<!-- tests/conformance/09-types/none-in-synth-rejected.fors -->
```fors
//! name: none_in_synth_rejected
//! rule: 09.R28
//! expect: check-error
//! detail: T0039 -- `none` in SYNTH mode has no way to determine Option's argument; write Option[u8].none

module m;

fn f() {
    let c = none;
}
```

**T0018** (6 tests) — In an `impl_decl` with `for`, the first type MUST be a trait and the second MUST NOT be one; without `for` the type MUST be a struct or enum.
<!-- tests/conformance/09-types/blanket-impl-rejected.fors -->
```fors
//! name: blanket_impl_rejected
//! rule: 09.R18
//! expect: check-error
//! detail: T0018 -- the self type is a bare type parameter; blanket impls do not exist

module m;

trait Shape { fn area(let self) -> f64; }
impl[T] Shape for T { fn area(let self: T) -> f64 { return 0.0; } }
```

**T0010** (5 tests) — There is no subtyping.
<!-- tests/conformance/09-types/rigid-to-dyn-rejected.fors -->
```fors
//! name: rigid-to-dyn-rejected
//! rule: 09.R10
//! expect: check-error
//! detail: T0010 -- a value of RIGID type MUST NOT be coerced to `dyn Tr`; a generic body that wants an object takes `dyn Tr` as a parameter

needs { };

trait Tr { fn go(let self); }

fn f[T: Tr](sink x: T) -> dyn Tr {
    return x as dyn Tr;
}
```

**T0021** (5 tests) — The operator-trait set is closed; no other operator is overloadable and no other trait is consulted by an operator.
<!-- tests/conformance/10-std/container-of-linear-not-iterated-by-value-rejected.fors -->
```fors
//! name: container_of_linear_not_iterated_by_value_rejected
//! rule: 10.S33
//! expect: check-error
//! detail: T0021 -- no linear `Item` can exist (R32, ch09 R21), so a container of LINEAR elements is emptied by `pop`/`remove`, never iterated by value

needs { };

fn f[A: brand](let v: Vec[Own[i64, A], A]) -> usize {
    return v.iter().count();
}
```

**T0033** (5 tests) — `never`.
<!-- tests/conformance/09-types/let-never-rejected.fors -->
```fors
//! name: let_never_rejected
//! rule: 09.R33
//! expect: check-error
//! detail: T0033 -- a binding must not be given type never by synthesis

module m;

fn die() -> never { return die(); }
fn f() {
    let x = die();
}
```

**T0012** (4 tests) — Bounds MUST hold at every use: for each argument `X` given to a parameter `P: Tr1 + ... + Trk`, `X` MUST implement every `Tri`.
<!-- tests/conformance/09-types/projection-head-without-impl-rejected.fors -->
```fors
//! name: projection_head_without_impl_rejected
//! rule: 09.R20
//! expect: check-error
//! detail: T0012 -- I := Plain is given explicitly, Plain has no Iterator impl, so neither the bound holds nor can Plain.Item be normalised; one root cause, reported once

module m;

struct Plain { n: i64 }
fn count[I: Iterator](let n: i64) -> i64 { return n; }
fn f() -> i64 { return count[Plain](1); }
```

**T0019** (4 tests) — Overlap.
<!-- tests/conformance/09-types/overlap-generic-vs-concrete-rejected.fors -->
```fors
//! name: overlap_generic_vs_concrete_rejected
//! rule: 09.R19
//! expect: check-error
//! detail: T0019 -- Pair[T] unifies with Pair[i32]

module m;

trait Shape { fn area(let self) -> f64; }
struct Pair[T] { a: T, b: T }
impl[T] Shape for Pair[T] { fn area(let self: Pair[T]) -> f64 { return 0.0; } }
impl Shape for Pair[i32] { fn area(let self: Pair[i32]) -> f64 { return 1.0; } }
```

**T0050** (4 tests) — A pattern is checked against the scrutinee's type `S` (`synth` of the `match` head).
<!-- tests/conformance/09-types/pattern-float-literal-rejected.fors -->
```fors
//! name: pattern_float_literal_rejected
//! rule: 09.R50
//! expect: check-error
//! detail: T0050 -- float literals are not patterns

module m;

fn f(let x: f64) -> i32 {
    match x {
        1.5 => 1,
        _ => 0,
    }
}
```

**T0024** (3 tests) — A marker trait (`Shared`, `Copyable`, and from round 6 `Linear` and `Droppable`) has no methods and contributes no operation to a generic body; as a bound it only restricts instantiation (ch01 Rule 21b).
<!-- tests/conformance/09-types/dyn-marker-rejected.fors -->
```fors
//! name: dyn_marker_rejected
//! rule: 09.R24
//! expect: check-error
//! detail: T0024 -- a marker trait must not be used as dyn

module m;

fn f(let x: dyn Copyable) { }
```

**T0027** (3 tests) — Literals.
<!-- tests/conformance/09-types/int-literal-to-float-rejected.fors -->
```fors
//! name: int_literal_to_float_rejected
//! rule: 09.R27
//! expect: check-error
//! detail: T0027 -- an integer literal must not check against a float type; write 1.0

module m;

fn f() -> f64 {
    let a: f64 = 1;
    return a;
}
```

**T0035** (3 tests) — Closures.
<!-- tests/conformance/09-types/closure-synth-unannotated-rejected.fors -->
```fors
//! name: closure_synth_unannotated_rejected
//! rule: 09.R35
//! expect: check-error
//! detail: T0035 -- in SYNTH mode every closure parameter must carry a type

module m;

fn f() {
    let g = |let n| n;
}
```

**T0048** (3 tests) — Member clashes (left open by ch08 Rule 27) are errors at the later declaration: two inherent methods or associated functions of one head with the same name, in the same or different `impl` blocks; an inherent member n...
<!-- tests/conformance/09-types/method-named-as-field-rejected.fors -->
```fors
//! name: method_named_as_field_rejected
//! rule: 09.R48
//! expect: check-error
//! detail: T0048 -- an inherent member named like a field of the struct

module m;

struct P { x: i32 }
impl P { fn x(let self: P) -> i32 { return 0; } }
```

**T0053** (3 tests) — A `match` MUST be exhaustive.
<!-- tests/conformance/09-types/match-int-needs-wildcard-rejected.fors -->
```fors
//! name: match_int_needs_wildcard_rejected
//! rule: 09.R53
//! expect: check-error
//! detail: T0053 -- integer literals have an infinite domain; e.g. 1 is uncovered

module m;

fn sign(let n: i32) -> i32 {
    match n {
        0 => 0,
        -1 => -1,
    }
}
```

**T0054** (3 tests) — An arm that is not useful with respect to the arms before it MUST be rejected as unreachable.
<!-- tests/conformance/09-types/arm-after-let-pattern-unreachable-rejected.fors -->
```fors
//! name: arm_after_let_pattern_unreachable_rejected
//! rule: 09.R54
//! expect: check-error
//! detail: T0054 -- `let n` is irrefutable, so no later arm is useful

module m;

fn f(let n: i32) -> i32 {
    match n {
        let other => other,
        0 => 0,
    }
}
```

**T0062** (3 tests) — Constraint entries.
<!-- tests/conformance/09-types/constraint-entry-in-struct-generics-rejected.fors -->
```fors
//! name: constraint_entry_in_struct_generics_rejected
//! rule: 09.R62
//! expect: check-error
//! detail: T0062 -- constraint entries are legal only in the generics of a fn

module m;

struct Sorted[I: Iterator, I.Item: Ord] { it: I }
```

**T0013** (2 tests) — A generic parameter whose bound is a type (Rule 15) is a const parameter; that type MUST be an integer type or `bool`.
<!-- tests/conformance/09-types/const-param-float-rejected.fors -->
```fors
//! name: const_param_float_rejected
//! rule: 09.R13
//! expect: check-error
//! detail: T0013 -- a const parameter's type must be an integer type or bool

module m;

struct Scaled[K: f64] { v: i32 }
```

**T0014** (2 tests) — A type of infinite size MUST be rejected.
<!-- tests/conformance/09-types/recursive-struct-rejected.fors -->
```fors
//! name: recursive_struct_rejected
//! rule: 09.R14
//! expect: check-error
//! detail: T0014 -- List stores an Option[List] by value: infinite size

module m;

struct List { head: Option[List] }
```

**T0016** (2 tests) — A `trait` declares methods and associated types (ch07 `trait_item`).
<!-- tests/conformance/09-types/self-receiver-wrong-type-rejected.fors -->
```fors
//! name: self_receiver_wrong_type_rejected
//! rule: 09.R16
//! expect: check-error
//! detail: T0016 -- a parameter named self must have type Self

module m;

trait Shape {
    fn area(let self: i32) -> f64;
}
```

**T0023** (2 tests) — `Copyable` is a checked marker trait with no methods.
<!-- tests/conformance/09-types/copyable-with-own-field-rejected.fors -->
```fors
//! name: copyable_with_own_field_rejected
//! rule: 09.R23
//! expect: check-error
//! detail: T0023 -- Own is never Copyable, so a struct holding one cannot be

module m;

struct H[A: brand] { p: Own[i64, A] }
impl[A: brand] Copyable for H[A] { }
```

## 7. Tools

`fors check <path>` — type-check and lint one file or package; human output.
`fors check --format json <path>` — JSON Lines: one "diagnostic" record per
error (`code`, `rule`, a byte+line+col range, and `fixes`, each carrying an
`applicability` of `machine-applicable` | `maybe-incorrect` |
`has-placeholders`), then one trailing "summary" record.
`fors explain <CODE>` — the rule text and rationale behind one diagnostic code.
`fors explain --list` — every diagnostic code this build knows, one per line.
`fors fmt` — the one canonical style: 4-space indent, 100-column target.
Run `fors check` after every edit, not only before a commit.
Apply a suggested fix automatically ONLY when its `applicability` is
`machine-applicable`; treat `maybe-incorrect` and `has-placeholders` fixes as
drafts for a human (or a slower review pass) to confirm.
The compiler is the arbiter of what Fors accepts. This pack is a guide for
getting a first draft close; when it disagrees with `fors check`, the
compiler wins and this pack is stale.
