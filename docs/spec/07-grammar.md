# Chapter 07 — Lexical Structure and Grammar

## Status

Draft, M0.5, 2026-09-19; round-5 owner decisions applied 2026-09-19 (see
"Closed by owner decision 2026-09-19, round 5"). Verified against every
`fors` example in ch01-06 (see Coverage). Implements PLAN "Surface"
(grammar parseable with no symbol table; generics in `[...]`) and fixes
the PLAN §4.3(3) syntax calls, now confirmed by the owner: mandatory `;`
with no ASI, and the flat bitwise tier.

## Scope

Owns exclusively: tokens, keywords (reserved and contextual), literals,
comments, the operator table, every syntax production, the lookahead
bound, and parser error-recovery synchronisation. The grammar is parseable
per file, independently and in parallel, to a lossless CST (whitespace and
comments kept as trivia) with no symbol table, no type information and no
backtracking. Defines no semantics: what a `Bracket` resolves to, what a
pattern binds, which expression is a legal `place`, whether a literal is in
range, are other chapters' facts; this chapter fixes only that the
token/production exists and how it parses.

## Lexical grammar

Source is UTF-8. Non-ASCII characters are legal only inside comments and
string literals. The lexer is context-free (no parser feedback), maximal
munch, and needs at most 2 characters of lookahead past the current one.

1. **Whitespace** (space, tab, CR, LF): trivia, separates tokens. There is
   no automatic semicolon insertion; newlines are never significant except
   as the terminator of `//` comments and `\\` string lines.
2. **Line comment**: `//` to end of line. **Block comment**: `/*` ... `*/`,
   nesting. After the opener the lexer keeps a depth counter, scanning raw
   characters: `/*` increments, `*/` decrements, nothing else is
   recognised (quotes and `//` are inert inside). EOF at depth > 0 is one
   error token to EOF. `a /*b` therefore opens a comment, as in C.
3. **Identifier**: `[A-Za-z_][A-Za-z0-9_]*`, longest match, then looked up
   in the reserved table (`inout` is one token, never `in`+`out`). The
   single character `_` alone is the token `_`, not an identifier.
4. **Number**: `dec = digit { ["_"] digit }`.
   - integer: `dec` | `0x` hex digits | `0o` octal digits | `0b` binary
     digits (same `_` rule);
   - float: `dec "." dec [exp]` | `dec exp`, `exp = [eE] [+-]? dec`.
     A `.` continues a number **only if the next character is a digit**; an
     `e`/`E` starts an exponent only if followed by a digit, or by `+`/`-`
     and a digit. So `1..<2` is `1` `..<` `2`; `1.` is `1` `.`; `1.e3` is
     `1` `.` `e3` (field access); `.5` is `.` `5` (a parse error: no
     leading-dot floats); `1.5..<2.5` is `1.5` `..<` `2.5`.
   - suffix: an identifier run glued to the literal (`300u32`, `1.5f32`).
     Legal suffixes: `i8 i16 i32 i64 u8 u16 u32 u64 isize usize f32 f64`;
     hex/octal/binary literals take integer suffixes only (`0xFFu8` is
     unambiguous because `u`/`i` are not hex digits; `0x1f32` is the hex
     integer 0x1f32). Any other glued identifier run is a lexical error.
   - A leading `-` is **never** part of a literal (Disambiguation 8).
5. **String**: `"` ... `"` on one line; escapes `\n \r \t \0 \\ \" \xHH
   \u{H..}`. A raw newline or EOF inside is an error token ending at the
   line end.
6. **Multiline string**: the two characters `\\` at token start begin a
   string line that runs to (not including) the line end; no escapes are
   processed. Consecutive `\\` lines separated only by whitespace form one
   literal, joined with `\n`; a comment between them ends the literal. `\`
   is not otherwise a token, and inside `"..."` the lexer is already in
   string mode, so `"a\\b"` is unaffected. The statement's `;` goes on a
   later line.
7. **Punctuation and operators** (longest match):
   `( ) [ ] { } , ; : . @ ? -> => = == != < > <= >= + - * / % & | ^ << >>
   ..< ..= += -= *= /= %= &= |= ^= <<= >>=`.
   Deliberately **not** tokens: `&out` (always `&` then identifier `out`),
   `||` and `&&` (so an empty closure `||` is two `|`), `!`, `~`, `..`,
   `...`, `?.`, `??`, `::`, `<-`, `'`. `..` not followed by `<` or `=` is a
   lexical error. No munch hazard exists from `>>`/`>=`/`]]` because
   generics use `[ ]` and `]` is always a single token.

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

## Grammar

ISO-style EBNF; `,` concatenation is omitted for readability. A production
name ending `_ns` is the same production with struct literals disabled
(Disambiguation 1).

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

`()` is the unit value / unit type, `(e)` a parenthesised expression /
type, `(e,)` a 1-tuple, `(a, b)` a tuple: decided by whether a `,` follows
the first element, inside one production, no lookahead.

An `asm_expr`'s `asm_item` list MUST contain at least one `string_lit`
item (an instruction). This is a syntactic constraint: a block with none
MUST be a parse error (both parsers count the items; it needs no name or
type information), although the EBNF above does not encode it. Whether an
`asm_expr` has an expected type is NOT syntactic: that is a checker rule
(ch04 Rule 27).

## Disambiguation rules

Every choice below is made on the current token plus at most one more
(LL(2)); nothing is re-scanned.

1. **Struct literal vs block.** `expr_ns` is used for the head of `if`,
   `while`, `match`, `for ... in`, `parallel for`/`simd for` (iterable and
   `grain`), and every contract clause (`pre i < self.len` is followed by
   the body `{`). In `_ns` mode `primary_expr` has no `struct_lit`
   alternative, so `{` after the head is always the block. The mode is a
   parser flag, cleared inside any `( )`, `[ ]` or `{ }` nested in the
   head and restored after; write `if (P { x: 0 }) == p { }`. Everywhere
   else `path {` and `path [args] {` is a struct literal; no other
   construct places `{` after an expression in normal mode (`with` and
   `raises` heads end in a *type*, which never contains `{`).
2. **`|`.** At the start of a `primary_expr`: closure. After a complete
   `cast_expr`: bitwise-or. After `else` that follows a call's `)`:
   handler binder. At the start of an `arg_value` when the next token is
   `,` or `)`: bare operator. Closure body: `{` means block (no expression
   starts with `{`), anything else is an `expr`, taken greedily
   (`|a| a | b` has body `a | b`).
3. **`else`.** A `handler` exists only directly after a call's `)`
   (ch02 Rule 5), so `f()? else |e| {}` and `{ ... } else |e| {}` do not
   parse. After an `if_expr` block, `else` is followed by `if` or `{`;
   after a call `)`, by `|`. The then-block of an `if` ends in `}`, never
   in `)`, so the two never compete.
4. **`&`, `&out`, `move`.** `&` begins an expression nowhere except the
   start of an `arg_value`, so infix `&` is always bitwise-and. At
   `arg_value` start: `&` followed by `,`/`)` is `bare_op`; otherwise the
   inout/set marker, and then the identifier `out` followed by another
   identifier is the set marker (`&out x`), else `out` is the binding
   (`c.get_into(url, &out)?`, ch04). `move` is reserved and is an ordinary
   prefix operator (`move w.net`, `f(move b)`).
5. **`[`.** Directly after the name in `fn`/`struct`/`enum`/`trait`, or
   directly after `impl`: `generics`. After a `path` in a type: `targ`
   list. After a complete postfix expression: `Bracket`. At the start of a
   primary (including statement start): array literal. Attributes take
   `( )`, never `[ ]`. Statement-form `if`/`match`/`comptime`/`for`/... end
   at their `}`, so a following `[` starts a new statement.
6. **Named argument / attribute argument.** Identifier followed by `:` is
   a label (LA 2); there is no other `ident ":"` in expressions.
7. **Bare operator argument** (`reduce(+, xs, identity: 0.0)`). At
   `arg_value` start an operator token that cannot begin an expression is
   a `bare_op` (LA 1); `-`, `|`, `&` are `bare_op` iff the next token is
   `,` or `)` (LA 2). Syntactically legal in any call; the checker
   restricts it to parameters of operator kind.
8. **Unary minus and literals.** `-` is never lexed into a number. `-128i8`
   is `unary_expr("-", number)`; the CST keeps that shape, and ch03's
   literal range check is applied to the negated value when the operand of
   `-` is directly a literal. `x - 1`, `x + -1`, `x - -1`, `-x.abs()`
   (= `-(x.abs())`), `-1 as i8` (= `(-1) as i8`) all follow from the
   level table.
9. **Statement start.** One token selects the statement: a statement
   keyword; `@` (attribute block); `{` (block); `if`/`match`/`comptime`
   (statement form: ends at its `}`, no `;`, and is not continued by a
   binary or postfix operator); anything else parses one `expr`, and the
   *following* token decides: `assign_op` means assignment, `;` means
   expression statement, `}` means the block's tail value. For an
   assignment the already-built left CST must have the shape of `place`;
   otherwise a syntax error is reported at the operator (a check on the
   built node, not a re-parse). There are no labels. A final statement-form
   `if`/`match`/`comptime` is also the block's tail value.
   `defer` and `errdefer` are statement keywords like the rest, so the
   current token alone selects `defer_stmt`/`errdefer_stmt` (LA 1). After
   the keyword the current token alone decides the body (LA 1): `{` is a
   `block` — no `expr` begins with `{`, the argument of Disambiguation 2 —
   and anything else begins an `expr` that ends at its `;`. A reserved word
   is never the head of a `path`, so the struct-literal question of
   Disambiguation 1 cannot arise after either keyword, and `defer P { x: 1
   };` is the `expr` form holding a `struct_lit`. The `expr ";"` form means
   exactly `{ expr; }`. An assignment is a `stmt`, not an `expr`, so
   `defer x = 1;` is a parse error at `=` (Error recovery). Both decisions
   are one token; the chapter's bound stays 2.
10. **Contextual keywords.** Exactly the table above; outside its slot the
    word is an identifier (`inout arena: ...`, `arena.alloc(...)`,
    `inout out: Slice[u8]`, `out[i] = ...` are all attested).
11. **Generic arguments: type or expression?** In *expression* position a
    `bracket_arg` is an `expr` unless its first token is `iso`, `imm`,
    `secret`, `fn` or `dyn` (all reserved), when it is a `type`.
    `wrap_as[u8]()`, `xs[i]`, `f[Vec[T]]()`, `f[(i32, u8)]()` parse as
    expressions and the checker reinterprets path/Bracket/tuple shapes as
    types. In *type* position a `targ` is chosen by its first token:
    number, string, `true`/`false` or `-` means `const_arg`; `(`, `fn`,
    `dyn` or a qualifier means `type`; an identifier parses a `type`, and
    if that type is a bare `path` and the next token is `+ - * / %` the
    path becomes the first operand of the `const_arg` `add_expr`
    (`Array[T, N + 1]`, `vector[f64, 8]`). A bare `path` targ is one CST
    node the checker classifies as type or constant. A const argument in
    type position that starts with `(` or contains a call must be hoisted
    into a `const`.
12. **`cmp_expr` alternatives.** Both start with `cast_expr`: parse one,
    then a bitwise operator selects `bit_expr`; otherwise the operand
    seeds `mul_expr`/`add_expr`. `a + b & c`, `a & b + c`, `a & b | c`,
    `a & b == c`, `a << b << c`, `a < b < c` are syntax errors with the
    fixed hint "parenthesize".
13. **`path` vs `.name`.** A primary `path` takes `.ident` greedily;
    `.ident` after a call/Bracket/`?` is the postfix form. A `dot_lit` is
    recognised only at primary (or pattern, or `contracts:`) start. Tuple
    index fields (`t.0`) do not exist, so `t.0.1` never meets the float
    rule.
14. **`fn_type` tail.** `-> T raises E` binds to the innermost `fn` type;
    parenthesise the type to attach it elsewhere.
15. **`pub use` vs `pub` decl.** LA 2 on the token after `pub`.
16. **`asm_item` choice.** Inside an `asm_expr` block, the current token
    `in` selects `"in" "(" ident ")" "=" expr`; `out` or `clobber` followed
    by `(` (LA 2) selects that item; anything else is the `string_lit`
    item. `in` is already reserved (Keywords — reserved); `out`/`clobber`
    are contextual only here.
17. **`let` inside a pattern.** `let` is already reserved, so it never
    starts a `path`/`dot_lit`/tuple pattern; one token of lookahead (the
    current token) is enough to choose the `"let" ident` alternative of
    `pattern` and of `fpat`. Inside a `payload`'s `{ }` list an `fpat`
    starting with `let` is the binding form; anything else must be
    `ident ":" pattern` (LA 1: the token after the identifier is checked
    to be `:`, never `,` or `}` — see Error recovery below). `"let"` is
    followed by exactly one `ident`: `_` is its own token, not an `ident`,
    so `let _` is a parse error (the wildcard is written `_`), and a
    pattern binding takes no type annotation, so `let x: T` in a pattern
    is a parse error at `:` (the token after a pattern must be `=>`, `,`,
    `)` or `}`).
18. **`as` in a `use_item`.** A `use_item` is not an expression: `path` is
    followed by `as`, `,` or `;` only, so the `as` of an import alias can
    never be confused with the `as` of a `cast_expr` (which occurs only
    inside `expr`), and the token after `as` must be an `ident` (not a
    `type`, not `_`). LA 1.

19. **Generics entry: parameter or constraint.** At the start of a
    `gentry` the current token is an `ident`; the NEXT token decides (LA
    2): `.` selects `gconstraint` (`I.Item: Add + Copyable`); `:`, `,` or
    `]` selects `gparam`. A `gconstraint` is exactly two identifiers
    joined by one `.`, then a mandatory `:` and `bounds`; its bound list
    never contains `brand` (that word is contextual in the `gparam` slot
    only, so here it would be an ordinary type path). `Self` is an
    ordinary `ident` token, so `Self.Item: Eq` is a `gconstraint`. A
    `generics` list MAY consist of constraints only (a method constraining
    a parameter of its `impl`). That the head names a type parameter
    declared EARLIER in the same list, a parameter of the enclosing
    `impl`/`trait`, or `Self` is ch08 Rule 26's; that the second
    identifier is an associated type of one of the head's bounds is ch09
    Rule 61's. There is no equality form: `[I: Iterator, I.Item = i64]`
    is a parse error at `=` (Error recovery).
20. **`type` in a `trait` / `impl` body.** `type` is reserved, no
    `fn_sig`, attribute or `pub` starts with it, so the current token
    alone (LA 1) selects `assoc_type_decl` (in a `trait_decl`) or
    `assoc_type_def` (in an `impl_decl`). The two forms are not
    interchangeable: after the `ident`, a `trait` body accepts `:` or `;`
    and an `impl` body accepts only `=`. An associated-type item takes no
    `attribute`, no `pub` and no `generics` (its visibility is ch08 Rule
    11's; generic associated types do not exist); `@a type T;`,
    `pub type T = X;` and `type T[U];` are parse errors. `type` is never
    part of a `type`: a projection is written as the ordinary dotted
    `path` `I.Item` / `Self.Item` inside `type_app`, with no new type
    syntax (its second segment is deferred, ch08 Rule 16).
21. **Receiver shorthand: `self` with no type.** Owner decision
    2026-09-19, round 5 (D1). In a `param`, after the mandatory
    `convention`, the current token is an `ident`; ONE token of lookahead
    (LA 2) decides: `:` selects `convention ident ":" type`; anything
    else (`,` or `)` in a well-formed list) selects the shorthand
    `convention "self"`, whose type is `Self`. `fn next(inout self)` and
    `fn next(inout self: Self)` are the same signature. Two restrictions,
    both syntactic and both checked by the parser at the point it takes
    the second alternative: the identifier MUST be spelled exactly
    `self` (`self` is an ordinary identifier token, ch07 "Keywords — not
    reserved"), and the `param` MUST belong to a `fn_sig` of a
    `trait_item` or an `impl_item`. A parameter that is not `self` and
    omits its `":" type`, and a `self` shorthand in a free function's
    `params`, are both the same parse error with the fixed message:
    `only a parameter named "self", in a trait or impl body, may omit
    its type annotation`, recovered like any other malformed `param` (at
    the next `,` or the closing `)`). A free function MAY still declare
    an ordinary parameter *named* `self` with an explicit type
    (`fn f(let self: i32)`): nothing in ch07-ch09 forbids it — ch09 Rule
    16's "a method whose first parameter is named `self` MUST give it the
    type `Self`" is about a `trait`/`impl` method only — so the
    shorthand's restriction is the only new rule here, not a ban. Two
    neighbouring productions are untouched, and their answers are fixed
    here so nobody re-derives them: a closure parameter is a `cparam`
    (`ident [ ":" type ]`), whose annotation was always optional, so
    `|self| self` parses in ANY body — inside a method it is an ordinary
    binding that shadows the receiver (ch08 Rule 18, N0018), in a free
    function it is just a name; and a `trait`/`impl` method that writes
    `self` WITH an explicit non-`Self` type (`fn area(let self: i32)`)
    parses as the annotated form and is ch09 Rule 16's error (T0016), not
    a parse error. Tests: 08-names `closure-param-named-self-{shadows-
    receiver-rejected,in-free-fn-accepted}`, 09-types
    `self-receiver-wrong-type-rejected`.

**Largest lookahead:** 2 tokens (rules 2, 4, 6, 7, 15, 16, 19, 21 and the
`scoped` / closure-`set` slots); lexer, 2 characters past the current one
(`..<`, exponent sign).

## Error recovery

Recovery is panic-mode with a fixed synchronisation set; one diagnostic
per recovery.

- **Declaration sync set**: `module`, `use`, `struct`, `enum`, `trait`,
  `impl`, `const`, `extern`, `fn` followed by an identifier (`fn (` is a
  type), `pub` followed by one of these, and identifier `soa` followed by
  `struct`. None of
  these can occur inside a function body, so on meeting one while inside a
  body the parser reports "unclosed `{`/`(`/`[` opened at ..." once, closes
  every open construct up to the enclosing item list (the `impl`/`trait`
  body for `fn`, the file otherwise) and resumes there. A missing `}`
  therefore never damages the next declaration. A run of `attribute`s
  immediately before the sync token belongs to the resumed declaration.
- **Statement sync set**: `;` and `}` at the current nesting depth, and at
  statement start `let var if match for while break continue return raise
  with parallel simd spawn consume discard defer errdefer comptime`. If `;` is expected
  and the current token is in this set or is `}`, the parser reports
  "missing `;`" at the end of the previous token, inserts it virtually and
  continues without skipping anything.
- Otherwise tokens are skipped, tracking bracket depth, to the nearest
  member of either set. Lexical error tokens are reported once and skipped.
- **Removed `fpat` shorthand.** An `fpat` that is a bare `ident` (no `:
  pattern` and no `let`) is a parse error, reported at the identifier, with
  the fixed message: `write "let x" to bind the field or "x: pattern"`.
  This is a dedicated diagnostic, not a fall-through to the declaration or
  statement sync sets: the parser has already committed to `fpat` (it is
  inside a `payload`'s `{ }`), so it reports and resumes at the next `,` or
  the closing `}` like any other `fpat` item, without unwinding further.

- **Associated-type items.** Inside a `trait`/`impl` body the item sync
  set is `fn`, `type`, `pub`, `@` and the closing `}`; a malformed
  `assoc_type_decl`/`assoc_type_def` reports once and resumes after its
  `;` or at the next member of that set. Three dedicated diagnostics, each
  reported once and recovered in place like the `fpat` one: `type` where a
  `decl` is expected (file level): `type aliases do not exist; "type" is
  legal only inside a trait or impl body`, then skip to `;`; `type A = T;`
  inside a `trait` body: `a trait declares "type A;" - the definition
  belongs in an impl` (no defaults in v0.1); `type A;` or `type A: B;`
  inside an `impl` body: `an impl defines "type A = T;"`.
- **Equality bound.** In a `gentry`, `=` after `ident "." ident` (or
  after a `gparam`'s `ident`) is a parse error with the fixed message
  `associated-type equality bounds do not exist; constrain with ":"`,
  recovering at the next `,` or `]` of the list.

## Coverage

Every fenced `fors` block of ch01-06 (ch06 has none) was derived from the
EBNF. Productions each needed beyond the obvious: ch01 ex1 `ret_type` with
`scoped` inside a tuple, contract in `_ns` mode, `bracket` holding a
range, tuple `binding`; ex2 `with_stmt`, `struct_lit` as argument,
assignment to a Bracket place, `gparam` `brand`, `arena` as identifier;
ex3 `parallel_for_stmt`, `out` as identifier; ex4 qualifiers, `?`.
ch02 ex1-4 optional `module_hdr`, `contracts_clause` before
`needs_clause`, `impl ... for`, `raise_stmt`, `handler`. ch03 ex1 `as`;
ex2 `attr_block_stmt`; ex3 `bare_op`, named arg; ex4 `gparam` bound, const
`targ`, `if_expr` as value. ch04 `use_decl` list, `move` prefix, string
arg, `&buf.slice`, `&out` on a binding named `out`, attributed
`extern_fn_decl`. ch05 argument-less attribute, numeric `targ`s.

## Rejected alternatives

- `&out` as one token: breaks `&out)` where `out` is a binding (ch04).
- Bitwise operands at additive level (first draft): accepts `a + b & c`.
- `not` as a level-2 prefix as well as level 8: two parses of `not a == b`.
- `?` followed by `else |e|`: ch02 Rule 1 makes them alternatives.
- Contextual `iso`/`imm`/`secret`/`raises`/`as`/`in`/`extern`: `-> iso
  raises E` and `x as T grain n` become order-dependent; reserving them
  keeps every type start LL(1).

## Drafting decisions

- `module` header is optional in the grammar (ch01/03/05 examples are
  header-less); whether a build unit requires one is ch04's.
- Header order is `module`, `contracts:`, `needs`, `inputs`, `use` (ch02
  decision, ch04 Rules 1, 13); the first draft had `needs` first.
- `asm` is reserved from v0.1 (owner decision 2026-09-19, round 2, R2-4);
  `out`/`clobber` stay contextual, scoped to `asm_item`, per the usual
  policy of not reserving a word that is common as an identifier.
- `use` is the import keyword (all examples); `import`, `recover` stay
  reserved-unused because un-reserving later is compatible, reserving
  later is not.
- Reserved beyond the handed-down list: `in as and or not true false
  extern inout sink iso imm secret raises dyn consume discard break
  continue`. `set` stays contextual (too common as a method/binding name);
  `reduce` and `unsafe` are *not* reserved (`reduce(...)` must parse as a
  call, `@unsafe` as an ordinary attribute; `unsafe { }` still fails, as a
  malformed struct literal or in the checker — ch04 test).
- Bitwise tier (PLAN §4.3(3), owner's call): flat, operands at cast
  level, same-operator chains for `& | ^`, shifts single-use, no mixing
  with anything but `not`/`and`/`or` — in the EBNF.
- `as` is its own level between prefix and `*`.
- `;` is mandatory; no ASI (surface-language.md; PLAN §4.3(3) still open).
- `&`/`&out` are argument markers only, not general prefix operators.
- `if` and `match` are expressions with a statement form; `with`, loops,
  `parallel`, `spawn` are statements only (ch01 Rule 15).
- Added because a parser cannot be written without them, all unattested:
  `break`/`continue` (unlabelled), `consume`/`discard` statements (ch01
  Rule 8), `let x: T;` without initialiser (needed for `&out x`), `..=`,
  `true`/`false`, hex/octal/binary and `_` in numbers, unit `()`, tuple
  and literal patterns, `[e; n]`, inherent and generic
  `impl`, body-less trait methods, `+`-joined bounds, `dyn T`, `pub`
  fields, `pub use`, `fn` types with conventions and `raises`, closure
  param conventions, struct-level `invariant`.
- Closed by owner decision 2026-09-19, round 3 (D1/D2): the `fpat`
  shorthand `ident` alone (bind-by-field-name) is REMOVED; a pattern binds
  a name only by writing `"let" ident`, in `pattern` directly or as the
  `fpat` form `"let" ident`. `"var" ident` is NOT a pattern alternative:
  patterns do not introduce mutable bindings (mutable pattern bindings are
  an open owner question — this draft recommends "no", see ch08). `use`
  gained an optional `"as" ident` per `use_item`; `"as"` was already
  reserved for casts, so no new keyword is needed.
- Owner decision 2026-09-19, round 4 (associated types): `trait_item`
  gains `assoc_type_decl`, `impl_decl`'s body becomes `{ impl_item }` with
  `assoc_type_def`, `generics` entries become `gentry` (parameter or
  `gconstraint`), `bounds` is factored out of `gparam` (same language as
  before), and `type` becomes RESERVED. No spec example and no corpus file
  used `type` as an identifier (checked by grep over `docs/spec` and
  `tests/conformance`), so nothing was migrated. A projection needs no
  production: `I.Item` is already a `path`. Deliberately not added (each
  can be added later without breaking accepted code): generic associated
  types, associated-type defaults, associated consts, equality bounds
  (`I.Item = T`), supertraits (`trait A: B`), a qualified projection
  `(P as Tr).A`, a `where` clause. Constraint entries live inside
  `generics` rather than in a `where` clause because the list is already
  the one place bounds are written (ch09 Rule 15) and the head-is-earlier
  rule keeps it a single left-to-right pass.
- Not added: char literals, labels, match guards, `|`-patterns, tuple
  index fields, type aliases, nested `fn`.
- Attribute args are `[label:] (literal | path)`, never `expr`.

## Closed by owner decision 2026-09-19, round 5

Five decisions of this round touch this chapter; each moves an item out
of "Open questions for the owner" above.

- **D1, receiver shorthand (new production).** `param` gains the
  alternative `convention "self"`, meaning `convention self: Self`. The
  production settled on is exactly:
  `param = convention ident ":" type | convention "self" ;`
  with Disambiguation 21 deciding on one token of lookahead and carrying
  both restrictions (`self` only, `trait_item`/`impl_item` only) and the
  fixed diagnostic. Nothing else changes: `fparam` (an `fn` type) is
  still `convention type`, a `cparam` still takes an optional type, and
  the explicit form stays legal and stays tested.
- **D2, `spmd` and `kernel` are reserved (Q3 closed).** Both become
  reserved words now, used by no production (the regions arrive in
  M6/M9). They are in the reserved list and the reserved-unused table
  above. Nothing was migrated: no spec example and no corpus file used
  either word as an identifier (grep over `docs/spec` and
  `tests/conformance`; ch05's `fn bad_kernel` and ch06's English
  "kernel" are unaffected, since a reserved word matches a whole
  identifier).
- **D4, mandatory `;` and no ASI (Q1, first half).** Confirmed as
  drafted: every `let`/`assign`/`expr`/`return`/`raise`/`use`/`module`/
  header statement ends in `;`, newlines are never terminators, and
  there is no automatic semicolon insertion anywhere (Lexical 1).
- **D4, the flat bitwise tier (Q1, second half).** Confirmed exactly as
  drafted: level 7b, operands at cast level, `& | ^` each chain with
  themselves only, `<<`/`>>` single-use, no mixing with each other, with
  arithmetic/range, or with comparisons — everything else parenthesised,
  in the EBNF (`bit_expr`) and not as a checker rule.
- **D4, the reserved set (Q2).** Confirmed as drafted, plus D2's two
  words; `set` stays contextual (too common as a method or binding
  name), and `reduce`/`unsafe`/`self` stay ordinary identifiers.
- **D5, `fors fmt` (tooling convention).** There is ONE canonical style,
  not a configurable one: 4-space indent, a 100-column target. Recorded
  here rather than in ch06 because ch06 owns measurement (kernel tiers,
  baselines, metric definitions) and nothing else, while this chapter
  already owns whitespace, trivia and the token stream a formatter
  rewrites; the formatter's own implementation is tooling, not spec.

## Closed by owner decision 2026-09-20, round 6

- **O2, `defer` and `errdefer` are reserved words with a production.**
  `stmt` gains `defer_stmt` and `errdefer_stmt`, each `keyword ( block |
  expr ";" )`; both words join the reserved list and the statement
  synchronisation set; Disambiguation 9 gains the two one-token
  decisions. No identifier in the spec, `std/` or `tests/conformance`
  was spelled either way, so nothing that parses today stops parsing.
  Rejected here: a CONTEXTUAL `defer` — `defer {` would be a
  `struct_lit` by Disambiguation 1 and telling the two apart needs the
  token after the `{` (`ident ":"` versus anything else), three tokens,
  which would break the chapter's bound of 2; and a single word with an
  error-only modifier (`defer(error) { }`), which spends call syntax on a
  statement keyword. `fors fmt` writes `defer expr;` on one line and puts
  a `defer { }` body on its own lines like any other block.
  What the two words MEAN — when a body runs, in which order, what it may
  contain, what it may consume — is ch01 Rules 23-23f, and the
  error-exit definition they key on is ch02 Rule 16.

## Open questions for the owner

1. ~~PLAN §4.3(3): confirm mandatory `;`, and the bitwise tier as drafted
   (same-operator chains allowed, everything else parenthesised).~~
   Closed by owner decision 2026-09-19, round 5 (D4): both confirmed as
   drafted — see "Closed by owner decision 2026-09-19, round 5".
2. ~~Confirm the reservation of `iso imm secret raises in as extern inout
   sink consume discard break continue dyn true false`, and `set`
   contextual.~~ Closed by owner decision 2026-09-19, round 5 (D4): the
   set as drafted plus `spmd`/`kernel`, `set` contextual.
3. ~~`spmd`/`kernel` (ch01/ch03 name them as regions): keyword, attribute
   (`@device` style), or future chapter? Not reserved now; reserving later
   breaks code that uses `kernel` as a name.~~ Closed by owner decision
   2026-09-19, round 5 (D2): both are RESERVED from v0.1, used by no
   production yet.
4. Char literals, labelled `break`, match guards: deliberately absent.
5. `contracts:` placement (ch02 Q3) and `recover` (ch01 Q2, the
   ownership-qualifier question — not trap recovery, which ch02 closed
   in round 5) are encoded as drafted there; a change moves one line of
   `file` / the reserved list.

## Conformance tests

- `must_parse_ch01_06_examples` — every fenced `fors` block in ch01-05 (ch06 has none)
  parses with no error, each block as one `file`.
- `lex_numbers` — `1..<2` is 3 tokens; `1.` is `1` `.`; `1.e3` is `1` `.`
  `e3`; `1e3`, `1.5e-3`, `300u32`, `0xFFu8`, `1_000` are one token each;
  `.5`, `1__0`, `1.5q` rejected.
- `lex_munch` — `&out` is 2 tokens; `||` is 2 tokens; `a<=-b` is `a` `<=`
  `-` `b`; `x=>y` has `=>`; `f()?.x` is `?` then `.`; `..` alone rejected.
- `lex_nested_comment` — `/* a /* b */ " */ c` ends at the second `*/`;
  unterminated comment is one error.
- `lex_multiline_string` — two adjacent `\\` lines form one literal joined
  by `\n`; `"a\\b"` is a 3-character string.
- `struct_lit_disabled_in_heads` — `if P { x: 0 } { }` rejected;
  `if (P { x: 0 }).ok { }` accepted; `fn f(let i: usize) pre i < s.len { }`
  accepted. (Rule 1)
- `pipe_three_roles` — `f(|x| x + 1)`, `a | b | c`,
  `g() else |e| { raise e; }`, `reduce(|, xs)` accepted; `g()? else |e| {}`
  rejected. (Rules 2, 3)
- `amp_markers` — `f(&x)`, `f(&out x)`, `f(&out)`, `f(&out.len)`, `a & b`,
  `reduce(&, xs)` accepted; `let y = &x;` rejected. (Rule 4)
- `bracket_roles` — `xs[i]`, `Vec[T]`, `[1, 2, 3]`, `[0; n]`, `@f(a: 1)`,
  `fn g[T]()`, `impl[T] A[T] for B { }` accepted. (Rule 5)
- `contextual_kw_as_identifier` — `let arena = 1; let brand = 2; let out =
  3; let set = 4; let scoped = 5; let needs = 6; let pre = 7; let grain =
  8;` accepted; `let secret = 1;`, `let in = 1;` rejected. (Rule 10)
- `generic_arg_forms` — `vector[f64, 8]`, `Array[T, N + 1]`,
  `x.wrap_as[u8]()`, `f[iso Buf]()` accepted; `Array[T, (N + 1)]`
  rejected. (Rule 11)
- `bitwise_needs_parens` — `a + b & c`, `a & b | c`, `a & b == c`,
  `a << b << c` rejected; `(a + b) & c`, `a | b | c`, `(a & m) != 0`
  accepted. (Rule 12)
- `comparison_no_chaining` — `a < b < c` rejected.
- `not_is_low` — `not a == b` parses as `not (a == b)`; `a == not b`
  rejected.
- `unary_minus_shapes` — `-1`, `x - 1`, `x + -1`, `-1 as i8` accepted with
  the shapes of Rule 8.
- `tuple_paren_unit` — `()`, `(a)`, `(a,)`, `(a, b)` distinguished.
- `statement_start` — `x = 1;`, `a.b[i].c = 1;`, `f();`, `P { x: 1 };`,
  `[1, 2].len;`, tail `x` accepted; `f() = 1;` rejected. (Rule 9)
- `trailing_comma_everywhere` — accepted in every comma list.
- `extern_fn_no_body` — `extern "c" fn dgemm(let n: i32);` accepted.
- `recover_missing_semicolon` — `let a = 1 let b = 2;` yields exactly one
  diagnostic.
- `recover_missing_brace` — a `fn` body missing its `}` followed by
  `struct S { }` and `fn g() { }` yields exactly one diagnostic and both
  later declarations in the CST.
- `asm_expr_parses` — `asm(x86_64) { in(dx) = port, in(al) = value, "out
  dx, al" }` parses as one `asm_expr` with two `in` items and one
  `string_lit` item, `out` result unit (no `out` item).
- `asm_item_disambiguation` — inside an `asm_expr`, `in(...)  = ...`,
  `out(...)`, `clobber(...)`, and a bare `string_lit` each parse as the
  matching `asm_item`; `out`/`clobber` outside an `asm_expr` parse as
  ordinary identifiers.
- `asm_reserved_word` — `let asm = 1;` is rejected; `asm` is unavailable as
  a binding, field or path name.
- `inputs_clause_order` — `module m; needs { }; inputs { "a.json" }; use
  x;` parses; an `inputs` clause before `needs` or after `use` is rejected.
- `inputs_clause_items` — `inputs { };` parses (empty, like `needs { };`);
  `inputs { 1 };` and `inputs { a.b };` are rejected (items are
  `string_lit` only).
- `asm_no_string_parse_error` — an `asm_expr` with no `string_lit` item is
  a parse error.
- `needs_item_asm` — `needs { asm, syscall };` parses; `needs { asm.x };`
  and `use asm;` are rejected.
- `pattern_let_binding` — `match p { let n => f(n) }`,
  `match p { Some(let n) => f(n) }`,
  `match p { P { let x, y: Q(let z) } => g(x, z) }` accepted. (Rule 17)
- `pattern_fpat_let` — `match p { P { let x } => x }` accepted;
  `match p { P { x } => x }` rejected with "write \"let x\" to bind the
  field or \"x: pattern\"" at `x`.
- `pattern_bare_shorthand_removed` — a bare `ident` `fpat` (no `let`, no
  `:`) is a parse error in every position (top level and nested payload).
- `pattern_var_rejected` — `match p { var n => f(n) }` is a parse error;
  `var` is not an `fpat`/`pattern` alternative.
- `use_alias_forms` — `use a.b as c;`, `use a.b as c, d.e;`,
  `pub use a.b as c;` accepted; `use a.b as;` (missing ident) and
  `use a.b as as c;` (`as` twice) are rejected; `use a.b as _;` is
  rejected (`_` is not an `ident`). (Rule 18)
- `pattern_let_underscore_rejected` — `match p { let _ => 0 }` is a parse
  error (write `_`). (Rule 17)
- `assoc_type_items` — `trait It { type Item; fn next(inout self: Self)
  -> Option[Self.Item]; }`, `trait K { type Key: Eq + Ord; }`,
  `impl[I: It] It for Skip[I] { type Item = I.Item; fn next(inout self:
  Skip[I]) -> Option[I.Item] { return none; } }` accepted; `trait T { type
  A = i32; }`, `impl T for S { type A; }`, `impl T for S { pub type A =
  i32; }`, `trait T { @x type A; }`, `trait T { type A[U]; }` rejected.
  (Rule 20)
- `generics_constraint_entry` — `fn f[I: It, I.Item: Add + Copyable]()`,
  `fn g[Self.Item: Eq]()`, `struct S[I: It, I.Item: Eq] { }`, trailing
  comma after a constraint accepted; `fn f[I.Item]()` (no `:`),
  `fn f[I.Item.X: Eq]()`, `fn f[I: It, I.Item = i64]()` (fixed message),
  `fn f[I.Item: brand + Eq]()` parses with `brand` as a path. (Rule 19)
- `type_reserved_word` — `let type = 1;`, `struct S { type: i32 }`,
  `x.type`, `f(type: 1)` rejected; `type A = i32;` at file level rejected
  with the fixed "type aliases do not exist" message and exactly one
  diagnostic, the following declaration intact.
- `recover_assoc_type_item` — `impl T for S { type A = ; fn f() { } }`
  yields exactly one diagnostic and `f` in the CST.
- `receiver_shorthand` (round 5, D1; Rule 21) — `trait It { fn next(inout
  self) -> i64; }`, an `impl` method `fn get(let self) -> i64 { }`, the
  three conventions `let`/`inout`/`sink self` in one trait, `fn at(let
  self, let i: usize) -> i64;` (shorthand followed by ordinary
  parameters), and a trait declaring `fn a(inout self)` beside `fn
  b(inout self: Self)` all parse; `fn f(let self) { }` at file level and
  `trait T { fn f(let x); }` are parse errors with the fixed message.
- `reserved_spmd_kernel` (round 5, D2) — `let spmd = 1;`, `let kernel =
  1;` (identifier), `fn f(let x: kernel) { }`, `struct S { f: spmd }`
  (type position) and `struct S { kernel: i32 }`, `x.spmd` (member name)
  are all parse errors: a member name is not a *name* (ch08 Rule 23) but
  it is still an `ident` token, and a reserved word is not one — exactly
  as for `type`.
- `pattern_let_typed_rejected` — `match p { let x: i32 => x }` is a parse
  error at `:`; so is `.Some(let n: i32)` inside a payload
  (`pattern_let_typed_in_payload_rejected`). (Rule 17)
- `defer-block-parses` (round 6, O2) — `defer { f(); g(); }` parses as one
  `defer_stmt` whose body is a `block`, with no `;` after the `}`.
- `defer-expr-parses` — `defer v.deinit(&a);` parses as one `defer_stmt`
  whose body is the `expr ";"` form.
- `errdefer-block-parses` — `errdefer { v.deinit(&a); }` parses.
- `errdefer-expr-parses` — `errdefer v.deinit(&a);` parses.
- `defer-assignment-rejected` — `defer x = 1;` is a parse error at `=`,
  one diagnostic; `errdefer x = 1;` likewise
  (`errdefer-assignment-rejected`).
- `defer-as-identifier-rejected` (`let defer = 1;`),
  `defer-as-field-name-rejected` (`struct S { defer: i32 }`) and
  `defer-as-member-access-rejected` (`x.defer`) are parse errors, exactly
  as for `type`; `errdefer-as-identifier-rejected` (`fn errdefer() { }`)
  the same for `errdefer`. (The implementation stage split this name into
  the three slots a reserved word can be tried in, matching the
  `reserved-*-as-*` files rounds 2-5 wrote for the other words.)
- `defer-missing-semicolon-recovers` — `defer f() defer g();` yields
  exactly one diagnostic ("missing `;`") and both statements in the CST.
- `defer-nested-parses` — a `defer { defer h(); }` and a `defer` inside a
  `for` body, an arm `block`, a `with` block and a closure body all parse.
- `defer-struct-literal-body-parses` — `defer P { x: 1 };` parses as the
  `expr` form holding a `struct_lit` (a reserved word is not a `path`
  head, so Disambiguation 1 never applies).
