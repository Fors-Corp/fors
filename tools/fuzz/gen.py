#!/usr/bin/env python3
"""Grammar-driven random program generator for the Fors differential fuzzer.

Hand-encodes the EBNF and disambiguation rules of docs/spec/07-grammar.md
(read in full while writing this file) as a set of recursive, depth-bounded
random-expansion functions. Deterministic: `generate(seed, count)` always
returns the same list of programs, byte for byte, for the same arguments -
this is the whole point of a reproducible fuzzing campaign.

Token-level rules the EBNF leaves to prose are hand-coded here to match
`tools/ref/fors_parse.py` exactly (the same RES/SUF vocabulary is imported
from it, so the generator can never emit a reserved word where an
identifier is required):

  * identifiers vs. reserved words (ch07 "Keywords - reserved") and the
    reserved-unused words (`import recover spmd kernel`);
  * integer/float literal forms, radices, digit-group underscores and
    suffixes (ch07 Lexical rule 4);
  * string escapes (rule 5) and the multiline `\\` string (rule 6);
  * comments, both `//` and nesting `/* */` (rule 2);
  * the mandatory `;` (no ASI, round-5 D4);
  * the flat bitwise tier: same-operator chains for `& | ^`, single-use
    `<< >>`, no mixing with anything else without `( )` (rule 12, bit_expr);
    single-use `..< ..=` (range_expr) and non-chaining comparisons (cmp_expr,
    "Levels 7a and 7b are alternatives, not a ladder");
  * `let n` bindings inside patterns (Disambiguation 17) and the removed
    bare-`ident` `fpat` shorthand (round-3 D1).

Usage:
    python3 gen.py --seed 1 --count 500 --out DIR
        Writes DIR/case_00000.fors .. case_00499.fors and DIR/verdicts.tsv
        (path<TAB>ok|err|crash, in the same format
        `tools/ref/diff_driver.py` prints), the crash rows being an
        exception fors_parse.py itself raised that is not one of its own
        E("...") parse-error objects (e.g. RecursionError on very deep
        nesting) - itself a finding, not a script bug.

    python3 gen.py --seed 1 --count 500
        Prints the programs to stdout, separated by a form-feed + newline,
        for quick manual inspection.
"""
from __future__ import annotations

import argparse
import os
import random
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(_HERE, "..", "ref"))
import fors_parse as ref  # noqa: E402  (RES / SUF / ISUF vocabulary)

RESERVED = ref.RES
ALL_SUFFIXES = sorted(ref.SUF)
INT_SUFFIXES = sorted(ref.ISUF)
FLOAT_SUFFIXES = sorted(ref.SUF - ref.ISUF)

# Contextual keywords (ch07 "Keywords - contextual"): legal identifiers
# everywhere outside their one recognised slot. Used often as plain
# identifiers to stress Disambiguation rule 10.
CONTEXTUAL = [
    "contracts", "needs", "inputs", "soa", "set", "brand", "scoped",
    "arena", "allocator", "pre", "post", "invariant", "grain", "out",
    "clobber",
]
# Words explicitly called out as NOT reserved (ch07 "Not reserved"), plus
# `self`, which is only special in the receiver-shorthand `param` slot.
NOT_RESERVED = [
    "reduce", "unsafe", "self", "some", "none", "identity", "order",
    "u8", "vector", "mask", "rawptr",
]
PLAIN_IDENTS = [
    "a", "b", "c", "d", "n", "m", "i", "j", "k", "x", "y", "z", "v", "w",
    "val", "item", "buf", "len", "result", "tmp", "acc", "node", "xs",
    "ys", "head", "tail", "count", "total", "left", "right", "elem",
    "flag", "state", "data", "value", "key", "index", "size",
]
IDENT_POOL = PLAIN_IDENTS + CONTEXTUAL + NOT_RESERVED
assert RESERVED.isdisjoint(IDENT_POOL), "generator vocabulary leaked a reserved word"

TYPE_IDENTS = [
    "T", "U", "V", "E", "K", "Item", "Self", "Buf", "Node", "Point",
    "Vec", "Option", "Result", "Slice", "Array", "List",
]

CMP_OPS = ["==", "!=", "<", ">", "<=", ">="]
ASSIGN_OPS = ["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="]


class Gen:
    """Holds the RNG and depth budgets; every method returns a source
    fragment (a `str`) with no leading/trailing statement `;` unless the
    grammar rule it implements owns one."""

    def __init__(self, rng: random.Random, max_depth: int):
        self.rng = rng
        self.max_depth = max_depth
        self.member_depth = 0  # >0 inside a trait/impl body: enables `self`

    # ---- generic helpers -------------------------------------------------
    def chance(self, p: float) -> bool:
        return self.rng.random() < p

    def pick(self, seq):
        return self.rng.choice(seq)

    def weighted(self, pairs):
        """pairs: list of (weight, thunk). Picks one thunk by weight and calls it."""
        total = sum(w for w, _ in pairs)
        r = self.rng.uniform(0, total)
        upto = 0.0
        for w, thunk in pairs:
            upto += w
            if r <= upto:
                return thunk()
        return pairs[-1][1]()

    def ident(self) -> str:
        return self.pick(IDENT_POOL)

    def type_ident(self) -> str:
        return self.pick(TYPE_IDENTS)

    # ---- lexical: literals -------------------------------------------------
    def digits(self, alphabet: str, minlen: int = 1, maxlen: int = 4) -> str:
        n = self.rng.randint(minlen, maxlen)
        out = [self.pick(alphabet) for _ in range(n)]
        # Splice in underscores only strictly between two digits (never
        # leading, trailing, or doubled) - ch07 Lexical rule 4's `digs`.
        if n > 2 and self.chance(0.3):
            pos = self.rng.randint(1, n - 1)
            out.insert(pos, "_")
        return "".join(out)

    def gen_number(self) -> str:
        kind = self.weighted([
            (5, lambda: "dec"),
            (1, lambda: "hex"),
            (1, lambda: "oct"),
            (1, lambda: "bin"),
            (3, lambda: "float"),
        ])
        if kind == "hex":
            lit = "0x" + self.digits("0123456789abcdefABCDEF", 1, 6)
            suf = self.pick([""] + INT_SUFFIXES) if self.chance(0.4) else ""
            return lit + suf
        if kind == "oct":
            lit = "0o" + self.digits("01234567", 1, 6)
            suf = self.pick([""] + INT_SUFFIXES) if self.chance(0.4) else ""
            return lit + suf
        if kind == "bin":
            lit = "0b" + self.digits("01", 1, 8)
            suf = self.pick([""] + INT_SUFFIXES) if self.chance(0.4) else ""
            return lit + suf
        if kind == "float":
            whole = self.digits("0123456789", 1, 3)
            frac = self.digits("0123456789", 1, 3)
            lit = f"{whole}.{frac}"
            if self.chance(0.3):
                sign = self.pick(["", "+", "-"])
                lit += self.pick(["e", "E"]) + sign + self.digits("0123456789", 1, 2)
            if self.chance(0.3):
                lit += self.pick(FLOAT_SUFFIXES)
            return lit
        # dec int, or dec-with-exponent float (`dec exp`, no dot)
        lit = self.digits("0123456789", 1, 5)
        if self.chance(0.15):
            sign = self.pick(["", "+", "-"])
            lit += self.pick(["e", "E"]) + sign + self.digits("0123456789", 1, 2)
            if self.chance(0.3):
                lit += self.pick(FLOAT_SUFFIXES)
            return lit
        if self.chance(0.4):
            lit += self.pick([""] + INT_SUFFIXES)
        return lit

    def gen_string(self) -> str:
        pieces = []
        for _ in range(self.rng.randint(0, 5)):
            pieces.append(self.weighted([
                (10, lambda: self.pick(list("abcXYZ 09_-"))),
                (1, lambda: "\\n"), (1, lambda: "\\r"), (1, lambda: "\\t"),
                (1, lambda: "\\0"), (1, lambda: "\\\\"), (1, lambda: '\\"'),
                (1, lambda: "\\x" + self.digits("0123456789abcdef", 2, 2)),
                (1, lambda: "\\u{" + self.digits("0123456789abcdef", 1, 4) + "}"),
            ]))
        return '"' + "".join(pieces) + '"'

    def gen_dot_lit(self) -> str:
        return "." + self.ident()

    def gen_literal(self) -> str:
        return self.weighted([
            (4, self.gen_number),
            (2, self.gen_string),
            (1, self.gen_dot_lit),
            (1, lambda: "true"),
            (1, lambda: "false"),
        ])

    # ---- paths / types ------------------------------------------------
    def gen_path(self, type_like: bool = False) -> str:
        first = self.type_ident() if type_like else self.ident()
        segs = [first]
        for _ in range(self.rng.randint(0, 2)):
            segs.append(self.ident())
        return ".".join(segs)

    def gen_generics_use(self, d: int) -> str:
        """`"[" targ {"," targ} [","] "]"` used as a call-site / type-app
        argument list (Disambiguation 11's expression-position rule)."""
        n = self.rng.randint(1, 2)
        args = [self.gen_targ(d - 1) for _ in range(n)]
        if self.chance(0.15):
            args.append("")
        return "[" + ", ".join(a for a in args if a != "") + ("," if args and args[-1] == "" else "") + "]"

    def gen_targ(self, d: int) -> str:
        # const_arg (an add_expr) iff the first token is number/string/
        # true/false/"-"; otherwise a type.
        if self.chance(0.25):
            return self.gen_add_expr(d, ns=False)
        return self.gen_type(d)

    def gen_type(self, d: int) -> str:
        quals = ""
        while self.chance(0.12):
            quals += self.pick(["iso ", "imm ", "secret "])
        return quals + self.gen_type_core(d)

    def gen_type_core(self, d: int) -> str:
        if d <= 0:
            return self.gen_path(type_like=True)
        return self.weighted([
            (6, lambda: self.gen_type_app(d)),
            (2, lambda: self.gen_tuple_type(d)),
            (1, lambda: self.gen_fn_type(d)),
            (1, lambda: "dyn " + self.gen_type_app(d - 1, no_generics_bias=True)),
        ])

    def gen_type_app(self, d: int, no_generics_bias: bool = False) -> str:
        p = self.gen_path(type_like=True)
        if not no_generics_bias and d > 0 and self.chance(0.35):
            return p + self.gen_generics_use(d - 1)
        return p

    def gen_tuple_type(self, d: int) -> str:
        n = self.rng.randint(0, 3)
        items = [self.gen_type(d - 1) for _ in range(n)]
        return "(" + ", ".join(items) + ("," if n == 1 and self.chance(0.5) else "") + ")"

    def gen_fparam(self, d: int) -> str:
        return self.gen_convention() + " " + self.gen_type(d - 1)

    def gen_fn_type(self, d: int) -> str:
        n = self.rng.randint(0, 2)
        params = ", ".join(self.gen_fparam(d - 1) for _ in range(n))
        s = f"fn({params})"
        if self.chance(0.4):
            s += " -> " + self.gen_ret_type(d - 1)
        if self.chance(0.15):
            s += " raises " + self.gen_type(d - 1)
        return s

    def gen_ret_type(self, d: int) -> str:
        prefix = ""
        if self.chance(0.08):
            prefix += f"scoped({self.ident()}) "
        while self.chance(0.1):
            prefix += self.pick(["iso ", "imm ", "secret "])
        if d <= 0 or self.chance(0.85):
            return prefix + self.gen_type_app(max(d - 1, 0))
        if self.chance(0.5):
            return prefix + self.gen_fn_type(d - 1)
        n = self.rng.randint(0, 2)
        return prefix + "(" + ", ".join(self.gen_ret_type(d - 1) for _ in range(n)) + ")"

    def gen_convention(self) -> str:
        return self.pick(["let", "inout", "sink", "set"])

    # ---- expressions ----------------------------------------------------
    # Precedence ladder (ch07 operator table / EBNF), threaded top-down.
    # `ns` disables struct_lit (expr_ns, Disambiguation 1); it is cleared
    # to False for anything generated inside a fresh `( )`, `[ ]` or `{ }`.

    def gen_expr(self, d: int, ns: bool) -> str:
        return self.gen_or(d, ns)

    def gen_or(self, d: int, ns: bool) -> str:
        e = self.gen_and(d, ns)
        n = self.rng.randint(0, 1) if d > 0 else 0
        for _ in range(n):
            e += " or " + self.gen_and(max(d - 1, 0), ns)
        return e

    def gen_and(self, d: int, ns: bool) -> str:
        e = self.gen_not(d, ns)
        n = self.rng.randint(0, 1) if d > 0 else 0
        for _ in range(n):
            e += " and " + self.gen_not(max(d - 1, 0), ns)
        return e

    def gen_not(self, d: int, ns: bool) -> str:
        if d > 0 and self.chance(0.08):
            return "not " + self.gen_not(d - 1, ns)
        return self.gen_cmp(d, ns)

    def gen_cmp(self, d: int, ns: bool) -> str:
        # cmp_expr = bit_expr | range_expr [cmp_op range_expr] -- the two
        # alternatives are exclusive (rule 12): never emit both.
        if d > 0 and self.chance(0.22):
            return self.gen_bit(d, ns)
        e = self.gen_range(d, ns)
        if d > 0 and self.chance(0.3):
            e += " " + self.pick(CMP_OPS) + " " + self.gen_range(max(d - 1, 0), ns)
        return e

    def gen_bit(self, d: int, ns: bool) -> str:
        op = self.pick(["&", "|", "^", "<<", ">>"])
        operand = lambda: self.gen_cast(max(d - 1, 0), ns)  # noqa: E731
        if op in ("<<", ">>"):
            return f"{operand()} {op} {operand()}"
        n = self.rng.randint(2, 3)
        return f" {op} ".join(operand() for _ in range(n))

    def gen_range(self, d: int, ns: bool) -> str:
        e = self.gen_add_expr(d, ns)
        if d > 0 and self.chance(0.15):
            e += " " + self.pick(["..<", "..="]) + " " + self.gen_add_expr(max(d - 1, 0), ns)
        return e

    def gen_add_expr(self, d: int, ns: bool) -> str:
        e = self.gen_mul(d, ns)
        n = self.rng.randint(0, 1) if d > 0 else 0
        for _ in range(n):
            e += " " + self.pick(["+", "-"]) + " " + self.gen_mul(max(d - 1, 0), ns)
        return e

    def gen_mul(self, d: int, ns: bool) -> str:
        e = self.gen_cast(d, ns)
        n = self.rng.randint(0, 1) if d > 0 else 0
        for _ in range(n):
            e += " " + self.pick(["*", "/", "%"]) + " " + self.gen_cast(max(d - 1, 0), ns)
        return e

    def gen_cast(self, d: int, ns: bool) -> str:
        e = self.gen_unary(d, ns)
        if d > 0 and self.chance(0.1):
            e += " as " + self.gen_type(max(d - 1, 0))
        return e

    def gen_unary(self, d: int, ns: bool) -> str:
        if d > 0 and self.chance(0.12):
            return self._unary_op(d, ns)
        return self.gen_postfix(d, ns)

    def _unary_op(self, d: int, ns: bool) -> str:
        op = self.pick(["-", "move"])
        sep = "" if op == "-" else " "
        return op + sep + self.gen_unary(d - 1, ns)

    def gen_postfix(self, d: int, ns: bool) -> str:
        e = self.gen_primary(d, ns)
        ops = self.rng.randint(0, 2) if d > 0 else 0
        for _ in range(ops):
            e = self.weighted([
                (2, lambda: e + "?"),
                (3, lambda: e + "." + self.ident()),
                (2, lambda: e + self.gen_call(max(d - 1, 0))),
                (2, lambda: e + self.gen_bracket(max(d - 1, 0))),
            ])
        return e

    def gen_call(self, d: int) -> str:
        n = self.rng.randint(0, 2)
        args = [self.gen_arg(max(d - 1, 0)) for _ in range(n)]
        s = "(" + ", ".join(args) + ")"
        if self.chance(0.08):
            s += " else |" + self.ident() + "| " + self.gen_block(max(d - 1, 0))
        return s

    def gen_arg(self, d: int) -> str:
        return self.weighted([
            (5, lambda: self.gen_expr(d, ns=False)),
            (1, lambda: self.ident() + ": " + self.gen_expr(d, ns=False)),
            (1, lambda: "&" + self.gen_place()),
            (1, lambda: "&out " + self.gen_place()),
            (1, lambda: self.pick(["+", "-", "*", "/", "%", "&", "|", "^", "and", "or"])),
        ])

    def gen_place(self) -> str:
        p = self.ident()
        for _ in range(self.rng.randint(0, 2)):
            if self.chance(0.6):
                p += "." + self.ident()
            else:
                p += "[" + self.gen_expr(1, ns=False) + "]"
        return p

    def gen_bracket(self, d: int) -> str:
        n = self.rng.randint(1, 2)
        args = [self.gen_expr(max(d - 1, 0), ns=False) for _ in range(n)]
        return "[" + ", ".join(args) + "]"

    def gen_primary(self, d: int, ns: bool) -> str:
        if d <= 0:
            return self.weighted([(3, self.gen_literal), (2, lambda: self.gen_path())])
        choices = [
            (5, self.gen_literal),
            (5, lambda: self.gen_path()),
            (2, lambda: self.gen_tuple_or_paren(d - 1)),
            (2, lambda: self.gen_array_lit(d - 1)),
            (2, lambda: self.gen_closure(d - 1)),
            (1, lambda: self.gen_if_expr(d - 1, as_stmt=False)),
            (1, lambda: self.gen_match_expr(d - 1, as_stmt=False)),
        ]
        if not ns:
            choices.append((2, lambda: self.gen_struct_lit(d - 1)))
        if self.member_depth == 0:
            choices.append((0, lambda: ""))  # keep list shape stable
        if self.chance(0.02):
            choices.append((1, lambda: self.gen_asm_expr(d - 1)))
        return self.weighted(choices)

    def gen_tuple_or_paren(self, d: int) -> str:
        n = self.rng.randint(0, 3)
        items = [self.gen_expr(d, ns=False) for _ in range(n)]
        if n == 1 and self.chance(0.3):
            return "(" + items[0] + ",)"
        return "(" + ", ".join(items) + ")"

    def gen_array_lit(self, d: int) -> str:
        if self.chance(0.25):
            return "[" + self.gen_expr(d, ns=False) + "; " + self.gen_expr(d, ns=False) + "]"
        n = self.rng.randint(0, 3)
        return "[" + ", ".join(self.gen_expr(d, ns=False) for _ in range(n)) + "]"

    def gen_closure(self, d: int) -> str:
        n = self.rng.randint(0, 2)
        params = []
        for _ in range(n):
            p = ""
            if self.chance(0.3):
                p += self.gen_convention() + " "
            p += self.pick(["_"] + [self.ident()])
            if self.chance(0.2):
                p += ": " + self.gen_type(d)
            params.append(p)
        head = "|" + ", ".join(params) + "|"
        body = self.gen_block(d) if self.chance(0.4) else self.gen_expr(d, ns=False)
        return head + " " + body

    def gen_struct_lit(self, d: int) -> str:
        p = self.gen_path(type_like=True)
        if self.chance(0.2):
            p += self.gen_generics_use(d)
        n = self.rng.randint(0, 2)
        fields = [self.ident() + ": " + self.gen_expr(max(d - 1, 0), ns=False) for _ in range(n)]
        return p + " { " + ", ".join(fields) + " }"

    def gen_if_expr(self, d: int, as_stmt: bool) -> str:
        s = "if " + self.gen_expr(d, ns=True) + " " + self.gen_block(d)
        if self.chance(0.6):
            if self.chance(0.35) and d > 0:
                s += " else " + self.gen_if_expr(d - 1, as_stmt=False)
            else:
                s += " else " + self.gen_block(d)
        return s

    def gen_match_expr(self, d: int, as_stmt: bool) -> str:
        n = self.rng.randint(1, 3)
        arms = []
        for idx in range(n):
            pat = self.gen_pattern(d)
            if self.chance(0.35):
                body = self.gen_block(max(d - 1, 0))
                comma = "," if self.chance(0.3) else ""
            else:
                body = self.gen_expr(max(d - 1, 0), ns=False)
                comma = "," if (idx < n - 1 or self.chance(0.5)) else ""
            arms.append(f"{pat} => {body}{comma}")
        return "match " + self.gen_expr(d, ns=True) + " {\n        " + "\n        ".join(arms) + "\n    }"

    def gen_asm_expr(self, d: int) -> str:
        items = ['"nop"']
        for _ in range(self.rng.randint(0, 2)):
            items.append(self.weighted([
                (1, lambda: f"in({self.ident()}) = {self.gen_expr(1, ns=False)}"),
                (1, lambda: f"out({self.ident()})"),
                (1, lambda: f"clobber({self.ident()})"),
                (1, lambda: self.gen_string()),
            ]))
        self.rng.shuffle(items)
        return "asm(x86_64) { " + ", ".join(items) + " }"

    # ---- patterns --------------------------------------------------------
    def gen_pattern(self, d: int) -> str:
        return self.weighted([
            (2, lambda: "_"),
            (2, lambda: self.gen_number()),
            (1, lambda: "-" + self.gen_number()),
            (1, self.gen_string),
            (1, lambda: "true"),
            (1, lambda: "false"),
            (2, lambda: "let " + self.ident()),
            (2, lambda: self.gen_dot_lit() + (self.gen_payload(max(d - 1, 0)) if self.chance(0.5) else "")),
            (2, lambda: self.gen_path() + (self.gen_payload(max(d - 1, 0)) if self.chance(0.5) else "")),
            (1, lambda: "(" + ", ".join(self.gen_pattern(max(d - 1, 0)) for _ in range(self.rng.randint(0, 2))) + ")"),
        ])

    def gen_payload(self, d: int) -> str:
        if self.chance(0.5):
            n = self.rng.randint(1, 2)
            return "(" + ", ".join(self.gen_pattern(d) for _ in range(n)) + ")"
        n = self.rng.randint(1, 2)
        fields = []
        for _ in range(n):
            if self.chance(0.5):
                fields.append("let " + self.ident())
            else:
                fields.append(self.ident() + ": " + self.gen_pattern(d))
        return "{ " + ", ".join(fields) + " }"

    # ---- statements -------------------------------------------------------
    def gen_block(self, d: int) -> str:
        n = self.rng.randint(0, 3) if d > 0 else 0
        lines = [self.gen_stmt(max(d - 1, 0)) for _ in range(n)]
        if self.chance(0.25):
            lines.append(self.gen_expr(max(d - 1, 0), ns=False))
        body = "\n        ".join(lines)
        return "{\n        " + body + "\n    }" if body else "{ }"

    def gen_binding(self, d: int = 1) -> str:
        if d > 0 and self.chance(0.15):
            n = self.rng.randint(1, 2)
            return "(" + ", ".join(self.gen_binding(0) for _ in range(n)) + ")"
        return self.pick(["_"] + [self.ident()])

    def gen_stmt(self, d: int) -> str:
        choices = [
            (4, lambda: self.gen_let_stmt(d)),
            (3, lambda: self.gen_if_expr(d, as_stmt=True)),
            (2, lambda: self.gen_match_expr(d, as_stmt=True)),
            (1, lambda: "comptime " + self.gen_block(d)),
            (2, lambda: "for " + self.gen_binding() + " in " + self.gen_expr(d, ns=True) + " " + self.gen_block(d)),
            (2, lambda: "while " + self.gen_expr(d, ns=True) + " " + self.gen_block(d)),
            (1, lambda: "break;"),
            (1, lambda: "continue;"),
            (2, lambda: "return" + (" " + self.gen_expr(d, ns=False) if self.chance(0.6) else "") + ";"),
            (1, lambda: "raise " + self.gen_expr(d, ns=False) + ";"),
            (1, lambda: self.gen_with_stmt(d)),
            (1, lambda: "parallel " + self.gen_block(d)),
            (1, lambda: self.gen_parallel_for(d)),
            (1, lambda: "simd for " + self.gen_binding() + " in " + self.gen_expr(d, ns=True) + " " + self.gen_block(d)),
            (1, lambda: "spawn " + self.gen_expr(d, ns=False) + ";"),
            (1, lambda: "consume " + self.gen_place() + ";"),
            (1, lambda: "discard " + self.gen_place() + ";"),
            (2, lambda: self.gen_defer_stmt(d, "defer")),
            (2, lambda: self.gen_defer_stmt(d, "errdefer")),
            (1, lambda: self.gen_attribute() + " " + self.gen_block(d)),
            (1, lambda: self.gen_block(d)),
            (4, lambda: self.gen_assign_or_expr_stmt(d)),
        ]
        return self.weighted(choices)

    def gen_let_stmt(self, d: int) -> str:
        kw = self.pick(["let", "var"])
        s = kw + " " + self.gen_binding(1)
        if self.chance(0.4):
            s += ": " + self.gen_type(d)
        if self.chance(0.85):
            s += " = " + self.gen_expr(d, ns=False)
        return s + ";"

    def gen_with_stmt(self, d: int) -> str:
        kw = self.pick(["arena", "allocator"])
        return f"with {kw} {self.ident()}: {self.gen_type(d)} " + self.gen_block(d)

    def gen_parallel_for(self, d: int) -> str:
        s = "parallel for " + self.gen_binding() + " in " + self.gen_expr(d, ns=True)
        if self.chance(0.3):
            s += " grain " + self.gen_expr(max(d - 1, 0), ns=True)
        return s + " " + self.gen_block(d)

    def gen_defer_stmt(self, d: int, kw: str) -> str:
        if self.chance(0.4):
            return kw + " " + self.gen_block(d)
        return kw + " " + self.gen_expr(d, ns=False) + ";"

    def gen_attribute(self) -> str:
        s = "@" + self.ident()
        if self.chance(0.3):
            n = self.rng.randint(0, 2)
            args = []
            for _ in range(n):
                lbl = (self.ident() + ": ") if self.chance(0.4) else ""
                val = self.gen_literal() if self.chance(0.6) else self.gen_path()
                args.append(lbl + val)
            s += "(" + ", ".join(args) + ")"
        return s

    def gen_assign_or_expr_stmt(self, d: int) -> str:
        if self.chance(0.3):
            lhs = self.gen_place()
            op = self.pick(ASSIGN_OPS)
            return f"{lhs} {op} {self.gen_expr(d, ns=False)};"
        return self.gen_expr(d, ns=False) + ";"

    # ---- declarations -------------------------------------------------
    def gen_generics_decl(self, d: int, names: list) -> str:
        n = self.rng.randint(1, 2)
        entries = []
        for _ in range(n):
            nm = self.type_ident()
            names.append(nm)
            entries.append(self.gen_gparam(d, nm))
        if names and self.chance(0.25):
            entries.append(self.gen_gconstraint(d, names))
        return "[" + ", ".join(entries) + "]"

    def gen_gparam(self, d: int, name: str) -> str:
        s = name
        if self.chance(0.5):
            if self.chance(0.2):
                s += ": brand"
            else:
                bounds = [self.gen_type_app(max(d - 1, 0)) for _ in range(self.rng.randint(1, 2))]
                s += ": " + " + ".join(bounds)
        return s

    def gen_gconstraint(self, d: int, names: list) -> str:
        head = self.pick(names + ["Self"])
        bounds = [self.gen_type_app(max(d - 1, 0)) for _ in range(self.rng.randint(1, 2))]
        return f"{head}.{self.ident()}: " + " + ".join(bounds)

    def gen_params(self, d: int, allow_self: bool) -> str:
        n = self.rng.randint(0, 3)
        params = []
        used_self_slot = False
        for i in range(n):
            if allow_self and i == 0 and not used_self_slot and self.chance(0.5):
                params.append(self.gen_convention() + " self")
                used_self_slot = True
            else:
                params.append(self.gen_convention() + " " + self.ident() + ": " + self.gen_type(d))
        return "(" + ", ".join(params) + ")"

    def gen_contract(self, d: int) -> str:
        kw = self.pick(["pre", "post", "invariant"])
        return " " + kw + " " + self.gen_expr(max(d - 1, 1), ns=True)

    def gen_fn_sig(self, d: int, allow_self: bool) -> str:
        s = "fn " + self.ident()
        names: list = []
        if self.chance(0.25):
            s += self.gen_generics_decl(d, names)
        s += self.gen_params(d, allow_self)
        if self.chance(0.5):
            s += " -> " + self.gen_ret_type(d)
        if self.chance(0.15):
            s += " raises " + self.gen_type(d)
        for _ in range(self.rng.randint(0, 1)):
            s += self.gen_contract(d)
        return s

    def gen_fn_decl(self, d: int, allow_self: bool = False) -> str:
        return self.gen_fn_sig(d, allow_self) + " " + self.gen_block(d)

    def gen_extern_fn_decl(self, d: int) -> str:
        return 'extern "c" ' + self.gen_fn_sig(d, allow_self=False) + ";"

    def gen_struct_decl(self, d: int) -> str:
        s = ("soa " if self.chance(0.1) else "") + "struct " + self.type_ident()
        names: list = []
        if self.chance(0.35):
            s += self.gen_generics_decl(d, names)
        for _ in range(self.rng.randint(0, 1)):
            s += " invariant " + self.gen_expr(d, ns=True)
        n = self.rng.randint(0, 4)
        fields = []
        for _ in range(n):
            f = ("pub " if self.chance(0.3) else "") + self.ident() + ": " + self.gen_type(d)
            fields.append(f)
        s += " {\n        " + ",\n        ".join(fields) + ("," if fields and self.chance(0.3) else "") + "\n    }"
        return s

    def gen_enum_decl(self, d: int) -> str:
        s = "enum " + self.type_ident()
        names: list = []
        if self.chance(0.25):
            s += self.gen_generics_decl(d, names)
        n = self.rng.randint(1, 4)
        variants = []
        for _ in range(n):
            v = self.ident()
            shape = self.weighted([(3, lambda: "unit"), (2, lambda: "tuple"), (1, lambda: "struct")])
            if shape == "tuple":
                items = [self.gen_type(d) for _ in range(self.rng.randint(1, 2))]
                v += "(" + ", ".join(items) + ")"
            elif shape == "struct":
                fs = [self.ident() + ": " + self.gen_type(d) for _ in range(self.rng.randint(1, 2))]
                v += " { " + ", ".join(fs) + " }"
            variants.append(v)
        s += " {\n        " + ",\n        ".join(variants) + "\n    }"
        return s

    def gen_trait_decl(self, d: int) -> str:
        name = self.type_ident()
        s = "trait " + name
        names: list = []
        if self.chance(0.25):
            s += self.gen_generics_decl(d, names)
        self.member_depth += 1
        n = self.rng.randint(1, 3)
        items = []
        for _ in range(n):
            if self.chance(0.15):
                bounds = ""
                if self.chance(0.4):
                    bounds = ": " + " + ".join(self.gen_type_app(max(d - 1, 0)) for _ in range(self.rng.randint(1, 2)))
                items.append(f"type {self.ident()}{bounds};")
            else:
                attrs = "".join(self.gen_attribute() + " " for _ in range(self.rng.randint(0, 1)))
                sig = attrs + self.gen_fn_sig(d, allow_self=True)
                items.append(sig + (" " + self.gen_block(d) if self.chance(0.4) else ";"))
        self.member_depth -= 1
        s += " {\n        " + "\n        ".join(items) + "\n    }"
        return s

    def gen_impl_decl(self, d: int) -> str:
        s = "impl"
        names: list = []
        if self.chance(0.3):
            s += self.gen_generics_decl(d, names)
        s += " " + self.gen_type_app(d)
        if self.chance(0.4):
            s += " for " + self.gen_type_app(d)
        self.member_depth += 1
        n = self.rng.randint(1, 3)
        items = []
        for _ in range(n):
            if self.chance(0.15):
                items.append(f"type {self.ident()} = {self.gen_type(d)};")
            else:
                attrs = "".join(self.gen_attribute() + " " for _ in range(self.rng.randint(0, 1)))
                pub = "pub " if self.chance(0.2) else ""
                items.append(attrs + pub + self.gen_fn_decl(d, allow_self=True))
        self.member_depth -= 1
        s += " {\n        " + "\n        ".join(items) + "\n    }"
        return s

    def gen_const_decl(self, d: int) -> str:
        return f"const {self.ident().upper()}: {self.gen_type(d)} = {self.gen_expr(d, ns=False)};"

    def gen_decl(self, d: int) -> str:
        attrs = "".join(self.gen_attribute() + "\n" for _ in range(self.rng.randint(0, 1)))
        pub = "pub " if self.chance(0.3) else ""
        body = self.weighted([
            (4, lambda: self.gen_fn_decl(d)),
            (1, lambda: self.gen_extern_fn_decl(d)),
            (3, lambda: self.gen_struct_decl(d)),
            (2, lambda: self.gen_enum_decl(d)),
            (2, lambda: self.gen_trait_decl(d)),
            (2, lambda: self.gen_impl_decl(d)),
            (2, lambda: self.gen_const_decl(d)),
        ])
        return attrs + pub + body

    # ---- file -------------------------------------------------------------
    def gen_file(self) -> str:
        d = self.max_depth
        parts = []
        if self.chance(0.25):
            parts.append("module " + self.gen_path() + ";")
        needs_present = False
        if self.chance(0.2):
            items = [self.pick(["asm"] + [self.gen_path() for _ in range(2)]) for _ in range(self.rng.randint(0, 3))]
            parts.append("needs { " + ", ".join(items) + " };")
            needs_present = True
        if needs_present and self.chance(0.3):
            strs = [self.gen_string() for _ in range(self.rng.randint(0, 2))]
            parts.append("inputs { " + ", ".join(strs) + " };")
        for _ in range(self.rng.randint(0, 2)):
            pub = "pub " if self.chance(0.2) else ""
            item = self.gen_path()
            if self.chance(0.3):
                item += " as " + self.ident()
            parts.append(pub + "use " + item + ";")
        n = self.rng.randint(1, 3)
        for _ in range(n):
            parts.append(self.gen_decl(d))
        return "\n\n".join(parts) + "\n"


def generate_one(rng: random.Random, max_depth: int = 3) -> str:
    return Gen(rng, max_depth).gen_file()


def generate(seed: int, count: int, max_depth: int = 3) -> list:
    """Deterministic: same (seed, count, max_depth) => same programs."""
    top = random.Random(f"fors-fuzz-gen:{seed}")
    programs = []
    for i in range(count):
        # Derive one independent stream per program so inserting/removing
        # earlier programs never perturbs later ones for a bigger --count.
        sub_seed = top.getrandbits(64) ^ i
        programs.append(generate_one(random.Random(sub_seed), max_depth))
    return programs


def verdict_of(src: str) -> str:
    """Mirrors `tools/ref/diff_driver.py`'s ok/err, plus `crash` for any
    exception that is not fors_parse's own E (a parse error) - itself a
    finding, never a script bug to hide."""
    try:
        err = ref.check(src)
        return "err" if err else "ok"
    except ref.E:
        return "err"
    except Exception:  # noqa: BLE001 - deliberately broad: this *is* the check
        return "crash"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--max-depth", type=int, default=3, help="expression/decl recursion bound")
    ap.add_argument("--out", type=str, default=None, help="write case_NNNNN.fors + verdicts.tsv here")
    ap.add_argument("--nesting-case", type=int, default=None,
                     help="also emit one case with this many nested parens, to probe the two parsers' nesting limits")
    args = ap.parse_args(argv)

    programs = generate(args.seed, args.count, args.max_depth)
    names = [f"case_{i:05d}.fors" for i in range(len(programs))]
    if args.nesting_case:
        n = args.nesting_case
        programs.append("fn main() {\n    let x = " + "(" * n + "1" + ")" * n + ";\n}\n")
        names.append(f"nesting_{n}.fors")

    if args.out is None:
        for p in programs:
            sys.stdout.write(p)
            sys.stdout.write("\f\n")
        return 0

    os.makedirs(args.out, exist_ok=True)
    with open(os.path.join(args.out, "verdicts.tsv"), "w", encoding="utf-8") as manifest:
        for name, src in zip(names, programs):
            path = os.path.join(args.out, name)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(src)
            manifest.write(f"{name}\t{verdict_of(src)}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
