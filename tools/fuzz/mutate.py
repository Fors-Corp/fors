#!/usr/bin/env python3
"""Mutations that turn a valid (or near-valid) Fors program into a NEAR-valid
one, because differential disagreements between the two parsers live at the
boundary of the grammar, not in the interior of clearly-valid or
clearly-garbage input.

Two mutation families:

  * Token-level (operate on a trivia-preserving tokenization of the source,
    so whitespace/comments are carried along unchanged): delete/duplicate/
    swap one token, drop a `;` or a closing delimiter, mix two different
    bitwise operators into one chain (breaks the flat, same-operator-only
    bitwise tier, ch07 rule 12/`bit_expr`), chain a comparison or a range
    operator (breaks the non-chaining `cmp_expr` / single-use `range_expr`),
    insert a reserved word where an identifier is expected, deepen a
    parenthesised group by a large, random amount (both parsers cap
    expression nesting somewhere - `crates/fors-syntax/src/parser.rs`'s
    `MAX_DEPTH` is 128; find out where the Python reference falls over).

  * Byte-level (operate after re-serialising to UTF-8, so they can produce
    input that is not even well-formed UTF-8): insert a NUL byte, an
    unpaired UTF-16 "surrogate" encoded as the three raw bytes that would
    spell it in CESU-8 (`ED A0 80` and friends - never legal UTF-8), a bare
    CR or a CRLF pair, a UTF-8 byte-order mark, or truncate the file
    mid-token (cutting inside a string/number/identifier rather than only
    ever on a token boundary, which is the uninteresting case).

`mutate_bytes(src, rng)` always returns `bytes` (even when nothing but a
text-level mutation applied, encoded back to UTF-8) and never raises: a
mutation that cannot find anything to act on is simply skipped, so calling
it always produces *something*, which is what a fuzz driver needs.
"""
from __future__ import annotations

import os
import random
import sys
from typing import List, Optional, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(_HERE, "..", "ref"))
import fors_parse as ref  # noqa: E402

RESERVED = sorted(ref.RES)
BIT_OPS = ["&", "|", "^"]
SHIFT_OPS = ["<<", ">>"]
CMP_OPS = ["==", "!=", "<", ">", "<=", ">="]
RANGE_OPS = ["..<", "..="]

Token = Tuple[str, str]  # (kind, exact source text)

# ---------------------------------------------------------------------------
# A trivia-preserving tokenizer: concatenating every token's text reproduces
# the input exactly. It only ever runs on our OWN generator's output, which
# is plain ASCII by construction, so it does not need to be hardened against
# arbitrary bytes - anything it does not recognise becomes a one-character
# "other" token rather than raising, so a mutation pass is never the reason
# a campaign crashes.
PUN = sorted(
    "( ) [ ] { } , ; : . @ ? -> => = == != < > <= >= + - * / % & | ^ << >>"
    " ..< ..= += -= *= /= %= &= |= ^= <<= >>=".split(),
    key=len,
    reverse=True,
)


def _digs(src: str, j: int, n: int, ok: str) -> int:
    """Same shape as `fors_parse.lex`'s inner `digs`: a run of `ok`
    characters with single `_` separators allowed between two of them.
    Never raises - stops (rather than erroring) on a malformed group, since
    the caller only needs *a* token boundary, not a grammar-accurate one."""
    while j < n:
        if src[j] in ok:
            j += 1
        elif src[j] == "_" and j + 1 < n and src[j + 1] in ok:
            j += 2
        else:
            break
    return j


def _scan_number(src: str, i: int, n: int) -> int:
    """Returns the end offset of the number token starting at `src[i]`
    (a digit), covering int/float radices, exponents and a glued suffix -
    ch07 Lexical rule 4, adapted from `fors_parse.lex`. Defensive: any
    irregularity just stops the scan early rather than raising, since a
    mutation pass must never crash on its own tokenizer's output."""
    j = i
    if src[i] == "0" and i + 1 < n and src[i + 1] in "xob":
        digits_for = {"x": "0123456789abcdefABCDEF", "o": "01234567", "b": "01"}
        j = _digs(src, i + 2, n, digits_for[src[i + 1]])
        if j == i + 2:  # no digit followed the radix prefix
            j = i + 1
    else:
        D = "0123456789"
        j = _digs(src, i, n, D)
        if j + 1 < n and src[j] == "." and src[j + 1] in D:
            j = _digs(src, j + 1, n, D)
        if j < n and src[j] in "eE" and j + 1 < n and (
            src[j + 1] in D or (src[j + 1] in "+-" and j + 2 < n and src[j + 2] in D)
        ):
            j += 1
            if src[j] in "+-":
                j += 1
            j = _digs(src, j, n, D)
    k = j
    while k < n and (src[k].isalnum() or src[k] == "_") and ord(src[k]) < 128:
        k += 1
    return k


def tokenize(src: str) -> List[Token]:
    toks: List[Token] = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n":
            j = i
            while j < n and src[j] in " \t\r\n":
                j += 1
            toks.append(("ws", src[i:j]))
            i = j
            continue
        if src.startswith("//", i):
            j = i
            while j < n and src[j] != "\n":
                j += 1
            toks.append(("lc", src[i:j]))
            i = j
            continue
        if src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth += 1
                    j += 2
                elif src.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            toks.append(("bc", src[i:j]))
            i = j
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] == "_") and ord(src[j]) < 128:
                j += 1
            word = src[i:j]
            kind = "_" if word == "_" else ("kw" if word in ref.RES else "id")
            toks.append((kind, word))
            i = j
            continue
        if c.isdigit():
            j = _scan_number(src, i, n)
            toks.append(("num", src[i:j]))
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"' and src[j] != "\n":
                if src[j] == "\\" and j + 1 < n:
                    j += 2
                else:
                    j += 1
            if j < n and src[j] == '"':
                j += 1
            toks.append(("str", src[i:j]))
            i = j
            continue
        if src.startswith("\\\\", i):
            j = i
            while j < n and src[j] != "\n":
                j += 1
            toks.append(("mstr", src[i:j]))
            i = j
            continue
        matched = False
        for p in PUN:
            if src.startswith(p, i):
                toks.append(("punct", p))
                i += len(p)
                matched = True
                break
        if matched:
            continue
        toks.append(("other", c))
        i += 1
    return toks


def render(tokens: List[Token]) -> str:
    return "".join(t for _, t in tokens)


# ---------------------------------------------------------------------------
# Token-level mutations. Each takes (tokens, rng) and returns a NEW token
# list, or None if it found nothing to act on (e.g. no `;` in a headerless
# expression fragment) so the caller can fall back to another mutation.

def _indices(tokens: List[Token], pred) -> List[int]:
    return [i for i, t in enumerate(tokens) if pred(t)]


def mut_delete_token(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    real = _indices(tokens, lambda t: t[0] not in ("ws", "lc", "bc"))
    if not real:
        return None
    i = rng.choice(real)
    return tokens[:i] + tokens[i + 1:]


def mut_duplicate_token(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    real = _indices(tokens, lambda t: t[0] not in ("ws", "lc", "bc"))
    if not real:
        return None
    i = rng.choice(real)
    return tokens[:i + 1] + [tokens[i]] + tokens[i + 1:]


def mut_swap_adjacent(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    real = _indices(tokens, lambda t: t[0] not in ("ws", "lc", "bc"))
    if len(real) < 2:
        return None
    k = rng.randrange(len(real) - 1)
    i, j = real[k], real[k + 1]
    out = list(tokens)
    out[i], out[j] = out[j], out[i]
    return out


def mut_drop_semicolon(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    idx = _indices(tokens, lambda t: t == ("punct", ";"))
    if not idx:
        return None
    i = rng.choice(idx)
    return tokens[:i] + tokens[i + 1:]


def mut_drop_closer(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    idx = _indices(tokens, lambda t: t[0] == "punct" and t[1] in ")]}")
    if not idx:
        return None
    i = rng.choice(idx)
    return tokens[:i] + tokens[i + 1:]


def mut_mix_bitwise(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    """Replace one `&`/`|`/`^` with a *different* one of the three, which
    turns a same-operator chain (or a fresh single use) into a mix the flat
    bitwise tier forbids without parentheses (ch07 rule 12)."""
    idx = _indices(tokens, lambda t: t[0] == "punct" and t[1] in BIT_OPS)
    if not idx:
        return None
    i = rng.choice(idx)
    cur = tokens[i][1]
    choice = rng.choice([op for op in BIT_OPS if op != cur])
    out = list(tokens)
    out[i] = ("punct", choice)
    return out


def mut_chain_comparison(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    """After an existing `cmp_op`, duplicate `cmp_op <ident>` once more, so
    `a < b` becomes `a < b < x`: a chained comparison (ch07 rule 12)."""
    idx = _indices(tokens, lambda t: t[0] == "punct" and t[1] in CMP_OPS)
    if not idx:
        return None
    i = rng.choice(idx)
    op = tokens[i][1]
    # insert right after the next non-trivia token (an approximation of
    # "after the RHS operand" that is exactly right when that operand is a
    # single identifier/number/path segment, which the generator favours).
    j = i + 1
    real_seen = 0
    while j < len(tokens) and real_seen < 1:
        if tokens[j][0] not in ("ws", "lc", "bc"):
            real_seen += 1
        j += 1
    insert = [("ws", " "), ("punct", op), ("ws", " "), ("id", "zz")]
    return tokens[:j] + insert + tokens[j:]


def mut_chain_range(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    idx = _indices(tokens, lambda t: t[0] == "punct" and t[1] in RANGE_OPS)
    if not idx:
        return None
    i = rng.choice(idx)
    op = tokens[i][1]
    j = i + 1
    real_seen = 0
    while j < len(tokens) and real_seen < 1:
        if tokens[j][0] not in ("ws", "lc", "bc"):
            real_seen += 1
        j += 1
    insert = [("ws", " "), ("punct", op), ("ws", " "), ("id", "zz")]
    return tokens[:j] + insert + tokens[j:]


def mut_reserved_as_identifier(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    idx = _indices(tokens, lambda t: t[0] == "id")
    if not idx:
        return None
    i = rng.choice(idx)
    out = list(tokens)
    out[i] = ("kw", rng.choice(RESERVED))
    return out


def mut_deep_nesting(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    """Find a matched `( ... )` span and multiply its opening/closing
    parens by a large random amount, to probe each parser's expression-
    nesting limit (`fors-syntax`'s parser caps at `MAX_DEPTH = 128`)."""
    stack = []
    pairs = []
    for i, t in enumerate(tokens):
        if t == ("punct", "("):
            stack.append(i)
        elif t == ("punct", ")") and stack:
            pairs.append((stack.pop(), i))
    if not pairs:
        return None
    open_i, close_i = rng.choice(pairs)
    extra = rng.randint(20, 400)
    out = list(tokens)
    out = (
        out[: open_i + 1]
        + [("punct", "(")] * extra
        + out[open_i + 1 : close_i]
        + [("punct", ")")] * extra
        + out[close_i:]
    )
    return out


def mut_truncate_mid_token(tokens: List[Token], rng: random.Random) -> Optional[List[Token]]:
    candidates = _indices(tokens, lambda t: t[0] in ("str", "num", "id", "kw", "bc", "mstr") and len(t[1]) > 1)
    if not candidates:
        return None
    i = rng.choice(candidates)
    kind, text = tokens[i]
    cut = rng.randint(1, len(text) - 1)
    return tokens[:i] + [(kind, text[:cut])]


TOKEN_MUTATIONS = [
    (3, mut_delete_token),
    (3, mut_duplicate_token),
    (2, mut_swap_adjacent),
    (3, mut_drop_semicolon),
    (3, mut_drop_closer),
    (3, mut_mix_bitwise),
    (3, mut_chain_comparison),
    (2, mut_chain_range),
    (3, mut_reserved_as_identifier),
    (2, mut_deep_nesting),
    (2, mut_truncate_mid_token),
]

# ---------------------------------------------------------------------------
# Byte-level mutations: applied after rendering to UTF-8, so they can make
# the file not-even-valid-UTF-8 on purpose.

LONE_SURROGATE_ENCODINGS = [
    bytes([0xED, 0xA0, 0x80]),  # would-be U+D800 (high surrogate), CESU-8 style
    bytes([0xED, 0xB0, 0x80]),  # would-be U+DC00 (low surrogate)
    bytes([0xED, 0xBF, 0xBF]),  # would-be U+DFFF
]


def byte_insert_nul(data: bytes, rng: random.Random) -> bytes:
    pos = rng.randint(0, len(data))
    return data[:pos] + b"\x00" + data[pos:]


def byte_insert_lone_surrogate(data: bytes, rng: random.Random) -> bytes:
    pos = rng.randint(0, len(data))
    return data[:pos] + rng.choice(LONE_SURROGATE_ENCODINGS) + data[pos:]


def byte_insert_crlf(data: bytes, rng: random.Random) -> bytes:
    nl = [i for i, b in enumerate(data) if b == 0x0A]
    if nl and rng.random() < 0.7:
        i = rng.choice(nl)
        return data[:i] + b"\r" + data[i:]
    pos = rng.randint(0, len(data))
    return data[:pos] + b"\r\n" + data[pos:]


def byte_insert_bom(data: bytes, rng: random.Random) -> bytes:
    bom = b"\xef\xbb\xbf"
    if rng.random() < 0.6:
        return bom + data
    pos = rng.randint(0, len(data))
    return data[:pos] + bom + data[pos:]


BYTE_MUTATIONS = [
    (1, byte_insert_nul),
    (1, byte_insert_lone_surrogate),
    (1, byte_insert_crlf),
    (1, byte_insert_bom),
]


def _weighted_choice(rng: random.Random, pairs):
    total = sum(w for w, _ in pairs)
    r = rng.uniform(0, total)
    upto = 0.0
    for w, fn in pairs:
        upto += w
        if r <= upto:
            return fn
    return pairs[-1][1]


def mutate_bytes(src: str, rng: random.Random, kind: Optional[str] = None) -> Tuple[bytes, str]:
    """Applies exactly one mutation to `src`. Returns (mutated_bytes, name)
    where `name` is the mutation function's name (used for reporting and for
    `--kind` replay during minimisation). `kind`, if given, forces that
    named mutation instead of a random pick (all names are the function
    `__name__`s in TOKEN_MUTATIONS/BYTE_MUTATIONS below)."""
    all_muts = {fn.__name__: ("token", fn) for _, fn in TOKEN_MUTATIONS}
    all_muts.update({fn.__name__: ("byte", fn) for _, fn in BYTE_MUTATIONS})

    if kind is not None:
        family, fn = all_muts[kind]
        names_tried = [kind]
    else:
        # ~70% token-level, ~30% byte-level, matching the task's emphasis on
        # near-valid *grammar* boundary cases over raw encoding garbage.
        if rng.random() < 0.7:
            fn = _weighted_choice(rng, TOKEN_MUTATIONS)
            family = "token"
        else:
            fn = _weighted_choice(rng, BYTE_MUTATIONS)
            family = "byte"
        names_tried = [fn.__name__]

    if family == "token":
        tokens = tokenize(src)
        result = fn(tokens, rng)
        tries = 0
        while result is None and tries < len(TOKEN_MUTATIONS) and kind is None:
            fn = _weighted_choice(rng, TOKEN_MUTATIONS)
            names_tried.append(fn.__name__)
            result = fn(tokens, rng)
            tries += 1
        if result is None:
            return src.encode("utf-8"), "none"
        return render(result).encode("utf-8", errors="surrogateescape"), names_tried[-1]

    data = src.encode("utf-8", errors="surrogateescape")
    result = fn(data, rng)
    return result, names_tried[-1]


def mutation_names() -> List[str]:
    return [fn.__name__ for _, fn in TOKEN_MUTATIONS] + [fn.__name__ for _, fn in BYTE_MUTATIONS]


def main(argv=None) -> int:
    import argparse

    ap = argparse.ArgumentParser(description="Apply one random mutation to a Fors source file.")
    ap.add_argument("path")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--kind", type=str, default=None, choices=mutation_names())
    args = ap.parse_args(argv)
    with open(args.path, "r", encoding="utf-8", errors="surrogateescape") as fh:
        src = fh.read()
    out, name = mutate_bytes(src, random.Random(args.seed), kind=args.kind)
    sys.stderr.write(f"# mutation: {name}\n")
    sys.stdout.buffer.write(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
