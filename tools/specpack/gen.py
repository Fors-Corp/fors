#!/usr/bin/env python3
"""Generate docs/spec/PACK.md, the spec-in-context pack for AI agents.

docs/spec/PACK.md is GENERATED from the normative spec (docs/spec/*.md), the
conformance corpus (tests/conformance/) and the standard library (std/) so it
cannot drift from them. Never hand-edit docs/spec/PACK.md.

Usage:
    python3 tools/specpack/gen.py --write   # regenerate docs/spec/PACK.md
    python3 tools/specpack/gen.py --check   # exit 1 if PACK.md is stale

Standard library only. Deterministic: sorted traversal, no timestamps, no
absolute paths in the output.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths and constants
# ---------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parents[2]
SPEC_DIR = ROOT / "docs" / "spec"
CORPUS_DIR = ROOT / "tests" / "conformance"
STD_DIR = ROOT / "std"
TOOL_DIR = Path(__file__).resolve().parent
ORIENTATION_PATH = TOOL_DIR / "orientation.md"
PACK_PATH = SPEC_DIR / "PACK.md"
VERSION_PATH = SPEC_DIR / "VERSION"
GRAMMAR_PATH = SPEC_DIR / "07-grammar.md"

SIZE_LIMIT_BYTES = 130_000
ORIENTATION_MAX_LINES = 120

# Chapter number -> spec file, for chapters that carry a numbered "## Rules"
# list (07-grammar has none: its material is reproduced verbatim in section 2).
CHAPTER_FILES = {
    "01": "01-ownership.md",
    "02": "02-failure.md",
    "03": "03-numerics-determinism.md",
    "04": "04-authority.md",
    "05": "05-ir-contract.md",
    "06": "06-measurement.md",
    "08": "08-names.md",
    "09": "09-types.md",
    "10": "10-std.md",
}
# Diagnostic-code letter per chapter, per the owner's scheme.
CHAPTER_LETTER = {
    "01": "O",
    "02": "F",
    "03": "D",
    "04": "A",
    "08": "N",
    "09": "T",
    "10": "S",
}
LETTER_CHAPTER = {v: k for k, v in CHAPTER_LETTER.items()}
# Chapters without an assigned diagnostic-code letter cite as "ch0N Rk".
UNLETTERED_CHAPTERS = ("05", "06")
RULE_INDEX_CHAPTERS = ("01", "02", "03", "04", "05", "06", "08", "09", "10")

# Corpus directory name for each chapter used by COMPLETE EXAMPLES.
EXAMPLE_GROUPS = (
    ("01", "01-ownership"),
    ("02", "02-failure"),
    ("03", "03-numerics"),
    ("04", "04-authority"),
    ("08", "08-names"),
    ("09", "09-types"),
    ("10", "10-std"),
)
EXAMPLES_MIN = 16
EXAMPLES_MAX = 24
EXAMPLES_MAX_PER_GROUP = 5

MISTAKES_TOP_N = 25
MISTAKES_MAX_LINES = 25

ACCEPTED_EXPECT_KINDS = {"parse-ok", "check-ok", "run-ok", "run-error", "trap"}
REJECTED_EXPECT_KINDS = {"parse-error", "check-error"}

DIAG_CODE_RE = re.compile(r"^[A-Za-z]\d{4}[a-z]*$")


# ---------------------------------------------------------------------------
# Small IO helpers (explicit `with open(...)`, no shell, no eval, no chmod)
# ---------------------------------------------------------------------------


def read_text(path: Path) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def read_lines(path: Path) -> list[str]:
    return read_text(path).splitlines()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


# ---------------------------------------------------------------------------
# Section 1: ORIENTATION (hand-written, machine-verified)
# ---------------------------------------------------------------------------

FROM_COMMENT_RE = re.compile(r"^<!--\s*from:\s*(\S+)\s*-->\s*$")


def normalise_line(line: str) -> str:
    """Whitespace-normalise one line for the contiguity check: trailing
    whitespace never carries meaning in either the pack or the corpus."""
    return line.rstrip()


def find_contiguous(haystack: list[str], needle: list[str]) -> bool:
    """True iff `needle` (already normalised) is a contiguous run of lines
    of `haystack` (already normalised)."""
    if not needle:
        return False
    n = len(needle)
    for i in range(0, len(haystack) - n + 1):
        if haystack[i : i + n] == needle:
            return True
    return False


def load_orientation() -> tuple[str, list[str]]:
    """Read orientation.md, verify every ```fors block is a contiguous,
    whitespace-normalised quote of the ACCEPTED corpus file its preceding
    `<!-- from: ... -->` comment names, and return (raw_text, errors)."""
    if not ORIENTATION_PATH.exists():
        return "", [f"missing {rel(ORIENTATION_PATH)}"]
    lines = read_lines(ORIENTATION_PATH)
    errors: list[str] = []
    if len(lines) > ORIENTATION_MAX_LINES:
        errors.append(
            f"{rel(ORIENTATION_PATH)} has {len(lines)} lines, "
            f"over the {ORIENTATION_MAX_LINES}-line limit"
        )

    file_cache: dict[str, list[str] | None] = {}
    expect_cache: dict[str, str | None] = {}

    i = 0
    n = len(lines)
    while i < n:
        m = FROM_COMMENT_RE.match(lines[i])
        if not m:
            i += 1
            continue
        source_rel = m.group(1)
        # The fenced ```fors block must follow (only blank/comment lines
        # may sit between the citation and its block).
        j = i + 1
        while j < n and lines[j].strip() == "":
            j += 1
        if j >= n or lines[j].strip() != "```fors":
            errors.append(
                f"{rel(ORIENTATION_PATH)}:{i + 1}: `from:` comment is not "
                "immediately followed by a ```fors block"
            )
            i += 1
            continue
        k = j + 1
        code_lines: list[str] = []
        while k < n and lines[k].strip() != "```":
            code_lines.append(lines[k])
            k += 1
        if k >= n:
            errors.append(
                f"{rel(ORIENTATION_PATH)}:{j + 1}: unterminated ```fors block"
            )
            break

        source_path = ROOT / source_rel
        if not (
            source_rel.startswith("tests/conformance/")
            and source_path.is_file()
        ):
            errors.append(
                f"{rel(ORIENTATION_PATH)}:{i + 1}: `{source_rel}` is not a "
                "file under tests/conformance/"
            )
        else:
            if source_rel not in file_cache:
                try:
                    file_cache[source_rel] = [
                        normalise_line(l) for l in read_lines(source_path)
                    ]
                except OSError:
                    file_cache[source_rel] = None
                expect_cache[source_rel] = read_expect_kind(source_path)
            haystack = file_cache[source_rel]
            expect = expect_cache.get(source_rel)
            if haystack is None:
                errors.append(
                    f"{rel(ORIENTATION_PATH)}:{i + 1}: could not read "
                    f"`{source_rel}`"
                )
            else:
                if expect in REJECTED_EXPECT_KINDS:
                    errors.append(
                        f"{rel(ORIENTATION_PATH)}:{i + 1}: `{source_rel}` is "
                        f"a REJECTED test (expect: {expect}), not accepted"
                    )
                needle = [normalise_line(l) for l in code_lines]
                if not find_contiguous(haystack, needle):
                    errors.append(
                        f"{rel(ORIENTATION_PATH)}:{i + 1}: the fenced block "
                        f"is not a contiguous quote of `{source_rel}`"
                    )
        i = k + 1

    return read_text(ORIENTATION_PATH).rstrip("\n"), errors


# ---------------------------------------------------------------------------
# Corpus directives
# ---------------------------------------------------------------------------

DIRECTIVE_RE = re.compile(r"^//!\s*([a-zA-Z]+):\s?(.*)$")


def read_directives(path: Path) -> dict[str, str]:
    directives: dict[str, str] = {}
    for line in read_lines(path):
        m = DIRECTIVE_RE.match(line)
        if m:
            directives.setdefault(m.group(1), m.group(2))
        elif line.strip() == "" or line.startswith("//!"):
            continue
        else:
            break
    return directives


def read_expect_kind(path: Path) -> str | None:
    d = read_directives(path)
    expect = d.get("expect")
    if expect is None:
        return None
    return expect.split()[0].rstrip(",")


def diagnostic_code(detail: str) -> str | None:
    first = detail.split()[0] if detail.split() else ""
    return first if DIAG_CODE_RE.match(first) else None


def is_single_file_test(path: Path) -> bool:
    return len(path.relative_to(CORPUS_DIR).parts) == 2


def iter_corpus_files():
    yield from sorted(CORPUS_DIR.rglob("*.fors"))


# ---------------------------------------------------------------------------
# Section 2: GRAMMAR (07-grammar.md, verbatim)
# ---------------------------------------------------------------------------


H2_RE = re.compile(r"^##\s")
H2_OR_H3_RE = re.compile(r"^#{2,3}\s")


def section_lines(lines: list[str], heading: str, stop_at_h3: bool = True) -> list[str]:
    """Lines from `heading` (inclusive) up to the next stopping heading
    (exclusive). By default that is the next level-2 OR level-3 heading, so
    a "### " subsection never swallows its sibling; `stop_at_h3=False` (for
    a "## " section that owns its own "### " subsections, e.g. ch09's
    lettered "## Rules" groups) stops only at the next level-2 heading."""
    stop_re = H2_OR_H3_RE if stop_at_h3 else H2_RE
    start = None
    for idx, line in enumerate(lines):
        if line.rstrip() == heading:
            start = idx
            break
    if start is None:
        return []
    end = len(lines)
    for idx in range(start + 1, len(lines)):
        if stop_re.match(lines[idx]):
            end = idx
            break
    return lines[start:end]


def build_grammar_section() -> tuple[str, list[str]]:
    errors: list[str] = []
    lines = read_lines(GRAMMAR_PATH)

    keywords_reserved = section_lines(lines, "### Keywords — reserved (never identifiers)")
    keywords_contextual = section_lines(lines, "### Keywords — contextual")
    operator_table = section_lines(lines, "## Operator table")
    grammar_section = section_lines(lines, "## Grammar")

    ebnf_blocks: list[list[str]] = []
    i = 0
    n = len(grammar_section)
    while i < n:
        if grammar_section[i].startswith("```"):
            start = i
            j = i + 1
            while j < n and grammar_section[j].strip() != "```":
                j += 1
            if j >= n:
                errors.append("07-grammar.md: unterminated fenced grammar block")
                break
            ebnf_blocks.append(grammar_section[start : j + 1])
            i = j + 1
        else:
            i += 1

    if not (keywords_reserved and keywords_contextual and operator_table and ebnf_blocks):
        errors.append(
            "07-grammar.md: could not find one of the keyword sections, the "
            "operator table, or a fenced grammar block"
        )

    parts = []
    parts.extend(keywords_reserved)
    parts.append("")
    parts.extend(keywords_contextual)
    parts.append("")
    parts.extend(operator_table)
    parts.append("")
    for block in ebnf_blocks:
        parts.extend(block)
        parts.append("")
    return "\n".join(parts).rstrip("\n"), errors


# ---------------------------------------------------------------------------
# Rule extraction, shared by RULE INDEX (section 3) and COMMON MISTAKES (6)
# ---------------------------------------------------------------------------

RULE_START_RE = re.compile(r"^(\d+)([a-z]*)\.\s+(.*)$")
RULE_CODE_PREFIX_RE = re.compile(r"^\*\*[A-Za-z]\d{4}[a-z]?\*\*\s*[—-]\s*")
ABBREVIATIONS = ("e.g.", "i.e.", "etc.", "cf.", "vs.", "Fig.", "No.", "approx.", "resp.")


def first_sentence(text: str, limit: int = 220) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    text = RULE_CODE_PREFIX_RE.sub("", text, count=1)
    n = len(text)
    backtick_open = False
    end = None
    i = 0
    while i < n:
        ch = text[i]
        if ch == "`":
            backtick_open = not backtick_open
            i += 1
            continue
        if ch in ".!?" and not backtick_open:
            if any(text[: i + 1].endswith(a) for a in ABBREVIATIONS):
                i += 1
                continue
            prev_ch = text[i - 1] if i > 0 else ""
            next_ch = text[i + 1] if i + 1 < n else ""
            if prev_ch.isdigit() and next_ch.isdigit():
                i += 1
                continue
            if next_ch == "." or prev_ch == ".":
                i += 1
                continue
            if next_ch == "" or next_ch == " ":
                end = i + 1
                break
        i += 1
    sentence = text if end is None else text[:end]
    if len(sentence) > limit:
        sentence = sentence[: limit - 3].rstrip() + "..."
    return sentence


_RULES_CACHE: dict[str, list[tuple[str, str, str]]] = {}


def extract_rules(chapter_num: str) -> list[tuple[str, str, str]]:
    """Return [(number, letter_suffix, raw_text), ...] for every numbered
    item of chapter_num's "## Rules" section, in document order."""
    if chapter_num in _RULES_CACHE:
        return _RULES_CACHE[chapter_num]
    path = SPEC_DIR / CHAPTER_FILES[chapter_num]
    lines = read_lines(path)
    section = section_lines(lines, "## Rules", stop_at_h3=False)[1:]  # drop the heading
    rules: list[tuple[str, str, str]] = []
    n = len(section)
    i = 0
    while i < n:
        m = RULE_START_RE.match(section[i])
        if not m:
            i += 1
            continue
        num, suffix, rest = m.group(1), m.group(2), m.group(3)
        collected = [rest]
        j = i + 1
        while j < n and len(collected) < 12:
            nxt = section[j]
            if nxt.strip() == "":
                break
            if RULE_START_RE.match(nxt):
                break
            if nxt.startswith("### ") or nxt.lstrip().startswith("```"):
                break
            if not nxt.startswith("  "):
                break
            collected.append(nxt.strip())
            j += 1
        rules.append((num, suffix, " ".join(collected)))
        i = j if j > i else i + 1
    _RULES_CACHE[chapter_num] = rules
    return rules


def rule_code(chapter_num: str, num: str, suffix: str) -> str:
    if chapter_num in UNLETTERED_CHAPTERS:
        return f"ch{chapter_num} R{num}{suffix}"
    letter = CHAPTER_LETTER[chapter_num]
    return f"{letter}{int(num):04d}{suffix}"


def rule_sentence_for_diagnostic_code(code: str) -> str | None:
    """Reverse a diagnostic code like 'S0011c' into its chapter + rule
    number and return that rule's first sentence, falling back to the
    un-suffixed rule if the exact lettered clause is not its own list item."""
    m = re.match(r"^([A-Za-z])(\d{4})([a-z]*)$", code)
    if not m:
        return None
    letter, digits, suffix = m.group(1), m.group(2), m.group(3)
    chapter_num = LETTER_CHAPTER.get(letter)
    if chapter_num is None:
        return None
    num = str(int(digits))
    rules = extract_rules(chapter_num)
    by_key = {(n, s): text for n, s, text in rules}
    text = by_key.get((num, suffix))
    if text is None:
        text = by_key.get((num, ""))
    if text is None:
        return None
    return first_sentence(text)


def build_rule_index() -> tuple[str, dict[str, int]]:
    lines: list[str] = []
    counts: dict[str, int] = {}
    for chapter_num in RULE_INDEX_CHAPTERS:
        rules = extract_rules(chapter_num)
        counts[chapter_num] = len(rules)
        for num, suffix, text in rules:
            code = rule_code(chapter_num, num, suffix)
            lines.append(f"{code}  {first_sentence(text)}")
    return "\n".join(lines), counts


# ---------------------------------------------------------------------------
# Section 4: STD SURFACE
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^[ \t]*((?:pub\s+)?(?:fn|struct|enum|trait|impl|const|static|type))\b",
    re.MULTILINE,
)
CONTAINER_KEYWORDS = ("impl", "trait")


def _skip_string_or_comment(text: str, i: int) -> int | None:
    """If text[i:] starts a string literal or a line comment, return the
    index just past it; else None."""
    if text[i] == '"':
        j = i + 1
        n = len(text)
        while j < n:
            if text[j] == "\\":
                j += 2
                continue
            if text[j] == '"':
                return j + 1
            j += 1
        return n
    if text[i : i + 2] == "//":
        j = text.find("\n", i)
        return len(text) if j == -1 else j
    return None


def find_header_end(text: str, start: int) -> tuple[int, str | None]:
    """From `start`, scan to the terminating '{' or ';' at paren/bracket
    depth 0, outside strings and comments. Returns (index, '{' | ';' | None)."""
    i = start
    n = len(text)
    paren = bracket = 0
    while i < n:
        skip_to = _skip_string_or_comment(text, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = text[i]
        if ch == "(":
            paren += 1
        elif ch == ")":
            paren -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket -= 1
        elif ch == "{" and paren <= 0 and bracket <= 0:
            return i, "{"
        elif ch == ";" and paren <= 0 and bracket <= 0:
            return i, ";"
        i += 1
    return n, None


def find_matching_brace(text: str, open_pos: int) -> int:
    depth = 0
    i = open_pos
    n = len(text)
    while i < n:
        skip_to = _skip_string_or_comment(text, i)
        if skip_to is not None:
            i = skip_to
            continue
        ch = text[i]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return n - 1


def one_line(text: str) -> str:
    s = re.sub(r"\s+", " ", text).strip()
    # Cosmetic only: a signature wrapped onto several source lines collapses
    # to one line above; tidy the seams left at bracket/paren/comma edges.
    s = re.sub(r"([(\[])\s+", r"\1", s)
    s = re.sub(r"\s+([)\]])", r"\1", s)
    s = re.sub(r",\s*([)\]])", r"\1", s)
    s = re.sub(r"\s+,", ",", s)
    return s


def scan_declarations(text: str, start: int, end: int, indent: str) -> list[str]:
    out: list[str] = []
    region = text[:end]
    pos = start
    while True:
        m = DECL_RE.search(region, pos)
        if not m or m.start(1) >= end:
            break
        decl_start = m.start(1)
        keyword = m.group(1).split()[-1]
        header_end, term = find_header_end(text, decl_start)
        if term is None:
            break
        header = one_line(text[decl_start:header_end])
        if term == ";":
            out.append(f"{indent}{header};")
            pos = header_end + 1
            continue
        close = find_matching_brace(text, header_end)
        if keyword in CONTAINER_KEYWORDS:
            inner = scan_declarations(text, header_end + 1, close, indent + "    ")
            if inner:
                out.append(f"{indent}{header} {{")
                out.extend(inner)
                out.append(f"{indent}}}")
            else:
                out.append(f"{indent}{header} {{}}")
        else:
            out.append(f"{indent}{header} {{ ... }}")
        pos = close + 1
    return out


def module_title(rel_path: str) -> str:
    stem = rel_path[len("std/") :]
    if stem.endswith(".fors"):
        stem = stem[: -len(".fors")]
    return "std." + stem.replace("/", ".")


def build_std_surface() -> str:
    parts: list[str] = []
    for path in sorted(STD_DIR.rglob("*.fors")):
        text = read_text(path)
        decls = scan_declarations(text, 0, len(text), "")
        parts.append(f"### {module_title(rel(path))}  (`{rel(path)}`)")
        if decls:
            parts.append("```fors")
            parts.extend(decls)
            parts.append("```")
        else:
            parts.append("(no top-level declarations)")
        parts.append("")
    return "\n".join(parts).rstrip("\n")


# ---------------------------------------------------------------------------
# Keyword scanning, shared by COMPLETE EXAMPLES
# ---------------------------------------------------------------------------

WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def top_level_keywords(path: Path) -> set[str]:
    kws: set[str] = set()
    for line in read_lines(path):
        if line.startswith("//") or line[:1] in (" ", "\t", ""):
            continue
        words = line.strip().split()
        if not words:
            continue
        w = words[0]
        if w == "pub" and len(words) > 1:
            w = words[1]
        m = WORD_RE.match(w)
        if m:
            kws.add(m.group(0))
    return kws


# ---------------------------------------------------------------------------
# Section 5: COMPLETE EXAMPLES
# ---------------------------------------------------------------------------


def candidate_examples(dirname: str) -> list[tuple[int, str, Path]]:
    d = CORPUS_DIR / dirname
    out = []
    for f in sorted(d.glob("*.fors")):
        if not is_single_file_test(f):
            continue
        expect = read_expect_kind(f)
        if expect not in ACCEPTED_EXPECT_KINDS:
            continue
        out.append((f.stat().st_size, rel(f), f))
    out.sort(key=lambda t: (t[0], t[1]))
    return out


def select_examples() -> list[Path]:
    global_covered: set[str] = set()
    selected: list[tuple[int, str, Path]] = []
    for _chnum, dirname in EXAMPLE_GROUPS:
        group_selected: list[tuple[int, str, Path]] = []
        group_covered: set[str] = set()
        for size, relpath, f in candidate_examples(dirname):
            kws = top_level_keywords(f)
            new_kws = kws - global_covered
            if not group_selected or new_kws:
                group_selected.append((size, relpath, f))
                group_covered |= kws
                global_covered |= kws
            if len(group_selected) >= EXAMPLES_MAX_PER_GROUP:
                break
        selected.extend(group_selected)

    if len(selected) > EXAMPLES_MAX:
        # Trim largest-first, but never drop a group below one example.
        by_group: dict[str, list[tuple[int, str, Path]]] = {}
        for item in selected:
            chnum = item[2].relative_to(CORPUS_DIR).parts[0]
            by_group.setdefault(chnum, []).append(item)
        while len(selected) > EXAMPLES_MAX:
            biggest = max(
                (it for it in selected if len(by_group[it[2].relative_to(CORPUS_DIR).parts[0]]) > 1),
                key=lambda t: (t[0], t[1]),
                default=None,
            )
            if biggest is None:
                break
            selected.remove(biggest)
            by_group[biggest[2].relative_to(CORPUS_DIR).parts[0]].remove(biggest)

    if len(selected) < EXAMPLES_MIN:
        chosen_paths = {p for _s, _r, p in selected}
        pool = []
        for _chnum, dirname in EXAMPLE_GROUPS:
            for size, relpath, f in candidate_examples(dirname):
                if f not in chosen_paths:
                    pool.append((size, relpath, f))
        pool.sort(key=lambda t: (t[0], t[1]))
        for item in pool:
            if len(selected) >= EXAMPLES_MIN:
                break
            selected.append(item)
            chosen_paths.add(item[2])

    selected.sort(key=lambda t: (t[2].relative_to(CORPUS_DIR).parts[0], t[1]))
    return [f for _s, _r, f in selected]


def build_examples_section(paths: list[Path]) -> str:
    parts = []
    for f in paths:
        parts.append(f"#### `{rel(f)}`")
        parts.append("```fors")
        parts.extend(read_lines(f))
        parts.append("```")
        parts.append("")
    return "\n".join(parts).rstrip("\n")


# ---------------------------------------------------------------------------
# Section 6: COMMON MISTAKES
# ---------------------------------------------------------------------------


def collect_rejected_by_code() -> dict[str, list[tuple[int, str, Path]]]:
    by_code: dict[str, list[tuple[int, str, Path]]] = {}
    for f in iter_corpus_files():
        directives = read_directives(f)
        expect = directives.get("expect")
        if expect is None or expect.split()[0] not in REJECTED_EXPECT_KINDS:
            continue
        detail = directives.get("detail", "")
        code = diagnostic_code(detail)
        if code is None:
            continue
        by_code.setdefault(code, []).append((f.stat().st_size, rel(f), f))
    return by_code


def select_mistake_codes(by_code: dict[str, list]) -> list[str]:
    codes = list(by_code.keys())
    codes.sort(key=lambda c: (-len(by_code[c]), c))
    return codes[:MISTAKES_TOP_N]


def build_mistakes_section() -> tuple[str, list[str]]:
    errors: list[str] = []
    by_code = collect_rejected_by_code()
    codes = select_mistake_codes(by_code)
    parts = []
    for code in codes:
        occurrences = sorted(by_code[code], key=lambda t: (t[0], t[1]))
        single_file = [o for o in occurrences if is_single_file_test(o[2])]
        pool = single_file or occurrences
        _size, relpath, path = pool[0]
        sentence = rule_sentence_for_diagnostic_code(code)
        if sentence is None:
            sentence = "(rule text unavailable)"
            errors.append(f"COMMON MISTAKES: no rule text found for {code}")
        parts.append(f"**{code}** ({len(occurrences)} tests) — {sentence}")
        parts.append(f"<!-- {relpath} -->")
        parts.append("```fors")
        lines = read_lines(path)
        truncated = len(lines) > MISTAKES_MAX_LINES
        parts.extend(lines[:MISTAKES_MAX_LINES])
        if truncated:
            parts.append("... (truncated)")
        parts.append("```")
        parts.append("")
    return "\n".join(parts).rstrip("\n"), errors


# ---------------------------------------------------------------------------
# Section 7: TOOLS (fixed)
# ---------------------------------------------------------------------------

TOOLS_SECTION = """\
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
compiler wins and this pack is stale."""


# ---------------------------------------------------------------------------
# Hashing over the generator's inputs
# ---------------------------------------------------------------------------


def input_file_list() -> list[Path]:
    files = [ORIENTATION_PATH, VERSION_PATH]
    for chapter_num in sorted(CHAPTER_FILES):
        files.append(SPEC_DIR / CHAPTER_FILES[chapter_num])
    files.append(GRAMMAR_PATH)
    files.extend(sorted(STD_DIR.rglob("*.fors")))
    files.extend(iter_corpus_files())
    # De-duplicate while keeping the list sorted by relative path.
    uniq = sorted({rel(p): p for p in files}.items())
    return [p for _r, p in uniq]


def compute_inputs_hash() -> str:
    h = hashlib.sha256()
    for path in input_file_list():
        h.update(rel(path).encode("utf-8"))
        h.update(b"\0")
        with open(path, "rb") as f:
            h.update(f.read())
        h.update(b"\0")
    return h.hexdigest()


# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------


def read_version() -> str:
    return read_text(VERSION_PATH).strip()


def build_pack(examples_max: int, mistakes_top_n: int) -> tuple[str, list[str], dict]:
    errors: list[str] = []

    global EXAMPLES_MAX, MISTAKES_TOP_N
    saved_examples_max, saved_mistakes_top_n = EXAMPLES_MAX, MISTAKES_TOP_N
    EXAMPLES_MAX, MISTAKES_TOP_N = examples_max, mistakes_top_n
    try:
        orientation, o_errors = load_orientation()
        errors.extend(o_errors)

        grammar, g_errors = build_grammar_section()
        errors.extend(g_errors)

        rule_index, rule_counts = build_rule_index()
        std_surface = build_std_surface()
        example_paths = select_examples()
        examples = build_examples_section(example_paths)
        mistakes, m_errors = build_mistakes_section()
        errors.extend(m_errors)
    finally:
        EXAMPLES_MAX, MISTAKES_TOP_N = saved_examples_max, saved_mistakes_top_n

    version = read_version()
    inputs_hash = compute_inputs_hash()

    header = f"""\
# Fors spec-in-context pack

GENERATED FILE — do not hand-edit; run `tools/specpack/gen.py --write` to
regenerate. Source: `docs/spec/*.md` (normative), `tests/conformance/`
(corpus) and `std/**/*.fors` (standard library).

Language version: {version} (`docs/spec/VERSION`)
Inputs SHA-256: {inputs_hash}

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
"""

    doc = "\n".join(
        [
            header,
            "## 1. Orientation",
            "",
            orientation,
            "",
            "## 2. Grammar",
            "",
            grammar,
            "",
            "## 3. Rule index",
            "",
            "One line per numbered rule of chapters 01-06 and 08-10 (chapter",
            "07's grammar is reproduced verbatim in section 2 instead): the",
            "diagnostic-code-shaped citation, two spaces, its first sentence",
            "truncated at 220 characters.",
            "",
            "```",
            rule_index,
            "```",
            "",
            "## 4. Standard-library surface",
            "",
            "Every top-level declaration under `std/`, signatures only, bodies",
            "elided as `{ ... }`, grouped by module in path order.",
            "",
            std_surface,
            "",
            "## 5. Complete examples",
            "",
            f"{len(example_paths)} whole ACCEPTED programs: the smallest single-file "
            "test per listed chapter that adds new top-level keyword coverage, "
            "chosen deterministically by (byte size, path).",
            "",
            examples,
            "",
            "## 6. Common mistakes",
            "",
            "The most frequent diagnostic codes across the REJECTED corpus,",
            "each with the owning rule's first sentence and the smallest",
            "rejected single-file example (at most 25 lines).",
            "",
            mistakes,
            "",
            "## 7. Tools",
            "",
            TOOLS_SECTION,
            "",
        ]
    )
    doc = re.sub(r"\n{3,}", "\n\n", doc).rstrip("\n") + "\n"

    stats = {
        "rule_counts": rule_counts,
        "examples": [rel(p) for p in example_paths],
        "size": len(doc.encode("utf-8")),
    }
    return doc, errors, stats


def build_pack_within_budget() -> tuple[str, list[str], dict]:
    examples_max = EXAMPLES_MAX
    mistakes_top_n = MISTAKES_TOP_N
    doc, errors, stats = build_pack(examples_max, mistakes_top_n)
    while stats["size"] > SIZE_LIMIT_BYTES and (
        mistakes_top_n > 10 or examples_max > EXAMPLES_MIN
    ):
        if mistakes_top_n > 10:
            mistakes_top_n -= 1
        elif examples_max > EXAMPLES_MIN:
            examples_max -= 1
        doc, errors, stats = build_pack(examples_max, mistakes_top_n)
    stats["examples_max"] = examples_max
    stats["mistakes_top_n"] = mistakes_top_n
    return doc, errors, stats


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true", help="regenerate docs/spec/PACK.md")
    group.add_argument("--check", action="store_true", help="verify docs/spec/PACK.md is current")
    args = parser.parse_args(argv)

    doc, errors, stats = build_pack_within_budget()

    size = stats["size"]
    token_estimate = size // 4
    print(f"PACK.md size: {size} bytes (~{token_estimate} tokens)")
    print(
        "rules indexed per chapter: "
        + ", ".join(f"{ch}={stats['rule_counts'][ch]}" for ch in RULE_INDEX_CHAPTERS)
    )
    print(f"complete examples chosen ({len(stats['examples'])}):")
    for p in stats["examples"]:
        print(f"  {p}")

    if size > SIZE_LIMIT_BYTES:
        print(
            f"FAIL: PACK.md would be {size} bytes, over the "
            f"{SIZE_LIMIT_BYTES}-byte limit even at the minimum example/"
            "mistake counts",
            file=sys.stderr,
        )
        return 1

    if errors:
        for e in errors:
            print(f"error: {e}", file=sys.stderr)
        return 1

    if args.write:
        with open(PACK_PATH, "w", encoding="utf-8") as f:
            f.write(doc)
        print(f"wrote {rel(PACK_PATH)}")
        return 0

    # --check
    if not PACK_PATH.exists():
        print(f"FAIL: {rel(PACK_PATH)} does not exist; run --write", file=sys.stderr)
        return 1
    current = read_text(PACK_PATH)
    if current != doc:
        print(f"FAIL: {rel(PACK_PATH)} is stale; run tools/specpack/gen.py --write", file=sys.stderr)
        return 1
    print(f"{rel(PACK_PATH)} is up to date")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
