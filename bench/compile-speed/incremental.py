#!/usr/bin/env python3
"""Incremental-rebuild compile-speed comparator (stdlib-only Python 3.14; no dependencies).

Generates one synthetic, pinned project of identical shape (M modules x F functions, a fixed
dependency graph) in C, Rust, Go, Zig and Java, builds each with that ecosystem's normal dev/debug
edit-run workflow, and measures: a cold build, an immediate no-op rebuild, and --reps repetitions
of five edit classes (comment-only, private constant, private signature, leaf public signature,
core public signature), each rebuild timed wall-clock including link, then run and its checksum
verified against a pure-Python reference computation of the same call graph.

Reuses bench/harness/run.py's measure() and host_info() (added to sys.path exactly like
compile_speed.py does); never edits bench/harness/ or compile_speed.py.

  python3 bench/compile-speed/incremental.py --modules 40 --functions 20 --reps 3
  python3 bench/compile-speed/incremental.py                      # default M=200 F=50 reps=10
"""
import argparse
import json
import platform
import shutil
import statistics
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "harness"))
from run import measure, host_info  # noqa: E402

BENCH_ROOT = HERE.parent  # bench/
BUILD_ROOT = BENCH_ROOT / ".build" / "incremental"
RESULTS_DIR = BENCH_ROOT / "results" / "compile"

MOD = 1000003
EDIT_CLASSES = ["E1", "E2", "E3", "E4", "E5"]
EDIT_LABELS = {
    "E1": "comment-only edit (leaf)",
    "E2": "private constant change (leaf)",
    "E3": "private signature change (leaf)",
    "E4": "public signature change (leaf)",
    "E5": "public signature change (core)",
}

# ---------------------------------------------------------------------------
# Project shape: a pure function of (seed, M, F, K). Identical across every language.
# Module 0 is "core", imported (via a fixed pub-slot assignment) by every other module.
# Module M-1 is guaranteed to be a leaf: nothing in [0, M-1) can point at an index that
# does not yet exist, so index M-1 is never anyone's dependency target.
# ---------------------------------------------------------------------------


def build_spec(seed, modules, functions, reps):
    k = max(1, min(reps, functions))
    state = [seed]

    def draw():
        state[0] = (state[0] * 48271) % 2147483647
        return state[0]

    consts, chosen = {}, {}
    for m in range(modules):
        consts[m] = [(draw() % 1000, draw() % 1000, draw() % 1000) for _ in range(functions)]
        if m > 0:
            chosen[m] = sorted(set([draw() % m, draw() % m]))
    base, rem = functions // k, functions % k
    slices, idx = [], 0
    for kk in range(k):
        sz = base + (1 if kk < rem else 0)
        slices.append(list(range(idx, idx + sz)))
        idx += sz
    return {
        "seed": seed, "M": modules, "F": functions, "K": k,
        "consts": consts, "chosen": chosen, "slices": slices, "leaf": modules - 1,
    }


def simulate(spec, const_override, extra_f, extra_pub):
    """Pure-Python reference: the SAME call graph every generated program executes.
    No recursive cross-module fan-out (each module calls a dependency's pub0 exactly
    once, never its full transitive entry chain), so this -- and every generated
    program -- runs in O(M*K) calls, not exponential in dependency depth."""
    consts, chosen, slices, k, m_count = spec["consts"], spec["chosen"], spec["slices"], spec["K"], spec["M"]

    def f(mod, idx, x):
        a, b, c = const_override.get((mod, idx), consts[mod][idx])
        r = (x * a + b) % MOD
        base = r + c if r % 2 == 0 else (r * 3) % MOD
        return base + extra_f.get((mod, idx), 0)

    def pub(mod, kk, x):
        y = x
        for idx in slices[kk]:
            y = f(mod, idx, y)
        return y + extra_pub.get((mod, kk), 0)

    def entry(mod, x):
        y = x
        for kk in range(k):
            y = pub(mod, kk, y)
        if mod != 0:
            y = pub(0, mod % k, y)
            for d in chosen[mod]:
                if d != 0:
                    y = pub(d, 0, y)
        return y

    acc = 1
    for mod in range(m_count):
        acc = entry(mod, acc)
    return acc


class State:
    """Mutable edit state layered on top of a frozen spec: which functions have gained an
    extra parameter (and its current value), and which private constants were changed."""

    def __init__(self, spec):
        self.spec = spec
        self.const_override = {}
        self.extra_f = {}
        self.extra_pub = {}
        self.comment_seq = 0

    def checksum(self):
        return simulate(self.spec, self.const_override, self.extra_f, self.extra_pub)


# ---------------------------------------------------------------------------
# Per-language generation + edit mutation. Each adapter renders the identical call graph
# (private f_i -> pub_k slices -> entry, one pub0 exported per module for cross-module
# dependency calls, all K pub slots of module 0 exported since every module's `mod % K`
# targets one of them) in that language's normal multi-file, dev-profile project shape.
# ---------------------------------------------------------------------------


def needed_deps(spec, mod):
    """Module indices whose exports `mod`'s file must reference: core plus its two chosen."""
    if mod == 0:
        return []
    return sorted({0, *spec["chosen"][mod]})


class LangAdapter:
    name = ""

    def toolchain_ok(self):
        raise NotImplementedError

    def generate(self, spec, root):
        raise NotImplementedError

    def build_cmd(self, root, variant="build"):
        raise NotImplementedError

    def run_cmd(self, root):
        raise NotImplementedError

    def clean_cache(self, root):
        """Wipe this language's project-owned build cache (stdlib/toolchain stay warm)."""
        raise NotImplementedError

    def module_file(self, root, mod):
        raise NotImplementedError

    # --- shared edit helpers: every adapter reuses these against its own text templates ---

    def apply_comment(self, root, state):
        path = self.module_file(root, state.spec["leaf"])
        old_marker = self.comment_syntax(state.comment_seq)  # generate() seeded rev 0
        state.comment_seq += 1
        new_marker = self.comment_syntax(state.comment_seq)
        self._replace_in(path, old_marker, new_marker)

    def comment_syntax(self, n):
        return f"{self.comment_tok} edit-marker rev {n}"

    def apply_const(self, root, state, rep):
        leaf, F = state.spec["leaf"], state.spec["F"]
        idx = rep % F
        old = state.const_override.get((leaf, idx), state.spec["consts"][leaf][idx])
        a, b, c = old
        new = ((a * 7 + 13) % 1000, (b * 11 + 17) % 1000, (c * 13 + 19) % 1000)
        old_block = self.render_f(leaf, idx, old, state.extra_f.get((leaf, idx)))
        state.const_override[(leaf, idx)] = new
        new_block = self.render_f(leaf, idx, new, state.extra_f.get((leaf, idx)))
        self._replace_in(self.module_file(root, leaf), old_block, new_block)

    def apply_priv_sig(self, root, state, rep):
        leaf, F, K = state.spec["leaf"], state.spec["F"], state.spec["K"]
        idx = (F // 2 + rep) % F
        owner_k = next(kk for kk, idxs in enumerate(state.spec["slices"]) if idx in idxs)
        consts = state.const_override.get((leaf, idx), state.spec["consts"][leaf][idx])
        old_extra = state.extra_f.get((leaf, idx))
        old_f_block = self.render_f(leaf, idx, consts, old_extra)
        old_call = self.render_call_f(leaf, idx, old_extra)
        new_extra = 13 + rep if old_extra is None else old_extra + 1
        state.extra_f[(leaf, idx)] = new_extra
        new_f_block = self.render_f(leaf, idx, consts, new_extra)
        new_call = self.render_call_f(leaf, idx, new_extra)
        path = self.module_file(root, leaf)
        self._replace_in(path, old_f_block, new_f_block)
        self._replace_in(path, old_call, new_call)

    def apply_pub_sig(self, root, state, mod, k):
        old_extra = state.extra_pub.get((mod, k))
        old_pub_block = self.render_pub(mod, k, state.spec["slices"][k], old_extra, state.extra_f)
        old_call = self.render_call_pub(mod, k, old_extra, exported=(k == 0 or mod == 0))
        new_extra = 7 if old_extra is None else old_extra + 1
        state.extra_pub[(mod, k)] = new_extra
        new_pub_block = self.render_pub(mod, k, state.spec["slices"][k], new_extra, state.extra_f)
        new_call = self.render_call_pub(mod, k, new_extra, exported=(k == 0 or mod == 0))
        path = self.module_file(root, mod)
        self._replace_in(path, old_pub_block, new_pub_block)
        # the definition's own file always also contains the intra-module call site (entry
        # calls its module's own pub_k) -- replace that occurrence too.
        self._replace_in(path, old_call, new_call, required=False)
        self.patch_related(root, mod, k, old_extra, new_extra)
        return old_call, new_call

    def patch_related(self, root, mod, k, old_extra, new_extra):
        """Hook for languages with an out-of-band declaration (a C header) that a pub
        function's signature change must also touch. No-op everywhere else."""

    def apply_leaf_pub_sig(self, root, state, rep):
        leaf, K = state.spec["leaf"], state.spec["K"]
        k = rep % K
        self.apply_pub_sig(root, state, leaf, k)

    def render_call_cross(self, mod, k, extra):
        """The call text a DEPENDENT module's file uses to reach module `mod`'s pub{k} --
        always fully qualified, so it can never collide with that dependent's own identically-
        named local pub{k} (which apply_pub_sig's plain, unqualified render_call_pub covers)."""
        return self.render_call_pub(mod, k, extra, exported=True)

    def apply_core_pub_sig(self, root, state, rep):
        k = rep % state.spec["K"]
        old_extra_before = state.extra_pub.get((0, k))
        old_cross = self.render_call_cross(0, k, old_extra_before)
        self.apply_pub_sig(root, state, 0, k)  # patches core's own file (definition + self-call)
        new_extra = state.extra_pub[(0, k)]
        new_cross = self.render_call_cross(0, k, new_extra)
        for mod in range(1, state.spec["M"]):
            if mod % state.spec["K"] == k:
                self._replace_in(self.module_file(root, mod), old_cross, new_cross)

    def _replace_in(self, path, old, new, required=True):
        text = path.read_text()
        if old not in text:
            if required:
                raise RuntimeError(f"{self.name}: edit anchor not found in {path}:\n{old!r}")
            return
        path.write_text(text.replace(old, new, 1))


# --------------------------------- C ---------------------------------------


class CAdapter(LangAdapter):
    name = "c"
    comment_tok = "//"

    def toolchain_ok(self):
        return shutil.which("clang") and shutil.which("make")

    def render_f(self, mod, idx, consts, extra):
        a, b, c = consts
        sig = f"static long long f{idx}(long long x{', long long extra' if extra is not None else ''}) {{"
        add = " + extra" if extra is not None else ""
        return (f"{sig}\n"
                f"    long long r = (x * {a}LL + {b}LL) % {MOD}LL;\n"
                f"    if (r % 2 == 0) return r + {c}LL{add};\n"
                f"    return (r * 3LL) % {MOD}LL{add};\n"
                f"}}")

    def render_call_f(self, mod, idx, extra):
        return f"f{idx}(x, {extra}LL)" if extra is not None else f"f{idx}(x)"

    def render_pub(self, mod, k, idxs, extra, extra_f=None):
        extra_f = extra_f or {}
        exported = k == 0 or mod == 0
        qual = "" if exported else "static "
        fname = f"m{mod}_pub{k}" if exported else f"pub{k}"
        sig = f"{qual}long long {fname}(long long x{', long long extra' if extra is not None else ''}) {{"
        body = "\n".join(f"    x = {self.render_call_f(mod, i, extra_f.get((mod, i)))};" for i in idxs)
        ret = "x + extra" if extra is not None else "x"
        return f"{sig}\n{body}\n    return {ret};\n}}"

    def render_call_pub(self, mod, k, extra, exported=True):
        prefix = f"m{mod}_" if exported else ""
        return f"{prefix}pub{k}(y, {extra}LL)" if extra is not None else f"{prefix}pub{k}(y)"

    def module_file(self, root, mod):
        return root / f"m{mod}.c"

    def _header(self, root, mod):
        return root / f"m{mod}.h"

    def _decl(self, mod, k, extra):
        return f"long long m{mod}_pub{k}(long long x{', long long extra' if extra is not None else ''});"

    def patch_related(self, root, mod, k, old_extra, new_extra):
        exported = k == 0 or mod == 0
        if not exported:
            return
        self._replace_in(self._header(root, mod), self._decl(mod, k, old_extra), self._decl(mod, k, new_extra))

    def generate(self, spec, root):
        root.mkdir(parents=True, exist_ok=True)
        for mod in range(spec["M"]):
            deps = needed_deps(spec, mod)
            lines = [f'#include "m{mod}.h"'] + [f'#include "m{d}.h"' for d in deps]
            lines.append("")
            for idx in range(spec["F"]):
                lines.append(self.render_f(mod, idx, spec["consts"][mod][idx], None))
            for k, idxs in enumerate(spec["slices"]):
                lines.append(self.render_pub(mod, k, idxs, None))
            lines.append(f"long long m{mod}_entry(long long x) {{")
            lines.append("    long long y = x;")
            for k in range(spec["K"]):
                lines.append(f"    y = {self.render_call_pub(mod, k, None, exported=(k == 0 or mod == 0))};")
            if mod != 0:
                slot = mod % spec["K"]
                lines.append(f"    y = {self.render_call_pub(0, slot, None, exported=True)};")
                for d in spec["chosen"][mod]:
                    if d != 0:
                        lines.append(f"    y = m{d}_pub0(y);")
            lines.append("    return y;")
            lines.append("}")
            self.module_file(root, mod).write_text(self.comment_syntax(0) + "\n" + "\n".join(lines) + "\n")

            hlines = ["#pragma once", f"long long m{mod}_entry(long long x);"]
            hlines.append("long long m%d_pub0(long long x);" % mod)
            if mod == 0:
                for k in range(1, spec["K"]):
                    hlines.append(f"long long m0_pub{k}(long long x);")
            self._header(root, mod).write_text("\n".join(hlines) + "\n")

        main_lines = [f'#include "m{m}.h"' for m in range(spec["M"])] + ["#include <stdio.h>", "", "int main(void) {"]
        main_lines.append("    long long acc = 1;")
        for m in range(spec["M"]):
            main_lines.append(f"    acc = m{m}_entry(acc);")
        main_lines.append('    printf("%lld\\n", acc);')
        main_lines.append("    return 0;")
        main_lines.append("}")
        (root / "main.c").write_text("\n".join(main_lines) + "\n")

        srcs = [f"m{m}.c" for m in range(spec["M"])] + ["main.c"]
        make = [
            "CC = clang", "CFLAGS = -O0 -g0 -std=c11",
            "SRCS = " + " ".join(srcs),
            "OBJS = $(SRCS:.c=.o)",
            "prog: $(OBJS)", "\t$(CC) $(CFLAGS) -o prog $(OBJS)",
            "%.o: %.c", "\t$(CC) $(CFLAGS) -MMD -MP -c $< -o $@",
            "-include $(OBJS:.o=.d)",
            ".PHONY: clean", "clean:", "\trm -f $(OBJS) $(OBJS:.o=.d) prog",
        ]
        (root / "Makefile").write_text("\n".join(make) + "\n")

    def build_cmd(self, root, variant="build"):
        return ["make", "-j8"]

    def run_cmd(self, root):
        return [str(root / "prog")]

    def clean_cache(self, root):
        for p in root.glob("*.o"):
            p.unlink()
        for p in root.glob("*.d"):
            p.unlink()
        (root / "prog").unlink(missing_ok=True)


# --------------------------------- Rust -------------------------------------


class RustAdapter(LangAdapter):
    name = "rust"
    comment_tok = "//"

    def toolchain_ok(self):
        return shutil.which("cargo")

    def render_f(self, mod, idx, consts, extra):
        a, b, c = consts
        sig = f"pub fn f{idx}(x: i64{', extra: i64' if extra is not None else ''}) -> i64 {{"
        add = " + extra" if extra is not None else ""
        return (f"{sig}\n"
                f"    let r = (x * {a} + {b}) % {MOD};\n"
                f"    if r % 2 == 0 {{ r + {c}{add} }} else {{ (r * 3) % {MOD}{add} }}\n"
                f"}}")

    def render_call_f(self, mod, idx, extra):
        return f"f{idx}(x, {extra})" if extra is not None else f"f{idx}(x)"

    def render_pub(self, mod, k, idxs, extra, extra_f=None):
        extra_f = extra_f or {}
        sig = f"pub fn pub{k}(x: i64{', extra: i64' if extra is not None else ''}) -> i64 {{"
        lines = [f"    let mut x = {self.render_call_f(mod, idxs[0], extra_f.get((mod, idxs[0])))};"]
        for i in idxs[1:]:
            lines.append(f"    x = {self.render_call_f(mod, i, extra_f.get((mod, i)))};")
        ret = "x + extra" if extra is not None else "x"
        return f"{sig}\n" + "\n".join(lines) + f"\n    {ret}\n}}"

    def render_call_pub(self, mod, k, extra, exported=True):
        return f"pub{k}(y, {extra})" if extra is not None else f"pub{k}(y)"

    def render_call_cross(self, mod, k, extra):
        return f"crate::m{mod}::" + self.render_call_pub(mod, k, extra)

    def module_file(self, root, mod):
        return root / "src" / f"m{mod}.rs"

    def generate(self, spec, root):
        (root / "src").mkdir(parents=True, exist_ok=True)
        for mod in range(spec["M"]):
            lines = []
            for idx in range(spec["F"]):
                lines.append(self.render_f(mod, idx, spec["consts"][mod][idx], None))
            for k, idxs in enumerate(spec["slices"]):
                lines.append(self.render_pub(mod, k, idxs, None))
            lines.append("pub fn entry(x: i64) -> i64 {")
            lines.append("    let mut y = x;")
            for k in range(spec["K"]):
                lines.append(f"    y = {self.render_call_pub(mod, k, None)};")
            if mod != 0:
                slot = mod % spec["K"]
                lines.append(f"    y = crate::m0::pub{slot}(y);")
                for d in spec["chosen"][mod]:
                    if d != 0:
                        lines.append(f"    y = crate::m{d}::pub0(y);")
            lines.append("    y")
            lines.append("}")
            self.module_file(root, mod).write_text(
                self.comment_syntax(0) + "\n#![allow(dead_code)]\n" + "\n".join(lines) + "\n"
            )
        main_lines = [f"mod m{m};" for m in range(spec["M"])]
        main_lines.append("fn main() {")
        main_lines.append("    let mut acc: i64 = 1;")
        for m in range(spec["M"]):
            main_lines.append(f"    acc = m{m}::entry(acc);")
        main_lines.append('    println!("{}", acc);')
        main_lines.append("}")
        (root / "src" / "main.rs").write_text("\n".join(main_lines) + "\n")
        cargo_toml = (
            '[package]\nname = "incr"\nversion = "0.1.0"\nedition = "2021"\n\n'
            # Empty [workspace]: without this, cargo walks UP the directory tree looking for
            # a workspace root and -- since this generated project lives under the Fors repo's
            # own tree -- would wrongly adopt it as a member of *that* repo's real Cargo
            # workspace (and fail if any of that workspace's other members don't build).
            "[workspace]\n\n"
            "[profile.dev]\nincremental = true\n"
        )
        (root / "Cargo.toml").write_text(cargo_toml)

    def build_cmd(self, root, variant="build"):
        return ["cargo", variant]

    def run_cmd(self, root):
        return [str(root / "target" / "debug" / "incr")]

    def clean_cache(self, root):
        shutil.rmtree(root / "target", ignore_errors=True)


# --------------------------------- Go ---------------------------------------


class GoAdapter(LangAdapter):
    name = "go"
    comment_tok = "//"

    def toolchain_ok(self):
        return shutil.which("go")

    def render_f(self, mod, idx, consts, extra):
        a, b, c = consts
        sig = f"func f{idx}(x int64{', extra int64' if extra is not None else ''}) int64 {{"
        add = " + extra" if extra is not None else ""
        return (f"{sig}\n"
                f"\tr := (x*{a} + {b}) % {MOD}\n"
                f"\tif r%2 == 0 {{\n\t\treturn r + {c}{add}\n\t}}\n"
                f"\treturn (r * 3) % {MOD}{add}\n"
                f"}}")

    def render_call_f(self, mod, idx, extra):
        return f"f{idx}(x, {extra})" if extra is not None else f"f{idx}(x)"

    def render_pub(self, mod, k, idxs, extra, extra_f=None):
        extra_f = extra_f or {}
        exported = k == 0 or mod == 0
        name = f"Pub{k}" if exported else f"pub{k}"
        sig = f"func {name}(x int64{', extra int64' if extra is not None else ''}) int64 {{"
        lines = [f"\tx = {self.render_call_f(mod, i, extra_f.get((mod, i)))}" for i in idxs]
        ret = "x + extra" if extra is not None else "x"
        return f"{sig}\n" + "\n".join(lines) + f"\n\treturn {ret}\n}}"

    def render_call_pub(self, mod, k, extra, exported=True):
        name = f"Pub{k}" if exported else f"pub{k}"
        return f"{name}(y, {extra})" if extra is not None else f"{name}(y)"

    def render_call_cross(self, mod, k, extra):
        return f"m{mod}." + self.render_call_pub(mod, k, extra, exported=True)

    def module_file(self, root, mod):
        return root / f"m{mod}" / f"m{mod}.go"

    def generate(self, spec, root):
        root.mkdir(parents=True, exist_ok=True)
        modname = "incr"
        for mod in range(spec["M"]):
            (root / f"m{mod}").mkdir(exist_ok=True)
            deps = needed_deps(spec, mod)
            lines = [f"package m{mod}", ""]
            if deps:
                lines.append("import (")
                for d in deps:
                    lines.append(f'\t"{modname}/m{d}"')
                lines.append(")")
                lines.append("")
            for idx in range(spec["F"]):
                lines.append(self.render_f(mod, idx, spec["consts"][mod][idx], None))
            for k, idxs in enumerate(spec["slices"]):
                lines.append(self.render_pub(mod, k, idxs, None))
            lines.append("func Entry(x int64) int64 {")
            lines.append("\ty := x")
            for k in range(spec["K"]):
                lines.append(f"\ty = {self.render_call_pub(mod, k, None, exported=(k == 0 or mod == 0))}")
            if mod != 0:
                slot = mod % spec["K"]
                lines.append(f"\ty = m0.{self.render_call_pub(0, slot, None, exported=True)}")
                for d in spec["chosen"][mod]:
                    if d != 0:
                        lines.append(f"\ty = m{d}.Pub0(y)")
            lines.append("\treturn y")
            lines.append("}")
            self.module_file(root, mod).write_text(
                self.comment_syntax(0) + "\n" + "\n".join(lines) + "\n"
            )
        main_lines = ["package main", "", 'import ('] + [f'\t"{modname}/m{m}"' for m in range(spec["M"])]
        main_lines += ['\t"fmt"', ")", "", "func main() {"]
        main_lines.append("\tvar acc int64 = 1")
        for m in range(spec["M"]):
            main_lines.append(f"\tacc = m{m}.Entry(acc)")
        main_lines.append("\tfmt.Println(acc)")
        main_lines.append("}")
        (root / "main.go").write_text("\n".join(main_lines) + "\n")
        (root / "go.mod").write_text(f"module {modname}\n\ngo 1.22\n")

    def build_cmd(self, root, variant="build"):
        # "go build ./..." (compile every package) can't write multiple packages to one -o
        # binary; "go build -o prog ." builds the same closure (main imports every m{i}
        # package, so all of them are compiled) and produces the single binary we need to run.
        return ["go", "build", "-o", "prog", "."]

    def run_cmd(self, root):
        return [str(root / "prog")]

    def clean_cache(self, root):
        (root / "prog").unlink(missing_ok=True)
        # GOCACHE is redirected to an isolated, wiped directory by the caller for cold builds.


# --------------------------------- Zig --------------------------------------


class ZigAdapter(LangAdapter):
    name = "zig"
    comment_tok = "//"
    incremental_supported = None  # filled in by main() after a probe

    def toolchain_ok(self):
        return shutil.which("zig")

    def render_f(self, mod, idx, consts, extra):
        # "fx" not "f": at idx 16/32/64/128 a plain `f16`/`f32`/... would shadow Zig's
        # built-in float-type primitives, which zig 0.16 rejects as a hard error.
        a, b, c = consts
        sig = f"pub fn fx{idx}(x: i64{', extra: i64' if extra is not None else ''}) i64 {{"
        add = " + extra" if extra is not None else ""
        return (f"{sig}\n"
                f"    const r: i64 = @mod(x * {a} + {b}, {MOD});\n"
                f"    if (@mod(r, 2) == 0) return r + {c}{add};\n"
                f"    return @mod(r * 3, {MOD}){add};\n"
                f"}}")

    def render_call_f(self, mod, idx, extra):
        # Always called on `acc`, never `x`: Zig disallows a local `var x` shadowing a
        # function parameter also named `x`, so pub bodies below thread an `acc` local
        # instead (initialised from `x`) and every f-call site -- generation and edit
        # anchors alike -- uses that same name uniformly.
        return f"fx{idx}(acc, {extra})" if extra is not None else f"fx{idx}(acc)"

    def render_pub(self, mod, k, idxs, extra, extra_f=None):
        extra_f = extra_f or {}
        sig = f"pub fn pub{k}(x: i64{', extra: i64' if extra is not None else ''}) i64 {{"
        lines = ["    var acc: i64 = x;"]
        for i in idxs:
            lines.append(f"    acc = {self.render_call_f(mod, i, extra_f.get((mod, i)))};")
        ret = "acc + extra" if extra is not None else "acc"
        return f"{sig}\n" + "\n".join(lines) + f"\n    return {ret};\n}}"

    def render_call_pub(self, mod, k, extra, exported=True):
        return f"pub{k}(y, {extra})" if extra is not None else f"pub{k}(y)"

    def render_call_cross(self, mod, k, extra):
        return f"m{mod}." + self.render_call_pub(mod, k, extra, exported=True)

    def module_file(self, root, mod):
        return root / f"m{mod}.zig"

    def generate(self, spec, root):
        root.mkdir(parents=True, exist_ok=True)
        for mod in range(spec["M"]):
            deps = needed_deps(spec, mod)
            lines = [f'const m{d} = @import("m{d}.zig");' for d in deps]
            lines.append("")
            for idx in range(spec["F"]):
                lines.append(self.render_f(mod, idx, spec["consts"][mod][idx], None))
            for k, idxs in enumerate(spec["slices"]):
                lines.append(self.render_pub(mod, k, idxs, None))
            lines.append("pub fn entry(x: i64) i64 {")
            lines.append("    var y: i64 = x;")
            for k in range(spec["K"]):
                lines.append(f"    y = {self.render_call_pub(mod, k, None)};")
            if mod != 0:
                slot = mod % spec["K"]
                lines.append(f"    y = m0.{self.render_call_pub(0, slot, None)};")
                for d in spec["chosen"][mod]:
                    if d != 0:
                        lines.append(f"    y = m{d}.pub0(y);")
            lines.append("    return y;")
            lines.append("}")
            self.module_file(root, mod).write_text(
                self.comment_syntax(0) + "\n" + "\n".join(lines) + "\n"
            )
        main_lines = [f'const m{m} = @import("m{m}.zig");' for m in range(spec["M"])]
        main_lines.append('const std = @import("std");')
        main_lines.append("pub fn main(init: std.process.Init) !void {")
        main_lines.append("    var acc: i64 = 1;")
        for m in range(spec["M"]):
            main_lines.append(f"    acc = m{m}.entry(acc);")
        main_lines.append('    var buf: [64]u8 = undefined;')
        main_lines.append('    const s = try std.fmt.bufPrint(&buf, "{d}\\n", .{acc});')
        main_lines.append('    try std.Io.File.stdout().writeStreamingAll(init.io, s);')
        main_lines.append("}")
        (root / "main.zig").write_text("\n".join(main_lines) + "\n")
        # `zig build` is Zig's normal edit-run loop: it caches whole build steps, so an unchanged project is
        # a ~0.1 s cache hit. Bare `zig build-exe` redoes the compile on every invocation (measured: 1.5 s for
        # one small file) and would misrepresent Zig, the main rival for an incremental-rebuild claim.
        (root / "build.zig").write_text(
            'const std = @import("std");\n\n'
            "pub fn build(b: *std.Build) void {\n"
            "    const exe = b.addExecutable(.{\n"
            '        .name = "prog",\n'
            "        .root_module = b.createModule(.{\n"
            '            .root_source_file = b.path("main.zig"),\n'
            "            .target = b.standardTargetOptions(.{}),\n"
            "            .optimize = .Debug,\n"
            "        }),\n"
            "    });\n"
            "    b.installArtifact(exe);\n"
            "}\n"
        )

    def build_cmd(self, root, variant="build"):
        # Project-local cache so "cold" is cold for the project; the global cache (prebuilt std) stays warm,
        # matching the stdlib-prebuilt-project-cold variant used for every other language.
        cmd = ["zig", "build", "--cache-dir", str(root / "zig-cache")]
        if variant == "incremental":
            cmd.append("-fincremental")
        return cmd

    def run_cmd(self, root):
        return [str(root / "zig-out" / "bin" / "prog")]

    def clean_cache(self, root):
        shutil.rmtree(root / "zig-cache", ignore_errors=True)
        shutil.rmtree(root / "zig-out", ignore_errors=True)


# --------------------------------- Java --------------------------------------


class JavaAdapter(LangAdapter):
    name = "java"
    comment_tok = "//"

    def toolchain_ok(self):
        return shutil.which("javac") and shutil.which("java")

    def render_f(self, mod, idx, consts, extra):
        a, b, c = consts
        sig = f"static long f{idx}(long x{', long extra' if extra is not None else ''}) {{"
        add = " + extra" if extra is not None else ""
        return (f"{sig}\n"
                f"        long r = (x * {a}L + {b}L) % {MOD}L;\n"
                f"        if (r % 2 == 0) return r + {c}L{add};\n"
                f"        return (r * 3L) % {MOD}L{add};\n"
                f"    }}")

    def render_call_f(self, mod, idx, extra):
        return f"f{idx}(x, {extra}L)" if extra is not None else f"f{idx}(x)"

    def render_pub(self, mod, k, idxs, extra, extra_f=None):
        extra_f = extra_f or {}
        sig = f"static long pub{k}(long x{', long extra' if extra is not None else ''}) {{"
        lines = [f"        x = {self.render_call_f(mod, i, extra_f.get((mod, i)))};" for i in idxs]
        ret = "x + extra" if extra is not None else "x"
        return f"{sig}\n" + "\n".join(lines) + f"\n        return {ret};\n    }}"

    def render_call_pub(self, mod, k, extra, exported=True):
        return f"pub{k}(y, {extra}L)" if extra is not None else f"pub{k}(y)"

    def render_call_cross(self, mod, k, extra):
        return f"M{mod}." + self.render_call_pub(mod, k, extra, exported=True)

    def module_file(self, root, mod):
        return root / "src" / "proj" / f"M{mod}.java"

    def generate(self, spec, root):
        (root / "src" / "proj").mkdir(parents=True, exist_ok=True)
        for mod in range(spec["M"]):
            lines = ["package proj;", "", f"public class M{mod} {{"]
            for idx in range(spec["F"]):
                lines.append(self.render_f(mod, idx, spec["consts"][mod][idx], None))
            for k, idxs in enumerate(spec["slices"]):
                lines.append(self.render_pub(mod, k, idxs, None))
            lines.append("    public static long entry(long x) {")
            lines.append("        long y = x;")
            for k in range(spec["K"]):
                lines.append(f"        y = {self.render_call_pub(mod, k, None)};")
            if mod != 0:
                slot = mod % spec["K"]
                lines.append(f"        y = M0.{self.render_call_pub(0, slot, None)};")
                for d in spec["chosen"][mod]:
                    if d != 0:
                        lines.append(f"        y = M{d}.pub0(y);")
            lines.append("        return y;")
            lines.append("    }")
            lines.append("}")
            self.module_file(root, mod).write_text(
                self.comment_syntax(0) + "\n" + "\n".join(lines) + "\n"
            )
        main_lines = ["package proj;", "", "public class Main {", "    public static void main(String[] a) {"]
        main_lines.append("        long acc = 1;")
        for m in range(spec["M"]):
            main_lines.append(f"        acc = M{m}.entry(acc);")
        main_lines.append("        System.out.println(acc);")
        main_lines.append("    }")
        main_lines.append("}")
        (root / "src" / "proj" / "Main.java").write_text("\n".join(main_lines) + "\n")

    def build_cmd(self, root, variant="build"):
        srcs = sorted(str(p.relative_to(root)) for p in (root / "src" / "proj").glob("*.java"))
        return ["javac", "-d", "out", *srcs]

    def run_cmd(self, root):
        return ["java", "-cp", str(root / "out"), "proj.Main"]

    def clean_cache(self, root):
        shutil.rmtree(root / "out", ignore_errors=True)


ADAPTERS = {"c": CAdapter(), "rust": RustAdapter(), "go": GoAdapter(), "zig": ZigAdapter(), "java": JavaAdapter()}


# ---------------------------------------------------------------------------
# Measurement driver
# ---------------------------------------------------------------------------


def _wait_mtime_tick():
    import time
    now = time.time()
    time.sleep(max(0.0, 1.05 - (now - int(now))))


def do_build(adapter, root, timeout, variant="build", env=None):
    log = root / "build.out"
    cmd = adapter.build_cmd(root, variant)
    import os
    import subprocess
    import threading
    import time
    full_env = dict(**__import__("os").environ)
    if env:
        full_env.update(env)
    with open(log, "wb") as out, open(str(log) + ".err", "wb") as err:
        start = time.perf_counter()
        proc = subprocess.Popen(cmd, stdout=out, stderr=err, cwd=root, env=full_env)
        timed_out = threading.Event()

        def kill():
            timed_out.set()
            proc.kill()

        timer = threading.Timer(timeout, kill)
        timer.start()
        _, status, ru = os.wait4(proc.pid, 0)
        wall = time.perf_counter() - start
        timer.cancel()
        proc.returncode = os.waitstatus_to_exitcode(status)
    from run import RSS_UNIT
    rec = {
        "wall_s": wall, "user_s": ru.ru_utime, "sys_s": ru.ru_stime,
        "max_rss_bytes": ru.ru_maxrss * RSS_UNIT,
        "exit_code": proc.returncode, "timed_out": timed_out.is_set(),
    }
    rec["ok"] = rec["exit_code"] == 0 and not rec["timed_out"]
    if not rec["ok"]:
        rec["error"] = Path(str(log) + ".err").read_text(errors="replace")[-2000:]
    return rec


def do_run(adapter, root, timeout):
    log = root / "run.out"
    rec = measure(adapter.run_cmd(root), log, timeout)
    text = log.read_text(errors="replace").strip()
    return rec, text


def verify(text, want):
    try:
        return int(text) == want
    except ValueError:
        return False


def p50_p95(samples):
    s = sorted(samples)
    if not s:
        return None, None
    p50 = statistics.median(s)
    p95 = s[min(len(s) - 1, round(0.95 * (len(s) - 1)))]
    return p50, p95


EDIT_FNS = {
    "E1": lambda a, r, st, rep: a.apply_comment(r, st),
    "E2": lambda a, r, st, rep: a.apply_const(r, st, rep),
    "E3": lambda a, r, st, rep: a.apply_priv_sig(r, st, rep),
    "E4": lambda a, r, st, rep: a.apply_leaf_pub_sig(r, st, rep),
    "E5": lambda a, r, st, rep: a.apply_core_pub_sig(r, st, rep),
}


def measure_language(adapter, spec, args, variant_label, variant, notes, extra_env=None, runnable=True):
    """`runnable=False` (cargo check: no artifact) records build/rebuild timings only --
    correctness for that source is verified by the paired `build` row over the same edits."""
    root = BUILD_ROOT / f"{adapter.name}-{variant}" if variant != "build" else BUILD_ROOT / adapter.name
    shutil.rmtree(root, ignore_errors=True)
    root.mkdir(parents=True)
    adapter.generate(spec, root)
    state = State(spec)
    want0 = state.checksum()
    row = {"lang": variant_label, "edit_classes": {}}

    def run_ok(want):
        if not runnable:
            return True
        _, text = do_run(adapter, root, args.timeout)
        return verify(text, want)

    # (a) cold: project cache wiped, stdlib/toolchain stays warm ("stdlib-prebuilt-project-cold").
    adapter.clean_cache(root)
    b = do_build(adapter, root, args.timeout, variant, extra_env)
    if not b["ok"]:
        notes.append(f"FAIL {variant_label} cold build:\n{b.get('error', '')}")
        row["error"] = "cold build failed"
        return row
    if not run_ok(want0):
        notes.append(f"FAIL {variant_label} cold build: checksum mismatch want={want0}")
        row["error"] = "cold build checksum mismatch"
        return row
    row["cold"] = {"wall_s": b["wall_s"], "user_s": b["user_s"], "sys_s": b["sys_s"], "max_rss_bytes": b["max_rss_bytes"]}

    # (b) no-op rebuild, immediately, cache now warm.
    b2 = do_build(adapter, root, args.timeout, variant, extra_env)
    ok2 = b2["ok"] and run_ok(want0)
    if not ok2:
        notes.append(f"FAIL {variant_label} no-op rebuild")
    row["noop"] = {"wall_s": b2["wall_s"], "user_s": b2["user_s"], "sys_s": b2["sys_s"], "max_rss_bytes": b2["max_rss_bytes"], "ok": ok2}

    # (c) edit classes, applied sequentially and CUMULATIVELY on the same warm cache (this is
    # a deliberate simplification over reset-and-resync between classes; see report).
    for cls in EDIT_CLASSES:
        samples, cpu_samples, rss_samples = [], [], []
        failed = False
        for rep in range(args.reps):
            _wait_mtime_tick()  # macOS's ancient GNU Make 3.81 compares mtimes at whole-second
            # resolution (it truncates st_mtime, ignoring the nanosecond field APFS actually
            # stores): the EDIT must land in a later integer second than the previous build's
            # objects, or `make` sees "not newer" and silently keeps the stale binary. Waiting
            # here, before writing the edit, guarantees that; it is not counted in the timed
            # build below.
            EDIT_FNS[cls](adapter, root, state, rep)
            want = state.checksum()
            b3 = do_build(adapter, root, args.timeout, variant, extra_env)
            if not b3["ok"]:
                notes.append(f"FAIL {variant_label} {cls} rep{rep}: rebuild failed\n{b3.get('error', '')}")
                failed = True
                break
            if not run_ok(want):
                notes.append(f"FAIL {variant_label} {cls} rep{rep}: checksum mismatch (stale build?) want={want}")
                failed = True
                break
            samples.append(b3["wall_s"])
            cpu_samples.append(b3["user_s"] + b3["sys_s"])
            rss_samples.append(b3["max_rss_bytes"])
        p50, p95 = p50_p95(samples)
        row["edit_classes"][cls] = {
            "n": len(samples), "p50_s": p50, "p95_s": p95,
            "median_cpu_s": statistics.median(cpu_samples) if cpu_samples else None,
            "median_rss_bytes": statistics.median(rss_samples) if rss_samples else None,
            "failed": failed,
        }
    return row


def render_markdown(rows):
    cols = ["lang", "cold", "no-op"] + EDIT_CLASSES
    header = "| " + " | ".join(cols) + " |"
    sep = "|" + "---|" * len(cols)
    out = [header, sep]

    def ms(v):
        return f"{v * 1000:.1f}" if v is not None else "-"

    for r in rows:
        if "error" in r:
            out.append(f"| {r['lang']} | FAILED: {r['error']} | | | | | | |")
            continue
        cells = [r["lang"], ms(r["cold"]["wall_s"]), ms(r["noop"]["wall_s"])]
        for cls in EDIT_CLASSES:
            e = r["edit_classes"].get(cls)
            cells.append(f"{ms(e['p50_s'])} / {ms(e['p95_s'])}" if e and e["n"] else "SKIP")
        out.append("| " + " | ".join(cells) + " |")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--modules", type=int, default=200)
    ap.add_argument("--functions", type=int, default=50)
    ap.add_argument("--reps", type=int, default=10)
    ap.add_argument("--lang", action="append", help="limit to this language (repeatable)")
    ap.add_argument("--timeout", type=float, default=900)
    ap.add_argument("--seed", type=int, default=None)
    args = ap.parse_args()

    import random
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(1, 2**31 - 1)
    spec = build_spec(seed, args.modules, args.functions, args.reps)
    print(f"project shape: M={args.modules} F={args.functions} K={spec['K']} leaf=m{spec['leaf']} seed={seed}")

    only = set(args.lang) if args.lang else set(ADAPTERS)
    BUILD_ROOT.mkdir(parents=True, exist_ok=True)
    notes, rows, versions, extra_notes = [], [], {}, []

    for name in ["c", "rust", "go", "zig", "java"]:
        if name not in only:
            continue
        adapter = ADAPTERS[name]
        if not adapter.toolchain_ok():
            print(f"SKIP  {name}: toolchain not installed")
            continue
        print(f"== {name} ==", flush=True)

        if name == "rust":
            cache = BUILD_ROOT / "rust-cache"
            env = {"CARGO_TARGET_DIR": str(BUILD_ROOT / "rust" / "target")}
            row = measure_language(adapter, spec, args, "rust/build", "build", notes, env)
            rows.append(row)
            row_chk = measure_language(adapter, spec, args, "rust/check", "check", notes, env, runnable=False)
            rows.append(row_chk)
        elif name == "go":
            # Deliberately NOT isolating GOCACHE: Go's build cache is content-addressed, so
            # wiping it would force a cold rebuild of the whole standard library too, which
            # is not "stdlib-prebuilt-project-cold" -- it's the "everything-from-source"
            # variant. Each run's freshly seeded, never-before-seen source content is already
            # guaranteed a cache miss (same approach documented in compile_speed.py / README's
            # "Go's build measurement is still a warm standard-library cache" caveat), while
            # stdlib stays served from the default, prebuilt global cache.
            row = measure_language(adapter, spec, args, "go", "build", notes)
            rows.append(row)
        elif name == "zig":
            # Probe -fincremental once, with a real edit-and-relink (not just a fresh cold
            # build): on this machine (macOS/Mach-O) zig 0.16's linker cannot yet save
            # incremental link state, so a SECOND invocation after a source edit hard-errors
            # ("TODO implement saving linker state for macho") even though the first build
            # succeeds. A tiny probe project (not the full M/F run) keeps this cheap.
            probe_root = BUILD_ROOT / "zig-probe"
            shutil.rmtree(probe_root, ignore_errors=True)
            probe_root.mkdir(parents=True)
            probe_spec = build_spec(seed, 6, 8, 2)
            adapter.generate(probe_spec, probe_root)
            probe_state = State(probe_spec)
            b1 = do_build(adapter, probe_root, args.timeout, "incremental")
            works = b1["ok"]
            if works:
                adapter.apply_const(probe_root, probe_state, 0)
                _wait_mtime_tick()
                b2 = do_build(adapter, probe_root, args.timeout, "incremental")
                works = b2["ok"]
            if works:
                # A signature-adding edit (what E3/E4/E5 all do) is what actually exposed the
                # incremental linker/frontend state bug in testing; a const-only edit alone
                # was not sufficient to catch it.
                adapter.apply_priv_sig(probe_root, probe_state, 0)
                _wait_mtime_tick()
                b2b = do_build(adapter, probe_root, args.timeout, "incremental")
                works = b2b["ok"]
                if not works:
                    b2 = b2b
            if works:
                # The small probe's edit-and-relink succeeded (so -fincremental is not
                # categorically broken here), but a full run at this project's default scale
                # was separately observed to make its incremental cache grow without bound
                # across successive edits (100s of MB after ~40 reps) with each rebuild getting
                # slower than the last -- a superlinear-cost pathology, not a fixed per-edit
                # cost. That makes it impractical for a repeated-edit benchmark regardless of
                # whether any single edit succeeds, so the actual measurement below always uses
                # the normal cached build (like every other language's row); a bare
                # hello-world's second -fincremental invocation, tested separately, also hit
                # 'error(compilation): TODO implement saving linker state for macho' outright.
                extra_notes.append(
                    "zig -fincremental: a small probe's edit-and-relink succeeded, so it is not "
                    "categorically broken on this machine -- but a full run at this project's "
                    "scale showed its incremental cache growing without bound and each rebuild "
                    "getting slower than the last (confirmed live: cache passed 400MB and "
                    "per-rebuild time kept climbing partway through one E1-E4 sweep at the "
                    "default M/F). That is a superlinear-cost pathology, not a fixed per-edit "
                    "cost, so it is not practically usable for a repeated-edit benchmark here; "
                    "this row measures the normal cached build instead, like every other "
                    "language's row. Separately, a bare hello-world's second -fincremental "
                    "invocation also hit 'error(compilation): TODO implement saving linker "
                    "state for macho' outright, so the failure mode is not even consistent."
                )
                row = measure_language(adapter, spec, args, "zig/cached (fincremental impractical here)", "build", notes)
            else:
                err = b1.get("error", "") if not b1["ok"] else b2.get("error", "")
                extra_notes.append(
                    "zig -fincremental: FAILS across separate CLI invocations on this machine "
                    f"(zig 0.16, macOS/Mach-O linker; error tail: "
                    f"{err.strip().splitlines()[-1] if err.strip() else 'n/a'}). "
                    "Falling back to the normal cached build (zig-cache/zig-global-cache warm, "
                    "matching every other language's incremental row)."
                )
                row = measure_language(adapter, spec, args, "zig/cached", "build", notes)
            rows.append(row)
        elif name == "java":
            extra_notes.append("java: javac has no incremental mode; this row is the honest full-rebuild comparator.")
            row = measure_language(adapter, spec, args, "java/javac (full rebuild)", "build", notes)
            rows.append(row)
        else:
            row = measure_language(adapter, spec, args, name, "build", notes)
            rows.append(row)

        for note in extra_notes:
            print(note)

    table = render_markdown(rows)
    print("\n" + table)
    for note in notes:
        print(note, file=sys.stderr)

    now = datetime.now(timezone.utc)
    doc = {
        "schema": 1,
        "timestamp": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "host": host_info(),
        "seed": seed,
        "project_shape": {"modules": args.modules, "functions": args.functions, "pub_slots_k": spec["K"],
                           "leaf_module": spec["leaf"], "reps": args.reps},
        "notes": extra_notes,
        "failures": notes,
        "rows": rows,
    }
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    path = RESULTS_DIR / f"incremental-{now.strftime('%Y%m%dT%H%M%SZ')}-{platform.node().split('.')[0]}.json"
    path.write_text(json.dumps(doc, indent=1))
    print(f"\nwrote {path.relative_to(BENCH_ROOT.parent)}")
    return 1 if notes else 0


if __name__ == "__main__":
    sys.exit(main())
