#!/usr/bin/env python3
"""Differential-test driver for fors_parse.py.

Prints "path<TAB>ok|err" for every ``*.fors`` file under a directory, using
the exact same `check()` logic `fors_parse.py`'s own `__main__` uses. Does
not change `fors_parse.py`'s behaviour: it only imports and calls it. Used
by `crates/fors-syntax`'s differential test to compare accept/reject
against the Rust parser, invoked as::

    python3 tools/ref/diff_driver.py <root>
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fors_parse  # noqa: E402


def main() -> None:
    root = sys.argv[1]
    for dirpath, _dirs, files in sorted(os.walk(root)):
        for name in sorted(files):
            if not name.endswith(".fors"):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, root)
            with open(path, "r", encoding="utf-8", errors="surrogateescape") as fh:
                src = fh.read()
            err = fors_parse.check(src)
            print(f"{rel}\t{'err' if err else 'ok'}")


if __name__ == "__main__":
    main()
