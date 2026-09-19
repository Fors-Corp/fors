"""Shared helpers for building the toy binary and locating its patch site."""
import os
import subprocess

DIR = os.path.dirname(os.path.abspath(__file__))
MARKER = (0xC0FFEE1234567890).to_bytes(8, "little")


def build_toy(out_path: str, pad_bytes: int = 0):
    subprocess.run(
        [os.path.join(DIR, "make_toy.sh"), out_path, str(pad_bytes)],
        check=True, capture_output=True, text=True,
    )


def find_value_offset(path: str) -> int:
    """File offset of the little-endian int32 'magic value' patched by the spike."""
    with open(path, "rb") as f:
        data = f.read()
    idx = data.find(MARKER)
    if idx < 0:
        raise RuntimeError("magic marker not found in binary")
    return idx + 8  # marker(8) then int32 value


def i32le(v: int) -> bytes:
    return int(v).to_bytes(4, "little", signed=True)
