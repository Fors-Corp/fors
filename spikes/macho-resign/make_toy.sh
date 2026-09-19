#!/bin/bash
# make_toy.sh <out_binary> <pad_bytes>
# Builds the toy arm64 Mach-O from main.c and links in a __TEXT,__pad section
# of <pad_bytes> raw bytes so the binary spans many code-signature pages.
# The linker ad-hoc-signs the result automatically on arm64.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$1"
PAD_BYTES="${2:-0}"

PADFILE="$(mktemp /tmp/toy_pad.XXXXXX)"
trap 'rm -f "$PADFILE"' EXIT

if [ "$PAD_BYTES" -gt 0 ]; then
  python3 - "$PADFILE" "$PAD_BYTES" <<'EOF'
import sys
path, n = sys.argv[1], int(sys.argv[2])
n = int(n)
with open(path, "wb") as f:
    # non-zero, non-repeating-trivial content so pages are real "code-like" data
    chunk = bytes((i * 2654435761) & 0xFF for i in range(65536))
    written = 0
    while written < n:
        take = min(len(chunk), n - written)
        f.write(chunk[:take])
        written += take
EOF
else
  : > "$PADFILE"
fi

if [ "$PAD_BYTES" -gt 0 ]; then
  clang -O0 -arch arm64 "$DIR/main.c" -o "$OUT" -Wl,-sectcreate,__TEXT,__pad,"$PADFILE"
else
  clang -O0 -arch arm64 "$DIR/main.c" -o "$OUT"
fi
echo "built $OUT ($(stat -f%z "$OUT") bytes)"
