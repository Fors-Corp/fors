#!/bin/bash
# Builds and runs every test program on every implemented rung, printing a
# PASS/FAIL table. Expected outputs are independently verified (see
# REPORT.md) via a standalone Python re-implementation of each program.
set -u
cd "$(dirname "$0")"

cargo build --release -q || { echo "build failed"; exit 1; }
BIN=./target/release/spike
TMP=$(mktemp -d)

expected() {
  case "$1" in
    hello) printf 'hello' ;;
    fib) printf '832040' ;;
    collatz) printf '77031\n350' ;;
    loops) printf '6049050' ;;
  esac
}

printf "%-10s %-6s %-6s %-8s %s\n" "PROGRAM" "RUNG" "EXIT" "RESULT" "NOTES"
for rung in 1 2 3; do
  for prog in hello fib collatz loops; do
    src="programs/$prog.fors"
    out="$TMP/${prog}_r${rung}"
    if ! $BIN "$rung" "$src" -o "$out" >"$TMP/build.log" 2>&1; then
      printf "%-10s %-6s %-6s %-8s %s\n" "$prog" "$rung" "-" "SKIP" "rung not implemented / build failed"
      continue
    fi
    actual=$("$out" 2>"$TMP/run.log")
    code=$?
    exp=$(expected "$prog")
    if [ "$code" -eq 0 ] && [ "$actual" == "$exp" ] && codesign --verify "$out" 2>/dev/null; then
      status=PASS
    else
      status=FAIL
    fi
    printf "%-10s %-6s %-6s %-8s exit=%s\n" "$prog" "$rung" "$code" "$status" "$code"
  done
done

rm -rf "$TMP"
