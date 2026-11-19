#!/usr/bin/env bash
# Scratch compile of a standalone file against the worktree's check oleans (no -o).
set -u
source "$HOME/.elan/env"
ROOT=/workspace/u1416
OL="$ROOT/.lake/tcslib-check-oleans"
LP="$OL"
[ -d "$ROOT/.lake/build/lib/lean" ] && LP="$LP:$ROOT/.lake/build/lib/lean"
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"
cd "$ROOT"
/usr/bin/time -f "time: elapsed=%e s, maxrss=%M KiB, exit=%x" lean "$1" 2>&1
