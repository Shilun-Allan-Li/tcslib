#!/usr/bin/env bash
# run1.sh <oleans> <worktree> <file.lean> <out>: plain lean on a probe (no -o)
export PATH="$HOME/.elan/bin:$PATH"
OL=$1; ROOT=$2; LP=$OL
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"; cd $ROOT
s=$(date +%s); lean "$3" > "$4" 2>&1; rc=$?
echo "[rc=$rc time=$(( $(date +%s)-s ))s]" >> "$4"
