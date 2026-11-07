#!/usr/bin/env bash
# run1.sh <file.lean> <out>: plain lean on a probe or sealed copy (no -o), against postland-oleans
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
export PATH="$HOME/.elan/bin:$PATH"
ROOT=$SP/wt-shared-s1; LP=$SP/postland-oleans
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"; cd $ROOT
s=$(date +%s); lean "$1" > "$2" 2>&1 & pid=$!; echo "$pid run1 $1" >> $SP/s1work/pids.txt; wait $pid; rc=$?
echo "[rc=$rc time=$(( $(date +%s)-s ))s]" >> "$2"
