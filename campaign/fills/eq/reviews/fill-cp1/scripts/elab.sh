#!/bin/bash
# usage: elab.sh <worktree> <olean dir> <file (relative to the worktree, or absolute)> <out prefix>
# One elaboration through tools/leanelab.sh (which throttles itself to 2 machine-wide).
start=$(date -u +%FT%TZ)
/usr/bin/time -l bash /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/tools/leanelab.sh "$1" "$2" "$3" > "$4.out" 2> "$4.time"
st=$?
echo "exit=$st start=$start end=$(date -u +%FT%TZ) wt=$1 oleans=$2 file=$3" >> "$4.time"
echo "exit=$st; $(grep -c ': error' "$4.out") errors; $(grep -c ': warning' "$4.out") warnings; $(grep -E ' real' "$4.time" | awk '{print $1}')s; maxrss $(grep 'maximum resident' "$4.time" | awk '{print $1}')"
