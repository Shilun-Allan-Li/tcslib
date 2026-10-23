#!/usr/bin/env bash
# elab.sh <worktree> <olean dir> <file> <out>: one elaboration through leanelab.sh, timed, exit recorded
WT="$1"; OL="$2"; F="$3"; OUT="$4"
s=$(date +%s)
bash /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/tools/leanelab.sh "$WT" "$OL" "$F" > "$OUT" 2>&1
st=$?
e=$(date +%s)
echo "# exit=$st wall=$((e-s))s file=$F olean=$(basename $OL) wt=$(basename $WT) head=$(git -C "$WT" rev-parse --short HEAD)" >> "$OUT"
echo "$(basename $OUT): exit=$st errors=$(grep -c ': error' "$OUT") warnings=$(grep -c ': warning' "$OUT") wall=$((e-s))s"
