#!/usr/bin/env bash
# usage: elab.sh <worktree> <olean dir> <file.lean relative to worktree> <out file>
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
W="$1"; O="$2"; F="$3"; OUT="$4"
t0=$(date +%s)
echo "# elab $F in $W against $O; start $(date -u +%FT%TZ); file sha256 $(shasum -a 256 "$W/$F" | cut -d' ' -f1)" > "$OUT"
bash $S/tools/leanelab.sh "$W" "$O" "$F" >> "$OUT" 2>&1
st=$?
t1=$(date +%s)
echo "# exit=$st elapsed=$((t1-t0))s end $(date -u +%FT%TZ)" >> "$OUT"
echo "# errors=$(grep -c ': error' "$OUT") warnings=$(grep -c ': warning' "$OUT")" >> "$OUT"
