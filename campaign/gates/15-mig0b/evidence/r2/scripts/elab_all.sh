#!/usr/bin/env bash
# Elaborate every *.check.lean of a directory in parallel (read-only; leanelab.sh only).
# Usage: elab_all.sh <S> <dir> <outdir>
S="$1"; DIR="$2"; OUTD="$3"; mkdir -p "$OUTD"
for f in "$DIR"/*.lean; do
  b=$(basename "$f")
  ( start=$(date +%s); bash "$S/tools/leanelab.sh" "$S/wt-r2m0b" "$S/oleans-f8" "$f" > "$OUTD/$b.out" 2>&1
    echo "exit $?" >> "$OUTD/$b.out"; echo "seconds $(( $(date +%s) - start ))" >> "$OUTD/$b.out" ) &
  while [ "$(jobs -r | wc -l)" -ge 10 ]; do sleep 1; done
done
wait
