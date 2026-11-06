#!/usr/bin/env bash
# Resumable stop-at-first-failure replay: ladder.sh <worktree> <order-file> <log> [start-module]
# Checks modules in order with scripts/lean_check_tree.sh (one at a time); stops at the first failure.
set -u
WT="$1"; ORDER="$2"; LOG="$3"; START="${4:-}"
cd "$WT" || exit 2
export PATH="$HOME/.elan/bin:$PATH"
on=0; [ -z "$START" ] && on=1
while read -r m; do
  [ "$on" = 0 ] && { [ "$m" = "$START" ] && on=1 || continue; }
  t0=$(date +%s); out=$(mktemp)
  nice -n 10 bash scripts/lean_check_tree.sh "$m" > "$out" 2>&1; rc=$?
  echo "$m rc=$rc $(( $(date +%s)-t0 ))s errors=$(grep -c 'error:' "$out") sorry=$(grep -c "uses 'sorry'" "$out")" >> "$LOG"
  if [ $rc != 0 ]; then echo "---- FAIL output:" >> "$LOG"; grep -A12 "error:" "$out" | head -80 >> "$LOG"; echo "# stopped at $m" >> "$LOG"; rm -f "$out"; exit 1; fi
  rm -f "$out"
done < "$ORDER"
echo "# done $(date -u +%FT%TZ)" >> "$LOG"
