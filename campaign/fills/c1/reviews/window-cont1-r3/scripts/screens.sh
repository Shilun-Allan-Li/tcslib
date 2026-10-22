#!/usr/bin/env bash
# The review's v3 screens, one at a time, each only when no other screen runs.
# usage: screens.sh <worktree> <out> [<worktree> <out> ...]
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
POP=$S/wt-hk/campaign/fills/c1/inputs/c1-fill-window-cont1/screen-population.txt
while [ $# -ge 2 ]; do
  wt="$1"; out="$2"; shift 2
  while pgrep -f copy-text-screen-v3 >/dev/null; do sleep 15; done
  t0=$(date +%s)
  ( cd "$wt" && nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' "$POP") > "$out" 2> "$out.err" ); st=$?
  echo "exit $st, $(( $(date +%s) - t0 )) s, $(date)" > "$out.status"
done
echo ALL DONE
