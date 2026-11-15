#!/usr/bin/env bash
# Run seals.py chunk after chunk until DONE or a failure (for nohup use; seals.py is resumable).
# usage: seals_loop.sh TAG ROOT RUNLOG FILE...
export PATH=$HOME/.elan/bin:$PATH
tag=$1; root=$2; runlog=$3; shift 3
while true; do
  out=$(python3 -I /workspace/sctools/seals.py "$tag" "$root" "$@" 2>&1 | tail -1)
  echo "$(date -u +%FT%TZ) $out" >> "$runlog"
  case "$out" in PAUSE*) ;; *) break ;; esac
done
