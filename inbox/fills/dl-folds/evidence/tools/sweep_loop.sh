#!/usr/bin/env bash
# Run sweep.py chunk after chunk until the order is done or a module fails (for nohup use).
# usage: sweep_loop.sh ORDER TSV LOGDIR RUNLOG
export PATH=$HOME/.elan/bin:$PATH
cd "$(dirname "$2")"
while true; do
  out=$(python3 /workspace/foldtools/sweep.py "$1" "$2" "$3" 2>&1 | tail -1)
  echo "$(date -u +%FT%TZ) $out" >> "$4"
  case "$out" in PAUSE*) ;; *) break ;; esac
done
