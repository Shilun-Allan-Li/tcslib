#!/usr/bin/env bash
# Foreground sweep in chunks: check modules of <list> in order, resuming after the index stored in
# <state>, until <budget> seconds have elapsed; stop at the first failure.
# Usage: sweep_chunk.sh <list> <log> <state> <budget-seconds>
set -u
list="$1"; log="$2"; state="$3"; budget="$4"
start=$(date +%s)
idx=$(cat "$state" 2>/dev/null || echo 0)
total=$(grep -c . "$list")
while [ "$idx" -lt "$total" ]; do
  now=$(date +%s)
  if [ $((now - start)) -ge "$budget" ]; then echo "chunk paused at $idx/$total"; exit 0; fi
  m=$(sed -n "$((idx + 1))p" "$list")
  /workspace/ett-tools/check.sh "$m" "$log"
  if ! tail -n 1 "$log" | grep -q "status=0"; then echo "SWEEP STOPPED at $m" | tee -a "$log"; exit 1; fi
  idx=$((idx + 1)); echo "$idx" > "$state"
done
echo "SWEEP COMPLETE $(date -u +%FT%TZ)" | tee -a "$log"
