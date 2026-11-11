#!/usr/bin/env bash
# Sweep: check modules from a list in order, one at a time; stop at the first failure.
# Usage: sweep.sh <list file> <log file>
set -u
list="$1"; log="$2"
while read -r m; do
  [ -z "$m" ] && continue
  /workspace/s2b-tools/check.sh "$m" "$log" >/dev/null
  if ! tail -n 1 "$log" | grep -q "status=0"; then echo "SWEEP STOPPED at $m" >>"$log"; exit 1; fi
done < "$list"
echo "SWEEP COMPLETE $(date -u +%FT%TZ)" >>"$log"
