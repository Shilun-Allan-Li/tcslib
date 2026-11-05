#!/usr/bin/env bash
# Check the modules of an order list (from line $2, default 1) one at a time, logging each
# module's time and maximum memory; stop at the first failure.
ORDER="$1"; FROM="${2:-1}"
cd "$(dirname "$0")/../.." || exit 2
source ~/.elan/env
i=0
while read -r m; do
  i=$((i+1)); [ "$i" -lt "$FROM" ] && continue
  echo "=== [$i] $m"
  python3 evidence/runtime/timed.py bash scripts/lean_check_tree.sh "$m" || { echo "SWEEP STOPPED at [$i] $m"; exit 1; }
done < "$ORDER"
echo "SWEEP DONE"
