#!/usr/bin/env bash
# Check each module of an order list (or its tail from a given module) in order, one at a time,
# through scripts/lean_check_tree.sh via timed_check.py; stop at the first failing module.
# Usage: sweep.sh <order-list> [first-module]
set -u
ROOT=/home/user/tcslib
export PATH=$HOME/.elan/bin:$PATH
ORDER="$1"; FROM="${2:-}"
started=0; [ -z "$FROM" ] && started=1
echo "SWEEP start=$(date -u +%FT%TZ) order=$ORDER from=${FROM:-<first>} base=$(git -C $ROOT rev-parse HEAD)"
n=0
while read -r m; do
  [ -z "$m" ] && continue
  [ "$started" = 0 ] && [ "$m" = "$FROM" ] && started=1
  [ "$started" = 0 ] && continue
  n=$((n+1))
  echo "=== [$n] $m"
  python3 -I $ROOT/evidence/runtime/timed_check.py $ROOT "$m" || { echo "SWEEP FAILED at $m end=$(date -u +%FT%TZ)"; exit 1; }
done < "$ORDER"
echo "SWEEP OK modules=$n end=$(date -u +%FT%TZ)"
