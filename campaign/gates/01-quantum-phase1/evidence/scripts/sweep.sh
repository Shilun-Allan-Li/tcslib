#!/usr/bin/env bash
# Fresh sweep of the quantum-phase1 modules: delete each module's scratch olean, re-check it with
# scripts/lean_check_tree.sh (direct `lean`, never `lake build`), in dependency order.
# Fails on the first module that does not pass. Prints per-module sorry counts.
set -u
ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"; cd "$ROOT"
OL="${TCSLIB_OLEANS:-$ROOT/.lake/tcslib-check-oleans}"
total=0
while read -r m; do
  rm -f "$OL/$m.olean"
  out="$(bash scripts/lean_check_tree.sh "$m" 2>&1)"; rc=$?
  n="$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
  other="$(printf '%s\n' "$out" | grep -v "declaration uses 'sorry'" | grep -c -E 'warning|error')"
  echo "$m: exit=$rc sorry-warnings=$n other-diagnostics=$other"
  [ "$rc" -eq 0 ] || { printf '%s\n' "$out"; exit 1; }
  total=$((total + n))
done < "$(dirname "$0")/module_order.txt"
echo "TOTAL sorry-warnings=$total"
