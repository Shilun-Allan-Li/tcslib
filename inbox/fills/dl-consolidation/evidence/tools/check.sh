#!/usr/bin/env bash
# One module check through scripts/lean_check_tree.sh in $WT (default /workspace/dlc), with start/end time and max RSS.
# Usage: check.sh <module path without .lean> <log file>
set -u
mod="$1"; log="$2"
source "$HOME/.elan/env"
cd "${WT:-/workspace/dlc}"
{
  echo "=== $mod"
  echo "start $(date -u +%FT%TZ)"
  /usr/bin/time -f "time: elapsed=%e s, maxrss=%M KiB, exit=%x" bash scripts/lean_check_tree.sh "$mod"
  st=$?
  echo "end $(date -u +%FT%TZ) status=$st"
} >>"$log" 2>&1
