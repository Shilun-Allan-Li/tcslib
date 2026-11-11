#!/usr/bin/env bash
# One module check through scripts/lean_check_tree.sh, with start/end time and max RSS.
# Usage: check.sh <module path without .lean> <log file>
set -u
mod="$1"
log="$2"
source "$HOME/.elan/env"
cd /workspace/tcslib
{
  echo "=== $mod"
  echo "start $(date -u +%FT%TZ)"
  /usr/bin/time -f "time: elapsed=%e s, maxrss=%M KiB, exit=%x" bash scripts/lean_check_tree.sh "$mod"
  st=$?
  echo "end $(date -u +%FT%TZ) status=$st"
} >>"$log" 2>&1
tail -n 40 "$log" | sed -n "/=== ${mod//\//\\/}/,\$p" | grep -E "error|FAIL|status=|time:|sorry" | head -40
