#!/usr/bin/env bash
# Rebuild dev modules in order (one Lean process at a time), stopping at the first failure.
cd /home/user/tcslib
export PATH=$HOME/.elan/bin:$PATH
for m in "$@"; do
  out=$(python3 -I evidence/runtime/timed_check.py /home/user/tcslib evidence/dev/$m 2>&1)
  echo "$out" | grep -v "^$" | grep -v "declaration uses 'sorry'" | head -${LINES_SHOWN:-40}
  echo "$out" | grep -q "exit=0" || { echo "CHAIN STOPPED at $m"; exit 1; }
done
