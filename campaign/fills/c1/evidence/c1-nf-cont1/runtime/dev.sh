#!/usr/bin/env bash
# dev.sh part1 [part2 ...] : splice parts after line 704 of the base module into scratch/NFDev.lean
# and check it with lean_check_tree.sh (one Lean process).
set -u
source ~/.elan/env
cd /home/user/tcslib
BASE=scratch/NDNormalForm.base.lean
OUT=scratch/NFDev.lean
{ head -n 704 "$BASE"; for p in "$@"; do cat "$p"; done; tail -n +705 "$BASE"; } > "$OUT"
/usr/bin/time -f "wall=%e maxrss_kb=%M" bash scripts/lean_check_tree.sh scratch/NFDev 2>&1 | grep -v "^$" | head -${NLINES:-80}
