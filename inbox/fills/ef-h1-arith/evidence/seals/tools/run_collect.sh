#!/usr/bin/env bash
# run_collect.sh <worktree> <olean-tree> <outdir>: generate and run the candidate collector (no .olean is written).
set -u
WT="$1"; OL="$2"; OUT="$3"
TOOLS="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$OUT"
export PATH="$HOME/.elan/bin:$PATH"
LP="$OL"
for d in "$WT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"
python3 -I "$TOOLS/gen_collect.py" "$TOOLS/mods.txt" "$OUT" "$OUT/Collect.lean" || exit 2
cd "$WT" && lean "$OUT/Collect.lean" > "$OUT/collect.out" 2>&1
rc=$?
echo "collector rc=$rc"; grep -c "error" "$OUT/collect.out"; head -30 "$OUT/collect.out"
exit $rc
