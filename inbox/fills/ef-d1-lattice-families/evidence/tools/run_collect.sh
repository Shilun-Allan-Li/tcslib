# EF-D1 copy of gates/04-s2b/evidence-r5/tools/run_collect.sh; only change: ${MODS:-$TOOLS/mods.txt} lets the caller name the module list.
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
python3 -I "$TOOLS/gen_collect.py" "${MODS:-$TOOLS/mods.txt}" "$OUT" "$OUT/Collect.lean" || exit 2
cd "$WT" && lean "$OUT/Collect.lean" > "$OUT/collect.out" 2>&1
rc=$?
echo "collector rc=$rc"; grep -c "error" "$OUT/collect.out"; head -30 "$OUT/collect.out"
exit $rc
