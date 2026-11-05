#!/usr/bin/env bash
# bootstrap-snapshot.sh <worktree dir> <snapshot name>
# Build a fresh olean snapshot of a worktree's Lean tree, for a session that has none (a new
# machine or cloud VM). It compiles every module under the snapshot set (TCSlib/Complexity,
# TCSlib/BooleanAnalysis, TCSlib/Programs, TCSlib/ComputationalModels; never the root TCSlib) in
# dependency order, one at a time, through scripts/lean_check_tree.sh (no `lake build`), into
# $TCSLIB_SCRATCH/<snapshot name>. Mathlib's oleans must already be in the worktree's
# .lake/packages (`lake exe cache get`, with Mathlib's cache hosts reachable). The log records
# the commit, each module's exit status, error and sorry counts, and the total; a failure stops
# the build. Record the snapshot with the commit it matches (the log's first line).
set -u
S="${TCSLIB_SCRATCH:-$HOME/.tcslib-scratch}"; WT=$S/$1; NAME=$2; O=$S/$NAME
T="$(cd "$(dirname "$0")" && pwd)"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "no Mathlib build in $WT/.lake/packages" >&2; exit 2; }
[ -e "$O" ] && { echo "$O exists; choose a new name" >&2; exit 2; }
mkdir -p "$S/fills/replay"; LIST=$S/fills/replay/order-$NAME.txt; LOG=$S/fills/replay/bootstrap-$NAME.log
python3 -I "$T/bootstrap_order.py" "$WT" > "$LIST" || exit 2
cd "$WT" || exit 1
{ echo "# bootstrap $NAME at $(git rev-parse HEAD) ($(wc -l < "$LIST" | tr -d ' ') modules); $(date)"
  n=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$O nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    echo "$m exit=$st errors=$(printf '%s\n' "$out" | grep -c "error") sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { printf '%s\n' "$out" | grep error | head -5; echo "# stopped at $n"; exit 1; }
  done < "$LIST"
  echo "# modules=$n failed=0; $(date)"; } > "$LOG" 2>&1
tail -1 "$LOG"
