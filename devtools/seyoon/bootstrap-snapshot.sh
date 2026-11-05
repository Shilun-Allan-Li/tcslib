#!/usr/bin/env bash
# bootstrap-snapshot.sh <worktree dir> <snapshot name> [--resume]
# Build a fresh olean snapshot of a worktree's Lean tree, for a session that has none (a new
# machine or cloud VM). It compiles every module under the snapshot set (TCSlib/Complexity,
# TCSlib/BooleanAnalysis, TCSlib/Programs, TCSlib/ComputationalModels; never the root TCSlib) in
# dependency order, one at a time, through scripts/lean_check_tree.sh (no `lake build`), into
# $TCSLIB_SCRATCH/<snapshot name>. Mathlib's oleans must already be in the worktree's
# .lake/packages (`lake exe cache get`, with Mathlib's cache hosts reachable). The log records
# the commit, each module's exit status, error and sorry counts, and the total; a failure stops
# the build. Record the snapshot with the commit it matches (the log's first line).
#
# --resume continues a bootstrap that was killed (a cloud worker restart ends every process):
# the run must not have failed or finished, the worktree's Lean tree (`TCSlib/`, `TCSlib.lean`)
# must be clean and equal to the log's commit's, the order list must be unchanged, the modules
# logged `exit=0` must be exactly a prefix of it with non-empty oleans, and the run continues
# from the first module not logged (a killed module leaves no line), appending to the same log.
set -u
S="${TCSLIB_SCRATCH:-$HOME/.tcslib-scratch}"; WT=$S/$1; NAME=$2; O=$S/$NAME; MODE=${3:-}
T="$(cd "$(dirname "$0")" && pwd)"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "no Mathlib build in $WT/.lake/packages" >&2; exit 2; }
mkdir -p "$S/fills/replay"; LIST=$S/fills/replay/order-$NAME.txt; LOG=$S/fills/replay/bootstrap-$NAME.log
case "$MODE" in
  "") [ -e "$O" ] && { echo "$O exists; choose a new name, or --resume" >&2; exit 2; }
      python3 -I "$T/bootstrap_order.py" "$WT" > "$LIST" || exit 2
      : > "$LOG"; DONE=0 ;;
  --resume)
      [ -d "$O" ] && [ -f "$LOG" ] && [ -f "$LIST" ] || { echo "nothing to resume for $NAME" >&2; exit 2; }
      grep -q '^# stopped' "$LOG" && { echo "$NAME failed (see $LOG); start a new snapshot" >&2; exit 2; }
      grep -q '^# modules=' "$LOG" && { echo "$NAME is complete"; tail -1 "$LOG"; exit 0; }
      C0=$(head -1 "$LOG" | sed -n 's/^# bootstrap [^ ]* at \([0-9a-f]\{40\}\) .*/\1/p')
      [ -n "$C0" ] || { echo "no commit on the log's first line" >&2; exit 2; }
      for p in TCSlib TCSlib.lean; do
        [ "$(git -C "$WT" rev-parse "$C0:$p")" = "$(git -C "$WT" rev-parse "HEAD:$p")" ] \
          || { echo "$p at HEAD differs from $C0" >&2; exit 2; }
      done
      [ -z "$(git -C "$WT" status --porcelain -- TCSlib TCSlib.lean)" ] || { echo "uncommitted Lean changes in $WT" >&2; exit 2; }
      python3 -I "$T/bootstrap_order.py" "$WT" | cmp -s - "$LIST" || { echo "the order list changed" >&2; exit 2; }
      DONE=$(grep -c ' exit=0 errors=' "$LOG")
      [ "$(grep ' exit=0 errors=' "$LOG" | cut -d' ' -f1)" = "$(head -n "$DONE" "$LIST")" ] \
        || { echo "the logged modules are not a prefix of the order list" >&2; exit 2; }
      while read -r m; do [ -s "$O/$m.olean" ] || { echo "missing olean for logged $m" >&2; exit 2; }; done < <(head -n "$DONE" "$LIST")
      ;;
  *) echo "unknown option $MODE" >&2; exit 2 ;;
esac
cd "$WT" || exit 1
{ if [ "$DONE" -eq 0 ]; then
    echo "# bootstrap $NAME at $(git rev-parse HEAD) ($(wc -l < "$LIST" | tr -d ' ') modules); $(date)"
  else
    echo "# resumed after $DONE modules, at $(git rev-parse HEAD) (same Lean tree); $(date)"
  fi
  n=$DONE
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$O nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    echo "$m exit=$st errors=$(printf '%s\n' "$out" | grep -c "error") sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { printf '%s\n' "$out" | grep error | head -5; echo "# stopped at $n"; exit 1; }
  done < <(tail -n +"$((DONE+1))" "$LIST")
  echo "# modules=$n failed=0; $(date)"; } >> "$LOG" 2>&1
tail -1 "$LOG"
