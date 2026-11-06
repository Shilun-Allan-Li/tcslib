#!/usr/bin/env bash
# replay.sh <worktree> <olean tree> <order.txt> <log> <header>: check each module of order.txt in
# order with scripts/lean_check_tree.sh into the tree; stop at the first failure.
set -u
export PATH="$HOME/.elan/bin:$PATH"
WT=$1; OL=$2; ORD=$3; LOG=$4
echo "# $5" > $LOG
cd $WT
while read -r m; do
  [ -z "$m" ] && continue
  t0=$(date +%s)
  out=$(TCSLIB_OLEANS=$OL bash scripts/lean_check_tree.sh "$m" 2>&1); rc=$?
  t1=$(date +%s)
  e=$(printf '%s\n' "$out" | grep -c 'error:'); s=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")
  echo "$m rc=$rc $((t1-t0))s errors=$e sorry=$s" >> $LOG
  if [ $rc -ne 0 ]; then printf '%s\n' "$out" | grep -A6 'error:' | head -60 >> $LOG; echo "# stopped" >> $LOG; exit 1; fi
done < $ORD
echo "# done" >> $LOG
