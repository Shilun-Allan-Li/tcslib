#!/usr/bin/env bash
# ladder_g40.sh <tree> <worktree> <order-file> <logdir> <bkdir> <snapshot-pre>: back up each olean once
# (backup.py, hash checked against the snapshot), then check each module in order with the worktree's
# scripts/lean_check_tree.sh (TCSLIB_OLEANS=<tree>), one Lean process at a time; stop on failure.
# Error counts: both `error:` and `error(` forms.
T=$(dirname "$0")
export PATH=$HOME/.elan/bin:$PATH TCSLIB_OLEANS=$1
WT=$2; ORD=$3; LOG=$4; BK=$5; SNAP=$6; mkdir -p $LOG $BK
cd $WT || exit 9
while read -r m; do
  [ -z "$m" ] && continue
  python3 -I $T/backup.py $TCSLIB_OLEANS $BK $SNAP $m || exit 8
  p=${m//.//}; s=$(date +%s)
  bash scripts/lean_check_tree.sh $p > $LOG/$m.log 2>&1 & pid=$!
  echo "$pid $m" > $LOG/current.pid; wait $pid; rc=$?
  e1=$(grep -c 'error:' $LOG/$m.log); e2=$(grep -c 'error(' $LOG/$m.log)
  echo "$m rc=$rc error:=$e1 error(=$e2 sorry=$(grep -c "declaration uses 'sorry'" $LOG/$m.log) warnings=$(grep -c 'warning:' $LOG/$m.log) secs=$(( $(date +%s)-s ))" | tee -a $LOG/summary.txt
  [ $rc -ne 0 ] && exit $rc
done < $ORD
exit 0
