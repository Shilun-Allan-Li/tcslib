#!/usr/bin/env bash
# ladder.sh <order-file> <logdir>: check each module in order with lean_check_tree.sh on dl-oleans-2, one at a time.
SP=$SP
export PATH=$HOME/.elan/bin:$PATH TCSLIB_OLEANS=$SP/dl-oleans-2
cd $SP/wt-stmt-pairings
mkdir -p $2
while read m; do
  p=${m//.//}; s=$(date +%s)
  bash scripts/lean_check_tree.sh $p > $2/${m}.log 2>&1; rc=$?
  echo "$m rc=$rc errors=$(grep -c 'error:' $2/${m}.log) sorry=$(grep -c "declaration uses 'sorry'" $2/${m}.log) secs=$(( $(date +%s)-s ))" >> $2/summary.txt
  [ $rc -ne 0 ] && exit $rc
done < $1
