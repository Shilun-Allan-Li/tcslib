#!/usr/bin/env bash
# Full sweep: every module of the extended order list, one lean_check_tree.sh call at a time.
cd /home/user/fill
ORDER=evidence/logs/order-new.txt; LOG=evidence/logs/sweep.log
: > $LOG
echo "sweep start $(date -u +%FT%TZ) proof-branch $(git rev-parse --short HEAD)" >> $LOG
pass=0; fail=0
while read -r m; do
  /tmp/claude-0/pk/chk.sh "$m" $LOG > /dev/null
  if tail -n 1 $LOG | grep -q " status 0$"; then pass=$((pass+1)); else fail=$((fail+1)); echo "SWEEP FAIL $m" >> $LOG; fi
done < $ORDER
echo "sweep end $(date -u +%FT%TZ): $pass passed, $fail failed" >> $LOG
