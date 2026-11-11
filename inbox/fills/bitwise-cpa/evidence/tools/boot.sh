#!/usr/bin/env bash
# Bootstrap: the upstream closure of PublicKey/BitwiseCPA, in the order list's order, one module at a time.
cd /home/user/fill
LOG=evidence/logs/bootstrap.log
echo "bootstrap start $(date -u +%FT%TZ) base $(git rev-parse --short HEAD)" >> $LOG
n=0
while read -r m; do
  /tmp/claude-0/bw/chk.sh "$m" $LOG > /dev/null || { echo "BOOTSTRAP FAIL $m" >> $LOG; exit 1; }
  n=$((n+1))
done < evidence/logs/bootstrap-closure.txt
echo "bootstrap end $(date -u +%FT%TZ): $n modules passed" >> $LOG
