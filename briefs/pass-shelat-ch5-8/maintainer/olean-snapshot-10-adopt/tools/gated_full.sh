#!/usr/bin/env bash
# gated_full.sh <worktree> <order> <tree> <logdir> (LE-g45): runs phase 2's runner_full.py (unmodified; lean -DmaxErrors=0,
# no -o) one probe per call; before each probe it checks the host's Lean slot count and waits (30 s poll) while 3 or more
# lean processes run. Each slot reading goes to <logdir>/slot-log.txt.
set -u
W=$1; O=$2; TREE=$3; L=$4; SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
mkdir -p $L/one
while read -r m; do
  [ -z "$m" ] && continue
  while [ "$(pgrep -c -x lean)" -ge 3 ]; do echo "wait $(date -u +%FT%TZ) $(pgrep -c -x lean) lean" >> $L/slot-waits.txt; sleep 30; done
  echo "slot $(date -u +%FT%TZ) $(pgrep -c -x lean) lean before $m" >> $L/slot-log.txt
  echo "$m" > $L/one/order.txt
  python3 -I $SP/g6a-p2/tools/seal/runner_full.py $W $L/one/order.txt $TREE $L < /dev/null
done < $O
