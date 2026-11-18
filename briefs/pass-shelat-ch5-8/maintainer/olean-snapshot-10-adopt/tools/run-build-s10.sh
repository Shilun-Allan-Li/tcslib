#!/usr/bin/env bash
# run-build-s10.sh [queue] (#368 merge replay on snapshot #9): run-build-g50e.sh with only B and OUT re-pointed.
# Export wtx of R = merge-tree(523a00a6, 052e2b05) = d52cf05b (= cf6a2266^{tree}) on $SP/olean-replay-s10 (cp -al of snapshot #9),
# <queue> (default plan/queue.txt, imports-first) through the recipe's runner.py (unmodified), one
# module per call; slot gate before each module (wait while 3 or more lean processes run); stop if free disk < 1.5 GB.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
B=$SP/s10-work; OUT=$SP/olean-replay-s10; RUNNER=$SP/snaptools3/olean-advance-a6d01b1b/tools-used/runner.py
Q=${1:-$B/plan/queue.txt}; E=$B/build; WX=$B/wtx
export PATH=$HOME/.elan/bin:$PATH TMPDIR=$B/tmp
mkdir -p $E/one $B/tmp
echo "start $(date -u +%FT%TZ) queue $Q" >> $E/runner.start; df -m / | tail -1 >> $E/df-launch.txt
while read -r m; do
  while [ "$(pgrep -c -x lean)" -ge 3 ]; do echo "wait $(date -u +%FT%TZ) $(pgrep -c -x lean) lean" >> $E/slot-waits.txt; sleep 30; done
  echo "slot $(date -u +%FT%TZ) $(pgrep -c -x lean) lean before $m" >> $E/slot-log.txt
  echo "$m" > $E/one/order.txt
  python3 -I $RUNNER $WX $E/one/order.txt $OUT $E < /dev/null || { echo "runner FAIL $m $(date -u +%FT%TZ)" >> $E/runner.exit; exit 1; }
  avail=$(df -m / | tail -1 | awk '{print $4}'); [ "$avail" -lt 1536 ] && { echo "DISK LOW $avail MB after $m" >> $E/runner.exit; exit 2; }
done < $Q
echo "runner exit 0 $(date -u +%FT%TZ)" >> $E/runner.exit; df -m / | tail -1 >> $E/runner.exit
