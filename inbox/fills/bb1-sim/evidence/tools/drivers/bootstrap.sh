#!/usr/bin/env bash
# bootstrap.sh (bb1-sim, lead): tree F = order.txt (193 modules) at the check base 7cfe2b1b in the lead clone,
# one Lean process at a time through runner.py's per-module flock.
set -u
D=/home/user/exch/s/inbox/fills/bb1-sim
R=$D/evidence/tools/review/runner.py
B=$D/evidence/build/bootstrap
mkdir -p $B
git -C /home/user/fill/tcslib rev-parse HEAD > $B/HEAD.txt
cp /home/user/exch/s/outbox/fills/bb1-sim/order.txt $B/order.txt
python3 -I $R /home/user/fill/tcslib $B/order.txt /home/user/fill/treeF $B > $B/runner.out 2>&1
echo "F exit $?" >> $B/runner.out
