#!/usr/bin/env bash
# bootstrap.sh (bb1-sim-statements, lead): tree P (the probe, T4's order-final.txt at c90273fa in the probe
# worktree), then tree S (order.txt at the issue base in the lead clone). One Lean process at a time
# through runner.py's per-module flock.
set -u
D=/home/user/exch/s/inbox/fills/bb1-sim-statements
R=$D/evidence/tools/review/runner.py
T4O=/home/user/exch/s/inbox/fills/bb1-machine/evidence/build/order-final.txt
mkdir -p $D/evidence/build/bootstrap-P $D/evidence/build/bootstrap-S
git -C /home/user/fill/wt-probe rev-parse HEAD > $D/evidence/build/bootstrap-P/HEAD.txt
cp $T4O $D/evidence/build/bootstrap-P/order.txt
python3 -I $R /home/user/fill/wt-probe $D/evidence/build/bootstrap-P/order.txt /home/user/fill/treeP \
  $D/evidence/build/bootstrap-P > $D/evidence/build/bootstrap-P/runner.out 2>&1
echo "P exit $?" >> $D/evidence/build/bootstrap-P/runner.out
git -C /home/user/fill/tcslib rev-parse HEAD > $D/evidence/build/bootstrap-S/HEAD.txt
cp /home/user/exch/s/outbox/fills/bb1-sim-statements/order.txt $D/evidence/build/bootstrap-S/order.txt
python3 -I $R /home/user/fill/tcslib $D/evidence/build/bootstrap-S/order.txt /home/user/fill/treeS \
  $D/evidence/build/bootstrap-S > $D/evidence/build/bootstrap-S/runner.out 2>&1
echo "S exit $?" >> $D/evidence/build/bootstrap-S/runner.out
