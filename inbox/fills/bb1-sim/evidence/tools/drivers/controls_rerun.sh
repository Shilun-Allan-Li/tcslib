#!/usr/bin/env bash
# controls_rerun.sh (bb1-sim, lead): attempt 2 of the head series' paired controls, after fixing three rows of
# mkctl_bb1sim.py (its header). The seal records are those of the head seal run (rule10/head/seals-flat,
# seals-coe-flat; the seals are not rerun). The control probes are regenerated as in rule10_b.sh, run through
# poolrun.py (pool 3) into rule10/head/control-runs/, and checked with ctlcheck2.py. Attempt 1 is kept in
# rule10/head/controls-attempt1/.
set -u
E=/home/user/exch/s/inbox/fills/bb1-sim/evidence; T=$E/tools/seal; G=$T/review/archived-gate10-tools; R=$E/rule10/head
W=/home/user/fill/tcslib; P=Bb1sRule10; export POOL=3
rm -rf $W/$P/K $W/$P/KS $R/control-runs
python3 -I $T/review/mkctl_bb1sim.py $G $R/seals-flat $W $P/KS $R/controls-strict > $R/mkctl-strict.log
python3 -I $T/review/mkctl_bb1sim.py $G $R/seals-coe-flat $W $P/K $R/controls-coe > $R/mkctl-coe.log
(cd $W && ls $P/K/*.lean $P/KS/*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $R/order/control-queue-attempt2.txt
python3 -I $T/poolrun.py $W $R/order/control-queue-attempt2.txt /home/user/fill/treeF $R/control-runs > $R/control-runner.out 2>&1
python3 -I $T/review/ctlcheck2.py $R/controls-strict/controls-plan.json $R/control-runs $R/ctlcheck-strict.json > $R/ctlcheck-strict.log
python3 -I $T/review/ctlcheck2.py $R/controls-coe/controls-plan.json $R/control-runs $R/ctlcheck-coe.json > $R/ctlcheck-coe.log
tail -n 1 $R/ctlcheck-strict.log $R/ctlcheck-coe.log; cat $R/mkctl-strict.log $R/mkctl-coe.log | grep -v chosen
