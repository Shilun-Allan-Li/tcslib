#!/usr/bin/env bash
# controls_r2_g40.sh <tree>: paired controls, attempt 2 (mkctl_g40.py with the sidImpl row restated through
# type_of%). Attempt 1's control sources, plans and ctlcheck results are kept in rule10/controls-attempt1/;
# its runs stay in rule10/seal-runs/. The regenerated controls (same chooser, same seal records) run in
# rule10/control-runs-r2/ with runner_full.py (lean -DmaxErrors=0, no -o), then ctlcheck2 per harness.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
TREE=$1; E=$SP/dl-review/gate40-le; W=$SP/wt-gate40; T=$E/tools; R=$E/rule10
G=$T/review/archived-gate10-tools; P=G40Probe
A1=$R/controls-attempt1; mkdir -p $A1
mv $R/controls-strict $R/controls-coe $R/mkctl-strict.log $R/mkctl-coe.log $R/ctlcheck-strict.json \
   $R/ctlcheck-coe.json $R/ctlcheck-strict.log $R/ctlcheck-coe.log $A1/
rm -f $W/$P/K/*.lean $W/$P/KS/*.lean
python3 -I $T/review/mkctl_g40.py $G $R/seals-flat $W $P/KS $R/controls-strict > $R/mkctl-strict.log
python3 -I $T/review/mkctl_g40.py $G $R/seals-coe-flat $W $P/K $R/controls-coe > $R/mkctl-coe.log
(cd $W && ls $P/K/*.lean $P/KS/*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $R/order/control-queue-r2.txt
python3 -I $T/runner_full.py $W $R/order/control-queue-r2.txt $TREE $R/control-runs-r2 > $R/control-runner-r2.out 2>&1
python3 -I $T/review/ctlcheck2.py $R/controls-strict/controls-plan.json $R/control-runs-r2 $R/ctlcheck-strict.json > $R/ctlcheck-strict.log || true
python3 -I $T/review/ctlcheck2.py $R/controls-coe/controls-plan.json $R/control-runs-r2 $R/ctlcheck-coe.json > $R/ctlcheck-coe.log || true
cat $R/mkctl-*.log; tail -n 1 $R/ctlcheck-strict.log $R/ctlcheck-coe.log
echo CONTROLS-R2-DONE
