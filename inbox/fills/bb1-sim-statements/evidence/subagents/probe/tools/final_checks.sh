#!/usr/bin/env bash
# final_checks.sh: the probe's recorded checks, in order (sub-agent probe, bb1-sim-statements).
# 1 native readers (runner.py, olean into tree P); 2 native consumer (runner.py); 3-4 devseal A/B
# of the consumer (runner_full.py, -DmaxErrors=0, no -o); 5 axioms module (runner_full.py).
set -u
E=/home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/subagents/probe
T=/home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/tools
WT=/home/user/fill/wt-probe; P=/home/user/fill/treeP
mkdir -p $E/orders
echo PlProbe/BB1SimReaders > $E/orders/readers.txt
echo PlProbe/BB1SimStepM > $E/orders/stepm.txt
echo PlProbe/Sealed/BB1SimStepM_A > $E/orders/stepm-A.txt
echo PlProbe/Sealed/BB1SimStepM_B > $E/orders/stepm-B.txt
echo PlProbe/BB1SimAxioms > $E/orders/axioms.txt
for d in native-readers native-stepm devseal-A devseal-B axioms; do rm -rf $E/$d; done
python3 -I $T/review/runner.py $WT $E/orders/readers.txt $P $E/native-readers || exit 1
python3 -I $T/review/runner.py $WT $E/orders/stepm.txt $P $E/native-stepm || exit 1
python3 -I $E/tools/devseal.py $WT/PlProbe/BB1SimStepM.lean $WT/PlProbe/Sealed/BB1SimStepM_A.lean A
python3 -I $E/tools/devseal.py $WT/PlProbe/BB1SimStepM.lean $WT/PlProbe/Sealed/BB1SimStepM_B.lean B
python3 -I $T/seal/runner_full.py $WT $E/orders/stepm-A.txt $P $E/devseal-A
python3 -I $T/seal/runner_full.py $WT $E/orders/stepm-B.txt $P $E/devseal-B
python3 -I $T/seal/runner_full.py $WT $E/orders/axioms.txt $P $E/axioms
