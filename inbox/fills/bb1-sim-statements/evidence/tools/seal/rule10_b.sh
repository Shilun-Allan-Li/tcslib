#!/usr/bin/env bash
# rule10_b.sh (LE-gate29b: rule10.sh with runner_full.py: lean -DmaxErrors=0, no -o) <tools-used> <worktree> <evidence-dir> <probe-prefix> <head-rev> <mkctl.py> <dotted module>...
# After the collector run (<evidence>/rule10/probe-runs): strict (mkseals_ab) and coe (mkseals_coe) seals A and B
# (B with SEAL_EVAL=1), paired controls on the strict and coe records, one NOSTOP runner pass over all probes,
# sealsum per variant, ctlcheck2 per harness. Tree: $TCSLIB_OLEANS_TREE.
# bb1-sim-statements (lead, 2026-11-17): two changes, recorded here: the rule10 directory and the touched.json
# are read from $R10DIR and $TOUCHED when set (one directory per series); defaults unchanged.
set -eu
T=$1; W=$2; E=$3; P=$4; H=$5; CTL=$6; shift 6
G=$T/review/archived-gate10-tools; R=${R10DIR:-$E/rule10}; LOG=$R/probe-runs/mods/${P}_CollectHead.log
cd "$(dirname "$0")"
python3 -I $T/review/mkseals_ab.py $G $LOG $W $H $R/seals/A $P/S SealA_ "$@" > $R/mkseals-A.log
SEAL_EVAL=1 python3 -I $T/review/mkseals_ab.py $G $LOG $W $H $R/seals/B $P/S SealB_ "$@" > $R/mkseals-B.log
python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $R/seals-coe/A $P/C SealA_ "$@" > $R/mkseals-coe-A.log
SEAL_EVAL=1 python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $R/seals-coe/B $P/C SealB_ "$@" > $R/mkseals-coe-B.log
mkdir -p $R/seals-flat $R/seals-coe-flat
for v in A B; do
  for f in $R/seals/$v/Seal*.json; do cp $f $R/seals-flat/; done
  for f in $R/seals-coe/$v/Seal*.json; do cp $f $R/seals-coe-flat/; done
done
python3 -I $CTL $G $R/seals-flat $W $P/KS $R/controls-strict > $R/mkctl-strict.log
python3 -I $CTL $G $R/seals-coe-flat $W $P/K $R/controls-coe > $R/mkctl-coe.log
(cd $W && ls $P/C/*.lean $P/K/*.lean $P/KS/*.lean $P/S/*.lean 2>/dev/null | sed 's/\.lean$//' | LC_ALL=C sort) > $R/order/seal-control-queue.txt
python3 -I $T/runner_full.py $W $R/order/seal-control-queue.txt $TCSLIB_OLEANS_TREE $R/seal-runs > $R/seal-runner.out 2>&1 || true
TJ=${TOUCHED:-$E/statements/touched-after.json}
python3 -I $T/review/sealsum.py $R/seals/A $R/seal-runs $TJ $R/seals-A.tsv
python3 -I $T/review/sealsum.py $R/seals/B $R/seal-runs $TJ $R/seals-B.tsv
python3 -I $T/review/sealsum.py $R/seals-coe/A $R/seal-runs $TJ $R/seals-coe-A.tsv
python3 -I $T/review/sealsum.py $R/seals-coe/B $R/seal-runs $TJ $R/seals-coe-B.tsv
python3 -I $T/review/ctlcheck2.py $R/controls-strict/controls-plan.json $R/seal-runs $R/ctlcheck-strict.json > $R/ctlcheck-strict.log || true
python3 -I $T/review/ctlcheck2.py $R/controls-coe/controls-plan.json $R/seal-runs $R/ctlcheck-coe.json > $R/ctlcheck-coe.log || true
cat $R/mkseals-*.log $R/mkctl-*.log; cat $R/seals-*.tsv; for f in $R/ctlcheck-strict.log $R/ctlcheck-coe.log; do tail -n 1 $f; done
