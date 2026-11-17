#!/usr/bin/env bash
# rule10_stmt.sh <series> <phase>... (bb1-sim-statements, Claude lead, 2026-11-17): ADAPTED from the bb1-machine
# delivery's drivers/rule10_final.sh. Changes: (1) series s1 (stmt/games-relational: owners Games.Relational, Games.Probability;
# tree S1), s2 (stmt/pairing-group-helpers: owner Pairing.Group, plus Pairing.Assumptions sealed as the CONTROL CARRIER
# only, the smallest consumer of Group whose request set contains Group's definitions BilinearGen.inst and desc; tree S2)
# and base (Games.Probability and Pairing.Group at the issue base bdcadd85, the lead clone, tree S); (2) one rule10 dir
# per series (evidence/rule10/<series-name>/, rule10-base/) and touched.json per series (evidence/statements/);
# (3) controls generator mkctl_bb1s.py; (4) the collector runs per series (the base has its own collector at the base);
# (5) the scan covers the series' changed Lean files against the base (attempt 2 of the s1 scan: the facade Games.lean added
# to s1's touched files; attempt 1 stopped in scan1 with KeyError for it, log kept as scan/games-relational-attempt1/). Every probe through runner_full.py
# (lean -DmaxErrors=0, no -o, per-probe flock on the host's one-Lean lock). One Lean process at a time.
set -u
E=/home/user/exch/s/inbox/fills/bb1-sim-statements/evidence; T=$E/tools/seal; G=$T/review/archived-gate10-tools
B=bdcadd858cbe043e8c41e465a96e81feb1eecda1
GM=TCSlib.Cryptography.Games; PM=TCSlib.Cryptography.Pairing
case $1 in
s1) W=/home/user/fill/wt-s1; TREE=/home/user/fill/treeS1; NAME=games-relational; MODS="$GM.Relational $GM.Probability"
    FILES="TCSlib/Cryptography/Games/Relational.lean TCSlib/Cryptography/Games/Probability.lean TCSlib/Cryptography/Games.lean";;
s2) W=/home/user/fill/wt-s2; TREE=/home/user/fill/treeS2; NAME=group-helpers; MODS="$PM.Group $PM.Assumptions"
    FILES="TCSlib/Cryptography/Pairing/Group.lean TCSlib/Cryptography/Pairing/Assumptions.lean";;
base) W=/home/user/fill/tcslib; TREE=/home/user/fill/treeS; NAME=base; MODS="$GM.Probability $PM.Group"
    FILES="TCSlib/Cryptography/Games/Probability.lean TCSlib/Cryptography/Pairing/Group.lean";;
esac
shift
H=$(git -C $W rev-parse HEAD)
if [ $NAME = base ]; then R=$E/rule10-base; else R=$E/rule10/$NAME; fi
TJ=$E/statements/touched-$NAME.json
export TCSLIB_OLEANS_TREE=$TREE TMPDIR=/home/user/fill/tmp
PP=StmtSeal
mkdir -p $R/order $R/probe-sources $W/$PP $E/statements
for ph in "$@"; do
echo "phase $ph series $NAME start $(date -u +%FT%TZ) head $H"
case $ph in
touched)
  python3 -I $T/review/touched.py $W $B $H $TJ $FILES > $E/statements/touched-$NAME.tsv;;
collect)
  printf '%s\n' $MODS > $R/order/owners.txt
  python3 -I $T/review/mkcollect.py $T/review/NmCollect.template.lean $R/order/owners.txt "bb1-sim-statements $NAME collector" $W/$PP/CollectHead.lean
  cp $W/$PP/CollectHead.lean $R/probe-sources/CollectHead.lean.txt
  printf "$PP/CollectHead\n" > $R/order/probes.txt
  python3 -I $T/runner_full.py $W $R/order/probes.txt $TREE $R/probe-runs > $R/probe-runner.out 2>&1; echo "collector rc=$?";;
pretest)
  LOG=$R/probe-runs/mods/${PP}_CollectHead.log; Q=$R/pretest
  mkdir -p $Q/seals-flat
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $Q/seals-coe/A $PP/QC SealA_ $MODS > $Q/mkseals-coe-A.log
  cp $Q/seals-coe/A/Seal*.json $Q/seals-flat/
  python3 -I $T/review/mkctl_bb1s.py $G $Q/seals-flat $W $PP/QK $Q/controls > $Q/mkctl.log
  (cd $W && ls $PP/QK/ControlU_*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $Q/order.txt
  python3 -I $T/runner_full.py $W $Q/order.txt $TREE $Q/runs > $Q/runner.out 2>&1
  grep -h '"module"' $Q/runs/results.jsonl | python3 -I -c "import sys,json;[print(r['module'],r['rc'],r['errors']) for r in map(json.loads,sys.stdin)]" | tee $Q/summary.txt
  rm -rf $W/$PP/QC $W/$PP/QK;;
seals)
  R10DIR=$R TOUCHED=$TJ bash $T/rule10_b.sh $T $W $E $PP $H $T/review/mkctl_bb1s.py $MODS > $R/rule10-driver.out 2>&1; echo "rule10_b rc=$?";;
baseseals)
  LOG=$R/probe-runs/mods/${PP}_CollectHead.log
  python3 -I $T/review/mkseals_ab.py $G $LOG $W $H $R/seals/A $PP/ZS SealA_ $MODS > $R/mkseals-A.log
  SEAL_EVAL=1 python3 -I $T/review/mkseals_ab.py $G $LOG $W $H $R/seals/B $PP/ZS SealB_ $MODS > $R/mkseals-B.log
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $R/seals-coe/A $PP/ZC SealA_ $MODS > $R/mkseals-coe-A.log
  SEAL_EVAL=1 python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $R/seals-coe/B $PP/ZC SealB_ $MODS > $R/mkseals-coe-B.log
  (cd $W && ls $PP/ZS/*.lean $PP/ZC/*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $R/order/seals.txt
  python3 -I $T/runner_full.py $W $R/order/seals.txt $TREE $R/seal-runs > $R/seal-runner.out 2>&1
  for v in seals/A seals/B seals-coe/A seals-coe/B; do
    python3 -I $T/review/sealsum.py $R/$v $R/seal-runs $TJ $R/$(echo $v | tr / -).tsv; done;;
scan)
  S=$E/scan/$NAME; mkdir -p $S
  SF=$(git -C $W diff --name-only $B $H -- 'TCSlib/*.lean' | grep '/')
  echo $SF > $S/files.txt
  SCAN_IMPORTS="$MODS" python3 -I $T/scan1_g40.py $G/scan_explicit.py $W $TJ $S/items-head.json $W/$PP/ScanKindsHead.lean $SF > $S/scan1.out 2>&1
  cp $W/$PP/ScanKindsHead.lean $S/ScanKindsHead.lean.txt
  echo $PP/ScanKindsHead > $S/order.txt
  python3 -I $T/runner_full.py $W $S/order.txt $TREE $S/runs > $S/scan-runner.out 2>&1
  python3 -I $T/scan2.py $S/items-head.json $S/runs/mods/${PP}_ScanKindsHead.log $S/explicit-head.json > $S/scan2-head.log 2>&1; echo "scan2 rc=$?";;
esac
echo "phase $ph series $NAME done $(date -u +%FT%TZ)"
done
