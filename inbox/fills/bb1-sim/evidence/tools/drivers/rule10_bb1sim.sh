#!/usr/bin/env bash
# rule10_bb1sim.sh <series> <phase>... (bb1-sim, Claude lead, 2026-11-17): ADAPTED from bb1-sim-statements'
# drivers/rule10_stmt.sh. Changes: (1) series head (the check head in the lead clone, tree F; owners Games.Relational,
# IdentityBased.Defs, .BonehBoyen, .BonehBoyenSecurity and the five helpers BonehBoyenSecurity.{Lazy,Real,Coupling,
# Random,Chain}) and base (the four existing owners at the check base 7cfe2b1b in the worktree wt-base, tree B);
# (2) the touched and scan comparisons run against the check base; (3) the controls generator is mkctl_bb1sim.py;
# (4) evidence paths are this delivery's (evidence/rule10/<series>/, evidence/statements/, evidence/scan/<series>/);
# (5) the probe directory is Bb1sRule10/ (untracked). Every probe through runner_full.py (lean -DmaxErrors=0, no -o,
# per-probe flock on the host's one-Lean lock). One Lean process at a time.
# (6) (2026-11-17, the Lean-parallelism ruling) every probe runs through poolrun.py, and the seals phase through
# rule10_b_pool.sh: up to $POOL Lean processes host-wide, through the shared slot locks; the head and base series
# may run at the same time (distinct probe directories and output directories).
set -u
E=/home/user/exch/s/inbox/fills/bb1-sim/evidence; T=$E/tools/seal; G=$T/review/archived-gate10-tools
B=7cfe2b1b9a7e001d9ae972811cf85a332518111d
GM=TCSlib.Cryptography.Games; IM=TCSlib.Cryptography.AdvancedEncryption.IdentityBased
IF=TCSlib/Cryptography/AdvancedEncryption/IdentityBased
case $1 in
head) W=/home/user/fill/tcslib; TREE=/home/user/fill/treeF; NAME=head
      MODS="$GM.Relational $IM.Defs $IM.BonehBoyen $IM.BonehBoyenSecurity $IM.BonehBoyenSecurity.Lazy $IM.BonehBoyenSecurity.Real $IM.BonehBoyenSecurity.Coupling $IM.BonehBoyenSecurity.Random $IM.BonehBoyenSecurity.Chain"
      FILES="TCSlib/Cryptography/Games/Relational.lean $IF/Defs.lean $IF/BonehBoyen.lean $IF/BonehBoyenSecurity.lean $IF/BonehBoyenSecurity/Lazy.lean $IF/BonehBoyenSecurity/Real.lean $IF/BonehBoyenSecurity/Coupling.lean $IF/BonehBoyenSecurity/Random.lean $IF/BonehBoyenSecurity/Chain.lean";;
base) W=/home/user/fill/wt-base; TREE=/home/user/fill/treeB; NAME=base
      MODS="$GM.Relational $IM.Defs $IM.BonehBoyen $IM.BonehBoyenSecurity"
      FILES="TCSlib/Cryptography/Games/Relational.lean $IF/Defs.lean $IF/BonehBoyen.lean $IF/BonehBoyenSecurity.lean";;
esac
shift
H=$(git -C $W rev-parse HEAD)
R=$E/rule10/$NAME
TJ=$E/statements/touched-$NAME.json
export TCSLIB_OLEANS_TREE=$TREE TMPDIR=/home/user/fill/tmp
PP=Bb1sRule10
mkdir -p $R/order $R/probe-sources $W/$PP $E/statements $TMPDIR
for ph in "$@"; do
echo "phase $ph series $NAME start $(date -u +%FT%TZ) head $H"
case $ph in
touched)
  python3 -I $T/review/touched.py $W $B $H $TJ $FILES > $E/statements/touched-$NAME.tsv;;
collect)
  printf '%s\n' $MODS > $R/order/owners.txt
  python3 -I $T/review/mkcollect.py $T/review/NmCollect.template.lean $R/order/owners.txt "bb1-sim $NAME collector" $W/$PP/CollectHead.lean
  cp $W/$PP/CollectHead.lean $R/probe-sources/CollectHead.lean.txt
  printf "$PP/CollectHead\n" > $R/order/probes.txt
  python3 -I $T/poolrun.py $W $R/order/probes.txt $TREE $R/probe-runs > $R/probe-runner.out 2>&1; echo "collector rc=$?";;
pretest)
  LOG=$R/probe-runs/mods/${PP}_CollectHead.log; Q=$R/pretest
  mkdir -p $Q/seals-flat
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $Q/seals-coe/A $PP/QC SealA_ $MODS > $Q/mkseals-coe-A.log
  cp $Q/seals-coe/A/Seal*.json $Q/seals-flat/
  python3 -I $T/review/mkctl_bb1sim.py $G $Q/seals-flat $W $PP/QK $Q/controls > $Q/mkctl.log
  (cd $W && ls $PP/QK/ControlU_*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $Q/order.txt
  python3 -I $T/poolrun.py $W $Q/order.txt $TREE $Q/runs > $Q/runner.out 2>&1
  grep -h '"module"' $Q/runs/results.jsonl | python3 -I -c "import sys,json;[print(r['module'],r['rc'],r['errors']) for r in map(json.loads,sys.stdin)]" | tee $Q/summary.txt
  rm -rf $W/$PP/QC $W/$PP/QK;;
seals)
  R10DIR=$R TOUCHED=$TJ bash $T/rule10_b_pool.sh $T $W $E $PP $H $T/review/mkctl_bb1sim.py $MODS > $R/rule10-driver.out 2>&1; echo "rule10_b rc=$?";;
baseseals)
  LOG=$R/probe-runs/mods/${PP}_CollectHead.log
  python3 -I $T/review/mkseals_ab.py $G $LOG $W $H $R/seals/A $PP/ZS SealA_ $MODS > $R/mkseals-A.log
  SEAL_EVAL=1 python3 -I $T/review/mkseals_ab.py $G $LOG $W $H $R/seals/B $PP/ZS SealB_ $MODS > $R/mkseals-B.log
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $R/seals-coe/A $PP/ZC SealA_ $MODS > $R/mkseals-coe-A.log
  SEAL_EVAL=1 python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $R/seals-coe/B $PP/ZC SealB_ $MODS > $R/mkseals-coe-B.log
  (cd $W && ls $PP/ZS/*.lean $PP/ZC/*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $R/order/seals.txt
  python3 -I $T/poolrun.py $W $R/order/seals.txt $TREE $R/seal-runs > $R/seal-runner.out 2>&1
  for v in seals/A seals/B seals-coe/A seals-coe/B; do
    python3 -I $T/review/sealsum.py $R/$v $R/seal-runs $TJ $R/$(echo $v | tr / -).tsv; done;;
scan)
  S=$E/scan/$NAME; mkdir -p $S
  SF=$(git -C $W diff --name-only $B $H -- 'TCSlib/*.lean' | grep '/')
  echo $SF > $S/files.txt
  SCAN_IMPORTS="$MODS" python3 -I $T/scan1_g40.py $G/scan_explicit.py $W $TJ $S/items-head.json $W/$PP/ScanKindsHead.lean $SF > $S/scan1.out 2>&1
  cp $W/$PP/ScanKindsHead.lean $S/ScanKindsHead.lean.txt
  echo $PP/ScanKindsHead > $S/order.txt
  python3 -I $T/poolrun.py $W $S/order.txt $TREE $S/runs > $S/scan-runner.out 2>&1
  python3 -I $T/scan2.py $S/items-head.json $S/runs/mods/${PP}_ScanKindsHead.log $S/explicit-head.json > $S/scan2-head.log 2>&1; echo "scan2 rc=$?";;
esac
echo "phase $ph series $NAME done $(date -u +%FT%TZ)"
done
