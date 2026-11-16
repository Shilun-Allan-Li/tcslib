#!/usr/bin/env bash
# rule10_final.sh <phase...> (fill bb1-machine, Claude lead, 2026-11-16): ADAPTED from the checkpoint's
# drivers/rule10_bb1m.sh (fill-pair-bdh's rule10_pbdh.sh, LE-gate40 lineage). Changes: (1) host paths: worktree
# W=/home/user/fill/tcslib (the lead clone), olean tree /home/user/fill/oleans, evidence E=<this delivery>/evidence,
# TMPDIR /home/user/fill/tmp; (2) owners: the eight changed owners Defs, BonehBoyen, Draws, Words, Handler,
# Reduction, Oracles (new helper), BonehBoyenMachine; (3) controls generator mkctl_bb1m_readers.py (mkctl_bb1m.py
# plus the seven reader rows); (4) new phases: `pretest` (the unsealed controls only, before the seal run),
# `baseseals` (strict and coe A/B of Defs and BonehBoyen at the issue base 7c0a55e0); (5) the scan covers the files
# changed against #331's head 9e7a9648. Every probe through runner_full.py (lean -DmaxErrors=0, no -o, per-probe
# flock on the host's one-Lean lock). One Lean process at a time.
set -u
W=/home/user/fill/tcslib; TREE=/home/user/fill/oleans
E=/home/user/exch/x/inbox/fills/bb1-machine/evidence; T=$E/tools/seal; R=$E/rule10
B=9e7a96481785d6cac4dea3b2e990c49ac278b060; I=7c0a55e0239c14786612d0cd4462e64238543ca1
H=$(git -C $W rev-parse HEAD)
export TCSLIB_OLEANS_TREE=$TREE TMPDIR=/home/user/fill/tmp
P=TCSlib.Cryptography.AdvancedEncryption.IdentityBased
MODS="$P.Defs $P.BonehBoyen $P.BonehBoyenMachine.Draws $P.BonehBoyenMachine.Words $P.BonehBoyenMachine.Handler $P.BonehBoyenMachine.Reduction $P.BonehBoyenMachine.Oracles $P.BonehBoyenMachine"
G=$T/review/archived-gate10-tools
mkdir -p $R/order $R/probe-sources $E/scan $W/Bb1mProbe
for ph in "$@"; do
echo "phase $ph start $(date -u +%FT%TZ) head $H"
case $ph in
collect)
  printf '%s\n' $MODS > $R/order/owners.txt
  python3 -I $T/review/mkcollect.py $T/review/NmCollect.template.lean $R/order/owners.txt "fill-bb1-machine final collector" $W/Bb1mProbe/CollectHead.lean
  cp $W/Bb1mProbe/CollectHead.lean $R/probe-sources/CollectHead.lean.txt
  printf 'Bb1mProbe/CollectHead\n' > $R/order/probes.txt
  python3 -I $T/runner_full.py $W $R/order/probes.txt $TREE $R/probe-runs > $R/probe-runner.out 2>&1; echo "collector rc=$?";;
pretest)
  LOG=$R/probe-runs/mods/Bb1mProbe_CollectHead.log; Q=$R/pretest
  mkdir -p $Q/seals-flat
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $H $Q/seals-coe/A Bb1mProbe/QC SealA_ $MODS > $Q/mkseals-coe-A.log
  cp $Q/seals-coe/A/Seal*.json $Q/seals-flat/
  python3 -I $T/review/mkctl_bb1m_readers.py $G $Q/seals-flat $W Bb1mProbe/QK $Q/controls > $Q/mkctl.log
  (cd $W && ls Bb1mProbe/QK/ControlU_*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $Q/order.txt
  python3 -I $T/runner_full.py $W $Q/order.txt $TREE $Q/runs > $Q/runner.out 2>&1
  grep -h '"module"' $Q/runs/results.jsonl | python3 -I -c "import sys,json;[print(r['module'],r['rc'],r['errors']) for r in map(json.loads,sys.stdin)]" | tee $Q/summary.txt
  rm -rf $W/Bb1mProbe/QC $W/Bb1mProbe/QK;;
seals)
  bash $T/rule10_b.sh $T $W $E Bb1mProbe $H $T/review/mkctl_bb1m_readers.py $MODS > $R/rule10-driver.out 2>&1; echo "rule10_b rc=$?";;
baseseals)
  # Defs and BonehBoyen at the issue base: source bytes from `git show $I:<path>`; collector records of the head
  # (the two owners' import closures and the definitions in them are unchanged: the readers are theorems).
  LOG=$R/probe-runs/mods/Bb1mProbe_CollectHead.log; Z=$E/rule10-base
  mkdir -p $Z
  python3 -I $T/review/mkseals_ab.py $G $LOG $W $I $Z/seals/A Bb1mProbe/ZS SealA_ $P.Defs $P.BonehBoyen > $Z/mkseals-A.log
  SEAL_EVAL=1 python3 -I $T/review/mkseals_ab.py $G $LOG $W $I $Z/seals/B Bb1mProbe/ZS SealB_ $P.Defs $P.BonehBoyen > $Z/mkseals-B.log
  python3 -I $T/review/mkseals_coe.py $G $LOG $W $I $Z/seals-coe/A Bb1mProbe/ZC SealA_ $P.Defs $P.BonehBoyen > $Z/mkseals-coe-A.log
  SEAL_EVAL=1 python3 -I $T/review/mkseals_coe.py $G $LOG $W $I $Z/seals-coe/B Bb1mProbe/ZC SealB_ $P.Defs $P.BonehBoyen > $Z/mkseals-coe-B.log
  (cd $W && ls Bb1mProbe/ZS/*.lean Bb1mProbe/ZC/*.lean | sed 's/\.lean$//' | LC_ALL=C sort) > $Z/order.txt
  python3 -I $T/runner_full.py $W $Z/order.txt $TREE $Z/seal-runs > $Z/seal-runner.out 2>&1
  for v in seals/A seals/B seals-coe/A seals-coe/B; do
    python3 -I $T/review/sealsum.py $Z/$v $Z/seal-runs $E/statements/touched-base.json $Z/$(echo $v | tr / -).tsv; done;;
scan)
  FILES=$(git -C $W diff --name-only $B $H -- 'TCSlib/*.lean' | grep '/')
  echo $FILES > $E/scan/files.txt
  SCAN_IMPORTS="$MODS" python3 -I $T/scan1_g40.py $G/scan_explicit.py $W \
    $E/statements/touched-after.json $E/scan/items-head.json $W/Bb1mProbe/ScanKindsHead.lean $FILES > $E/scan/scan1.out 2>&1
  cp $W/Bb1mProbe/ScanKindsHead.lean $R/probe-sources/ScanKindsHead.lean.txt
  echo Bb1mProbe/ScanKindsHead > $R/order/scan.txt
  python3 -I $T/runner_full.py $W $R/order/scan.txt $TREE $E/scan/runs > $E/scan/scan-runner.out 2>&1
  python3 -I $T/scan2.py $E/scan/items-head.json $E/scan/runs/mods/Bb1mProbe_ScanKindsHead.log \
    $E/scan/explicit-head.json > $E/scan/scan2-head.log 2>&1; echo "scan2 rc=$?";;
esac
echo "phase $ph done $(date -u +%FT%TZ)"
done
