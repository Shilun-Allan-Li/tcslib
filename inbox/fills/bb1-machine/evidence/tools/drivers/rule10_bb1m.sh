#!/usr/bin/env bash
# rule10_bb1m.sh <phase...> (fill-bb1-machine): fill-pair-bdh's rule10_pbdh.sh (LE-gate40's rule10_g40.sh lineage) on the
# fill head, with the changed owners of this fill (the four helper modules under BonehBoyenMachine/ and the owned
# BonehBoyenMachine.lean). Changes: worktree wt-fill-bb1-machine, probe subdir Bb1mProbe, owners below, controls
# generator mkctl_bb1m.py (mkctl_pbdh.py plus rows, header), phases selectable (collect | seals | scan). Every probe
# through runner_full.py (lean -DmaxErrors=0, no -o: nothing written to the tree). One Lean process at a time.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
TREE=$SP/dl-oleans; E=$SP/dl-review/fill-bb1-machine; W=$SP/wt-fill-bb1-machine; T=$E/tools-used/seal; R=$E/rule10
B=9e7a96481785d6cac4dea3b2e990c49ac278b060; H=$(git -C $W rev-parse HEAD)
export TCSLIB_OLEANS_TREE=$TREE TMPDIR=$SP/bb1m-work/tmp
P=TCSlib.Cryptography.AdvancedEncryption.IdentityBased
MODS="$P.BonehBoyenMachine.Draws $P.BonehBoyenMachine.Words $P.BonehBoyenMachine.Handler $P.BonehBoyenMachine.Reduction $P.BonehBoyenMachine"
mkdir -p $R/order $R/probe-sources $E/scan $W/Bb1mProbe
for ph in "$@"; do
echo "phase $ph start $(date -u +%FT%TZ) head $H"
case $ph in
collect)
  printf '%s\n' $MODS > $R/order/owners.txt
  python3 -I $T/review/mkcollect.py $T/review/NmCollect.template.lean $R/order/owners.txt "fill-bb1-machine collector" $W/Bb1mProbe/CollectHead.lean
  cp $W/Bb1mProbe/CollectHead.lean $R/probe-sources/CollectHead.lean.txt
  printf 'Bb1mProbe/CollectHead\n' > $R/order/probes.txt
  python3 -I $T/runner_full.py $W $R/order/probes.txt $TREE $R/probe-runs > $R/probe-runner.out 2>&1; echo "collector rc=$?";;
seals)
  bash $T/rule10_b.sh $T $W $E Bb1mProbe $H $T/review/mkctl_bb1m.py $MODS > $R/rule10-driver.out 2>&1; echo "rule10_b rc=$?";;
scan)
  FILES=$(git -C $W diff --name-only $B $H -- 'TCSlib/*.lean' | grep '/')
  echo $FILES > $E/scan/files.txt
  SCAN_IMPORTS="$MODS" python3 -I $T/scan1_g40.py $T/review/archived-gate10-tools/scan_explicit.py $W \
    $E/statements/touched-after.json $E/scan/items-head.json $W/Bb1mProbe/ScanKindsHead.lean $FILES > $E/scan/scan1.out 2>&1
  cp $W/Bb1mProbe/ScanKindsHead.lean $R/probe-sources/ScanKindsHead.lean.txt
  echo Bb1mProbe/ScanKindsHead > $R/order/scan.txt
  python3 -I $T/runner_full.py $W $R/order/scan.txt $TREE $E/scan/runs > $E/scan/scan-runner.out 2>&1
  python3 -I $T/scan2.py $E/scan/items-head.json $E/scan/runs/mods/Bb1mProbe_ScanKindsHead.log \
    $E/scan/explicit-head.json > $E/scan/scan2-head.log 2>&1; echo "scan2 rc=$?";;
esac
echo "phase $ph done $(date -u +%FT%TZ)"
done
