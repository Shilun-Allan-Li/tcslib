#!/usr/bin/env bash
# rule10_g40.sh <tree>: phase 2 of LE-gate40 after the closure build: the collector and axiom probes,
# then rule10_b.sh (strict/coe seals A and B, paired controls, one runner pass, sealsum, ctlcheck2),
# then the explicit-unfold scan (scan1_g40 -> kinds probe -> scan2). Every probe through
# runner_full.py (lean -DmaxErrors=0, no -o: nothing written to the tree). One Lean process at a time.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
TREE=$1; E=$SP/dl-review/gate40-le; W=$SP/wt-gate40; T=$E/tools; R=$E/rule10
export TCSLIB_OLEANS_TREE=$TREE
H=$(git -C $W rev-parse HEAD)
MODS="TCSlib.Cryptography.Pairing.Group TCSlib.Cryptography.Pairing.Assumptions
 TCSlib.Cryptography.Pairing.Operations TCSlib.Cryptography.KeyExchange.Joux
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased TCSlib.Cryptography.AdvancedEncryption"
mkdir -p $R/order $E/axioms $E/scan
# 1. collector and axiom census
printf 'G40Probe/CollectHead\nG40Probe/AxiomsHead\n' > $R/order/probes.txt
python3 -I $T/runner_full.py $W $R/order/probes.txt $TREE $R/probe-runs > $R/probe-runner.out 2>&1
cp $R/probe-runs/mods/G40Probe_AxiomsHead.log $E/axioms/AxiomsHead.log
# 2. seals and controls
bash $T/rule10_b.sh $T $W $E G40Probe $H $T/review/mkctl_g40.py $MODS > $R/rule10-driver.out 2>&1
# 3. explicit-unfold scan
FILES=$(git -C $W diff --name-only 523d80d2d4dd8e4ed6799358831e5b3806c6187b $H -- 'TCSlib/*.lean' | grep '/')
SCAN_IMPORTS="$MODS" python3 -I $T/scan1_g40.py $T/review/archived-gate10-tools/scan_explicit.py $W \
  $E/statements/touched-after.json $E/scan/items-head.json $W/G40Probe/ScanKindsHead.lean $FILES > $E/scan/scan1.out 2>&1
cp $W/G40Probe/ScanKindsHead.lean $R/probe-sources/ScanKindsHead.lean.txt
echo G40Probe/ScanKindsHead > $R/order/scan.txt
python3 -I $T/runner_full.py $W $R/order/scan.txt $TREE $E/scan/runs > $E/scan/scan-runner.out 2>&1
python3 -I $T/scan2.py $E/scan/items-head.json $E/scan/runs/mods/G40Probe_ScanKindsHead.log \
  $E/scan/explicit-head.json > $E/scan/scan2-head.log 2>&1
echo PHASE2-DONE
