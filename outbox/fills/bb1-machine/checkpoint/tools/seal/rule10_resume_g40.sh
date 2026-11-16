#!/usr/bin/env bash
# rule10_resume_g40.sh <tree>: resume of rule10_g40.sh after its first background run was stopped by
# the 30-minute background limit during the runner pass (41 of 76 seal/control probes recorded in
# seal-runs/results.jsonl; the interrupted probe left no record). Runs the not-yet-recorded probes
# (same runner, appending to the same results.jsonl), then the rest of rule10_b.sh verbatim
# (sealsum per variant, ctlcheck2 per harness) and the explicit-unfold scan of rule10_g40.sh.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
TREE=$1; E=$SP/dl-review/gate40-le; W=$SP/wt-gate40; T=$E/tools; R=$E/rule10
H=$(git -C $W rev-parse HEAD)
python3 -I - $R <<'EOF'
import json, sys
R = sys.argv[1]
q = [l.strip() for l in open(R + '/order/seal-control-queue.txt') if l.strip()]
done = {json.loads(l).get('module') for l in open(R + '/seal-runs/results.jsonl')}
rest = [m for m in q if m not in done]
open(R + '/order/seal-control-queue-resume.txt', 'w').write(''.join(m + '\n' for m in rest))
print('recorded', len(q) - len(rest), 'remaining', len(rest))
EOF
python3 -I $T/runner_full.py $W $R/order/seal-control-queue-resume.txt $TREE $R/seal-runs > $R/seal-runner-resume.out 2>&1
TJ=$E/statements/touched-after.json
python3 -I $T/review/sealsum.py $R/seals/A $R/seal-runs $TJ $R/seals-A.tsv
python3 -I $T/review/sealsum.py $R/seals/B $R/seal-runs $TJ $R/seals-B.tsv
python3 -I $T/review/sealsum.py $R/seals-coe/A $R/seal-runs $TJ $R/seals-coe-A.tsv
python3 -I $T/review/sealsum.py $R/seals-coe/B $R/seal-runs $TJ $R/seals-coe-B.tsv
python3 -I $T/review/ctlcheck2.py $R/controls-strict/controls-plan.json $R/seal-runs $R/ctlcheck-strict.json > $R/ctlcheck-strict.log || true
python3 -I $T/review/ctlcheck2.py $R/controls-coe/controls-plan.json $R/seal-runs $R/ctlcheck-coe.json > $R/ctlcheck-coe.log || true
MODS="TCSlib.Cryptography.Pairing.Group TCSlib.Cryptography.Pairing.Assumptions
 TCSlib.Cryptography.Pairing.Operations TCSlib.Cryptography.KeyExchange.Joux
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity
 TCSlib.Cryptography.AdvancedEncryption.IdentityBased TCSlib.Cryptography.AdvancedEncryption"
mkdir -p $E/scan
FILES=$(git -C $W diff --name-only 523d80d2d4dd8e4ed6799358831e5b3806c6187b $H -- 'TCSlib/*.lean' | grep '/')
SCAN_IMPORTS="$MODS" python3 -I $T/scan1_g40.py $T/review/archived-gate10-tools/scan_explicit.py $W \
  $E/statements/touched-after.json $E/scan/items-head.json $W/G40Probe/ScanKindsHead.lean $FILES > $E/scan/scan1.out 2>&1
cp $W/G40Probe/ScanKindsHead.lean $R/probe-sources/ScanKindsHead.lean.txt
echo G40Probe/ScanKindsHead > $R/order/scan.txt
python3 -I $T/runner_full.py $W $R/order/scan.txt $TREE $E/scan/runs > $E/scan/scan-runner.out 2>&1
python3 -I $T/scan2.py $E/scan/items-head.json $E/scan/runs/mods/G40Probe_ScanKindsHead.log \
  $E/scan/explicit-head.json > $E/scan/scan2-head.log 2>&1
echo PHASE2-DONE
