#!/usr/bin/env bash
# Checkpoint-2 checks, one Lean process at a time: the downstream sweep, the axioms probe, the seals.
E=/workspace/exchange/inbox/fills/sc-ot/evidence/logs
EV=/workspace/exchange/inbox/fills/sc-ot/evidence/seal-cp2
mkdir -p $EV
cd /workspace/scot
[ -f /workspace/scot-work/cp2.state ] || echo 0 > /workspace/scot-work/cp2.state
/workspace/scot-tools/sweep_chunk.sh /workspace/scot-work/cp2-downstream.txt $E/checkpoint2-checks.log /workspace/scot-work/cp2.state 100000
[ -s $E/checkpoint2-axioms.log ] || /workspace/scot-tools/check.sh lean_proof/scot/probes/AxiomsCP2 $E/checkpoint2-axioms.log
F="TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean"
for v in As Ac Bs Bc; do
  args=""; case $v in A*) args="--eval-open";; esac; case $v in *c) args="$args --coe-open";; esac
  for f in $F; do
    grep -q "\"file\": \"$f\"" $EV/seal-$v.jsonl 2>/dev/null && continue
    python3 -I /workspace/scot-tools/seal_run.py /workspace/scot cp2$v $EV/seal-$v.jsonl $args $f
  done
done
echo CP2-CHECKS-DONE
