#!/usr/bin/env bash
# Final evidence at the final head: fresh sweep (olean tree removed first), declaration dump and
# axioms, whole-file seals (PolyExpr.eval sealed, then open for the failing files), paired
# controls, explicit-unfold scans. One Lean process at a time. Waits for phase_base.
set -u
L=/workspace/exchange/inbox/fills/dl-consolidation/evidence/logs
W=/workspace/dlc
while ! grep -q "PHASE BASE DONE" /workspace/dlc-work/phase_base.out 2>/dev/null; do sleep 30; done
cd $W
git rev-parse HEAD > $L/final-head.txt
git status --short > $L/final-status.txt
rm -rf $W/.lake/tcslib-check-oleans
rm -f $L/sweep-final.log /workspace/dlc-work/final.state
cp /workspace/dlc-work/order-final.txt $L/order-final.txt
bash /workspace/dlc-tools/sweep_chunk.sh $L/order-final.txt $L/sweep-final.log /workspace/dlc-work/final.state 100000 || exit 1
rm -f $L/decl-dump-final.log
/workspace/dlc-tools/check.sh lean_proof/dlc/DeclDumpFinal $L/decl-dump-final.log
rm -f $L/seal-final.jsonl $L/seal-final.out $L/seal-final-evalopen.jsonl $L/seal-final-evalopen.out
python3 /workspace/dlc-tools/seal_run.py $W final $L/seal-final.jsonl $(cat /workspace/dlc-work/final-files.txt)
FAILING=$(python3 -c "
import json
print(' '.join(json.loads(l)['file'] for l in open('$L/seal-final.jsonl') if json.loads(l)['status']!=0))")
[ -n "$FAILING" ] && python3 /workspace/dlc-tools/seal_run.py $W final-evalopen $L/seal-final-evalopen.jsonl --eval-open $FAILING
mkdir -p lean_proof/dlc
cp /workspace/dlc-tools/SealControls.lean lean_proof/dlc/SealControls.lean
python3 /workspace/dlc-tools/seal_gen.py $W lean_proof/dlc/SealControls.lean lean_proof/dlc/SealControlsSealed
python3 /workspace/dlc-tools/seal_gen.py $W lean_proof/dlc/SealControls.lean lean_proof/dlc/SealControlsSealedEvalOpen --eval-open
rm -f $L/seal-controls-unsealed.log $L/seal-controls-sealed.log $L/seal-controls-sealed-evalopen.log
/workspace/dlc-tools/check.sh lean_proof/dlc/SealControls $L/seal-controls-unsealed.log
/workspace/dlc-tools/check.sh lean_proof/dlc/SealControlsSealed $L/seal-controls-sealed.log
/workspace/dlc-tools/check.sh lean_proof/dlc/SealControlsSealedEvalOpen $L/seal-controls-sealed-evalopen.log
rm -f $L/rwids-final.log $L/rwids-final.tsv
bash /workspace/dlc-tools/rwids_run.sh $W lean_proof/dlc/rwids/final $L/rwids-final.log $L/rwids-final.tsv
echo "PHASE FINAL DONE $(date -u +%FT%TZ)"
