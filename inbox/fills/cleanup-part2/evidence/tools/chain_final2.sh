#!/usr/bin/env bash
# Final chain part 2 (after the seals): census rerun with the C3 collector that also enumerates the
# probe's own constants (rows for owned modules must be identical to run 1), C3 metadata controls,
# sensitivity controls (N4 redesigned; attempt 1 retained). Serial.
set -u
cd /workspace/cp2/src
EV=/workspace/cp2/evidence
NOT=Complexity.PolyExpr.eval,Complexity.PolyExpr.eval.match_1,Complexity.PolyExpr.eval._sunfold
echo "## CHAIN2 START $(date -u +%FT%TZ) HEAD=$(git rev-parse HEAD) dirty=$(git status --porcelain -- TCSlib audits TCSlib.lean | wc -l)"
mv $EV/census/final $EV/census/final-run1
mkdir -p $EV/census/final
python3 -I /workspace/cp2/tools/gen_census.py /workspace/tcslib/outbox/fills/cleanup-part2/inputs/owned-files.txt .lake/cleanup-part2-probes/census/FinalCensus2.lean $EV/census/final
CHK_PHASE=census-final2 python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/census/FinalCensus2
for f in names.tsv axioms.tsv c3.tsv closure.tsv; do cmp -s $EV/census/final/$f $EV/census/final-run1/$f && echo "IDENTICAL $f" || echo "DIFFERS $f"; done
rm -f $EV/census/c3controls/c3.tsv
python3 -I /workspace/cp2/tools/c3controls.py .lake/cleanup-part2-probes/census/C3Controls.lean $EV/census/c3controls
CHK_PHASE=c3controls-final2 python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/census/C3Controls
mkdir -p .lake/cleanup-part2-probes/controls
cp /workspace/cp2/tools/lean/Controls.lean.txt .lake/cleanup-part2-probes/controls/ControlsUnsealed.lean
CHK_PHASE=controls-final2 python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/controls/ControlsUnsealed
CP2_SEAL_NOTATION=$NOT python3 -I /workspace/cp2/tools/mkseal.py $EV/census/final/closure.tsv TCSlib.Complexity.Randomized.PPT /workspace/cp2/tools/lean/Controls.lean.txt .lake/cleanup-part2-probes/controls/ControlsSealed.lean
CHK_PHASE=controls-final2 python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/controls/ControlsSealed
echo "## CHAIN2 DONE $(date -u +%FT%TZ)"
