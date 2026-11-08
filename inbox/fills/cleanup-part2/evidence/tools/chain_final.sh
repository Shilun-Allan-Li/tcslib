#!/usr/bin/env bash
# Final verification chain at the frozen fill HEAD (serial, one Lean process at a time):
# affected replay + root + Checks (phase final), census (census-final), C3 metadata controls,
# whole-file seals (standard and strict variants), sensitivity controls (unsealed and sealed).
set -u
cd /workspace/cp2/src
H=$(git rev-parse HEAD)
EV=/workspace/cp2/evidence
NOT=Complexity.PolyExpr.eval,Complexity.PolyExpr.eval.match_1,Complexity.PolyExpr.eval._sunfold
echo "## CHAIN START $(date -u +%FT%TZ) HEAD=$H"
bash /workspace/cp2/tools/replay_affected.sh final > $EV/logs/replay-final.log 2>&1
echo "## replay done $(date -u +%FT%TZ) fails=$(grep -c '^FAIL' $EV/logs/replay-final.log)"
mkdir -p $EV/census/final .lake/cleanup-part2-probes/census
python3 -I /workspace/cp2/tools/gen_census.py /workspace/tcslib/outbox/fills/cleanup-part2/inputs/owned-files.txt .lake/cleanup-part2-probes/census/FinalCensus.lean $EV/census/final
CHK_PHASE=census-final python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/census/FinalCensus
echo "## census done $(date -u +%FT%TZ)"
mkdir -p $EV/census/c3controls
python3 -I /workspace/cp2/tools/c3controls.py .lake/cleanup-part2-probes/census/C3Controls.lean $EV/census/c3controls
CHK_PHASE=c3controls-final python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/census/C3Controls
echo "## c3 controls done $(date -u +%FT%TZ)"
mkdir -p .lake/cleanup-part2-probes/controls
cp /workspace/cp2/tools/lean/Controls.lean.txt .lake/cleanup-part2-probes/controls/ControlsUnsealed.lean
CHK_PHASE=controls-final python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/controls/ControlsUnsealed
CP2_SEAL_NOTATION=$NOT python3 -I /workspace/cp2/tools/mkseal.py $EV/census/final/closure.tsv TCSlib.Complexity.Randomized.PPT /workspace/cp2/tools/lean/Controls.lean.txt .lake/cleanup-part2-probes/controls/ControlsSealed.lean
CHK_PHASE=controls-final python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/controls/ControlsSealed
echo "## controls done $(date -u +%FT%TZ)"
CP2_SEAL_NOTATION=$NOT python3 -I /workspace/cp2/tools/sealrun.py final $H $EV/census/final/closure.tsv /workspace/cp2/seal-baseline-modules.txt
echo "## seal standard done $(date -u +%FT%TZ)"
python3 -I /workspace/cp2/tools/sealrun.py final-strict $H $EV/census/final/closure.tsv /workspace/cp2/seal-baseline-modules.txt
echo "## CHAIN DONE $(date -u +%FT%TZ)"
