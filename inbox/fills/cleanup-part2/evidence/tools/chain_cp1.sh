#!/usr/bin/env bash
# After the dev pass: root + Checks (phase dev), head census (phase census-j2), head seals (phase j2,
# standing-rule notation PolyExpr.eval unsealed). Serial; stops on the first failure.
set -u
cd /workspace/cp2/src
while ! grep -q "ALL PASS\|^STOP" /workspace/cp2/devrun.log; do sleep 30; done
grep -q "ALL PASS" /workspace/cp2/devrun.log || { echo "CHAIN: devrun stopped"; exit 1; }
echo "## root $(date -u +%FT%TZ)"
CHK_PHASE=dev python3 -I /workspace/cp2/tools/chk.py TCSlib || { echo "CHAIN: root FAIL"; exit 1; }
echo "## Checks $(date -u +%FT%TZ)"
CHK_PHASE=dev python3 -I /workspace/cp2/tools/chk.py audits/pass-shelat/Checks || { echo "CHAIN: Checks FAIL"; exit 1; }
echo "## census $(date -u +%FT%TZ)"
mkdir -p /workspace/cp2/evidence/census/j2 .lake/cleanup-part2-probes/census
python3 -I /workspace/cp2/tools/gen_census.py /workspace/tcslib/outbox/fills/cleanup-part2/inputs/owned-files.txt .lake/cleanup-part2-probes/census/J2Census.lean /workspace/cp2/evidence/census/j2
CHK_PHASE=census-j2 python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/census/J2Census || { echo "CHAIN: census FAIL"; exit 1; }
echo "## seals $(date -u +%FT%TZ)"
CP2_SEAL_NOTATION=Complexity.PolyExpr.eval,Complexity.PolyExpr.eval.match_1,Complexity.PolyExpr.eval._sunfold \
  python3 -I /workspace/cp2/tools/sealrun.py j2 HEAD /workspace/cp2/evidence/census/j2/closure.tsv /workspace/cp2/seal-baseline-modules.txt
echo "## CHAIN DONE $(date -u +%FT%TZ)"
