#!/usr/bin/env bash
# Resume: rerun (in root-prerequisite order) every module whose last baseline record is not PASS
# (the 80 modules skipped by the first run because chk.py's prerequisite resolver did not search
# the toolchain's own library for `Std.Sat.CNF`; fixed before this resume), then root and Checks.
export CHK_PHASE=baseline
O=/workspace/tcslib/outbox/fills/cleanup-part2/inputs/orders
echo "START resume $(date -u +%FT%TZ) HEAD=$(git -C /workspace/cp2/src rev-parse HEAD) dirty=$(git -C /workspace/cp2/src status --porcelain | wc -l)"
python3 -I - > /workspace/cp2/resume-list.txt <<'PY'
import json
last={}
for l in open('/workspace/cp2/evidence/logs/checks-baseline.jsonl'):
    r=json.loads(l); last[r['module']]=r.get('status')
for m in open('/workspace/tcslib/outbox/fills/cleanup-part2/inputs/orders/root-prerequisites-order.txt'):
    m=m.strip()
    if m and last.get(m)!='PASS': print(m)
PY
n=0; t=$(wc -l < /workspace/cp2/resume-list.txt)
while read -r m; do n=$((n+1)); echo "## resume $n/$t $m"; python3 -I /workspace/cp2/tools/chk.py "$m"; done < /workspace/cp2/resume-list.txt
echo "## root"; python3 -I /workspace/cp2/tools/chk.py TCSlib
echo "## Checks"; python3 -I /workspace/cp2/tools/chk.py audits/pass-shelat/Checks
echo "END $(date -u +%FT%TZ)"
