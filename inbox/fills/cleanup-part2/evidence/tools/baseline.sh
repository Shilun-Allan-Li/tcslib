#!/usr/bin/env bash
# Baseline at the ancestor: root prerequisites (1035) in order, then TCSlib (root), then Checks.
# Failures are recorded and the run continues; dependents of a failed module are skipped by chk.py.
export CHK_PHASE=baseline
O=/workspace/tcslib/outbox/fills/cleanup-part2/inputs/orders
echo "START $(date -u +%FT%TZ) HEAD=$(git -C /workspace/cp2/src rev-parse HEAD) dirty=$(git -C /workspace/cp2/src status --porcelain | wc -l)"
n=0
while read -r m; do n=$((n+1)); echo "## $n/1035 $m"; python3 -I /workspace/cp2/tools/chk.py "$m"; done < $O/root-prerequisites-order.txt
echo "## root"; python3 -I /workspace/cp2/tools/chk.py TCSlib
echo "## Checks"; python3 -I /workspace/cp2/tools/chk.py audits/pass-shelat/Checks
echo "END $(date -u +%FT%TZ)"
