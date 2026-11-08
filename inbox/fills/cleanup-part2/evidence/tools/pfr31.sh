#!/usr/bin/env bash
# The 31 PFR checks, serially, adapter PATH scoped to each single chk.py --pfr invocation; stop on first failure.
P=/workspace/tcslib/outbox/fills/cleanup-part2/external-bootstrap-r1/bootstrap-order.txt
echo "START $(date -u +%FT%TZ)"
n=0
while read -r rel; do
  n=$((n+1)); echo "## $n/31 $rel"
  python3 -I /workspace/cp2/tools/chk.py "$rel" --pfr || { echo "STOP at $rel (rc $?)"; exit 1; }
done < "$P"
echo "END $(date -u +%FT%TZ) all $n passed"
