#!/usr/bin/env bash
# Affected replay at the current fill HEAD (phase $1): changed modules and all their transitive
# importers in current topological order (tools/order.py, tools/affected.py), then TCSlib and
# Checks. Unaffected modules keep their baseline objects (same source, same prerequisites).
export CHK_PHASE=$1
cd /workspace/cp2/src
echo "START $(date -u +%FT%TZ) HEAD=$(git rev-parse HEAD) dirty=$(git status --porcelain -- TCSlib audits TCSlib.lean | wc -l)"
python3 -I /workspace/cp2/tools/order.py /workspace/cp2/evidence/logs/order-$1.txt
python3 -I /workspace/cp2/tools/affected.py /workspace/cp2/evidence/logs/order-$1.txt /workspace/cp2/evidence/logs/affected-$1.txt
n=0; t=$(wc -l < /workspace/cp2/evidence/logs/affected-$1.txt)
while read -r m; do n=$((n+1)); echo "## $n/$t $m"; python3 -I /workspace/cp2/tools/chk.py "$m"; done < /workspace/cp2/evidence/logs/affected-$1.txt
echo "## root"; python3 -I /workspace/cp2/tools/chk.py TCSlib
echo "## Checks"; python3 -I /workspace/cp2/tools/chk.py audits/pass-shelat/Checks
echo "END $(date -u +%FT%TZ)"
