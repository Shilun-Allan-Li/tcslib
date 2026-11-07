#!/usr/bin/env bash
# Build the Checks prerequisites not in inputs/order.txt, in checks-order.txt order, then Checks.
export PATH=$HOME/.elan/bin:$PATH
I=/workspace/tcslib/outbox/fills/reject-blocks-s2/inputs
cd /workspace/tcslib-fill
n=0
while read -r m; do
  grep -qxF "$m" $I/order.txt && continue
  n=$((n+1)); echo "## prereq $n/328 $m"
  python3 -I /workspace/bin/chkS.py "$m" 2>&1 | grep "^== \|FAIL\|error:" || true
  [ -s /workspace/s2-oleans/$m.olean ] || { echo "STOP: $m"; exit 1; }
done < $I/checks-order.txt
echo "## prereqs done: $n"
echo "## Checks"
python3 -I /workspace/bin/chkS.py audits/pass-shelat/Checks > /workspace/s2-evidence/logs/checks-final-Checks.full.log 2>&1
rc=$?
grep "^== \|FAIL" /workspace/s2-evidence/logs/checks-final-Checks.full.log
echo "## Checks rc=$rc"
