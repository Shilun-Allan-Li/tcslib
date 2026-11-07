#!/usr/bin/env bash
# Resume: wait for the in-flight module of the first driver, then build the remaining Checks
# prerequisites (skipping those with an object fresher than the first driver's start), then
# recheck the owned modules and their downstream modules (RSA docstring edit), then Checks.
export PATH=$HOME/.elan/bin:$PATH
I=/workspace/tcslib/outbox/fills/reject-blocks-s2/inputs
cd /workspace/tcslib-fill
while pgrep -x lean > /dev/null || pgrep -f "chkS.py" > /dev/null; do sleep 5; done
echo "## resume $(date -u +%H:%M:%S)"
n=0; skipped=0
while read -r m; do
  grep -qxF "$m" $I/order.txt && continue
  n=$((n+1))
  if [ -s /workspace/s2-oleans/$m.olean ] && [ /workspace/s2-oleans/$m.olean -nt /workspace/s2-prereq-stamp ]; then
    skipped=$((skipped+1)); continue
  fi
  echo "## prereq $n/328 $m"
  python3 -I /workspace/bin/chkS.py "$m" 2>&1 | grep "^== \|FAIL\|error:" || true
  [ -s /workspace/s2-oleans/$m.olean ] && [ /workspace/s2-oleans/$m.olean -nt /workspace/s2-prereq-stamp ] || { echo "STOP: $m"; exit 1; }
done < $I/checks-order.txt
echo "## prereqs done: $n (skipped as already built by the first driver: $skipped)"
echo "## downstream recheck"
for m in $(cat /workspace/s2-evidence/logs/downstream-order.txt); do
  python3 -I /workspace/bin/chkS.py "$m" 2>&1 | grep "^== \|FAIL\|error:" || { echo "STOP downstream $m"; exit 1; }
done
echo "## Checks"
python3 -I /workspace/bin/chkS.py audits/pass-shelat/Checks > /workspace/s2-evidence/logs/checks-final-Checks.full.log 2>&1
rc=$?
grep "^== \|FAIL" /workspace/s2-evidence/logs/checks-final-Checks.full.log
echo "## Checks rc=$rc"
