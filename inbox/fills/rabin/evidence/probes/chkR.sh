#!/usr/bin/env bash
# check the owned module, log to module-checks.log, print non-sorry lines
cd /workspace/tcslib-fill
export PATH=$HOME/.elan/bin:$PATH
python3 /workspace/bin/chk.py TCSlib/Cryptography/Candidates/Rabin > /tmp/chkR.out 2>&1
rc=$?
{ cat /tmp/chkR.out | grep "^==" ; echo "   errors=$(grep -c 'error' /tmp/chkR.out) sorry-warnings=$(grep -c "declaration uses 'sorry'" /tmp/chkR.out)"; } >> /workspace/rabin-evidence/logs/module-checks.log
grep -v "declaration uses 'sorry'" /tmp/chkR.out | head -${2:-60}
echo "sorry-warnings=$(grep -c "declaration uses 'sorry'" /tmp/chkR.out)"
exit $rc
