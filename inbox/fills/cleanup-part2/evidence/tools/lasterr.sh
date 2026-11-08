#!/usr/bin/env bash
# show the errors of the module the dev run stopped at
m=$(grep "^STOP" /workspace/cp2/devrun.log | tail -1 | awk '{print $3}')
echo "STOPPED AT: $(grep '^STOP' /workspace/cp2/devrun.log | tail -1)"
[ -z "$m" ] && { tail -3 /workspace/cp2/devrun.log; exit 0; }
grep -A${1:-10} "error" /workspace/cp2/evidence/logs/dev/modules/$m.log | grep -v "^FAIL" | head -${2:-60}
