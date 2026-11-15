#!/usr/bin/env bash
# Final runs, resumable after a host restart: recheck the owned module, sweep the final order
# (order.txt with the six helpers inserted before the owned module), then final_pipeline.sh.
set -u
E=/workspace/exchange/inbox/fills/sc-ot/evidence/logs
W=/workspace/scot-work
cd /workspace/scot
cp $W/order-final.txt $E/final-order.txt
if ! grep -q "status=0" $E/final-owned-recheck.log 2>/dev/null; then
  /workspace/scot-tools/check.sh TCSlib/Cryptography/SecureComputation/ObliviousTransfer $E/final-owned-recheck.log
fi
[ -f $W/final.state ] || echo 0 > $W/final.state
/workspace/scot-tools/sweep_chunk.sh $W/order-final.txt $E/final-sweep.log $W/final.state 100000 || exit 1
/workspace/scot-tools/final_pipeline.sh
echo RUN-FINAL-DONE
