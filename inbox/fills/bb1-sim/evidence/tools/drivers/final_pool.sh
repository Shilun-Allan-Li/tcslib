#!/usr/bin/env bash
# final_pool.sh (bb1-sim, lead): the final's Lean checks after the final sweep, under the Lean-parallelism ruling
# (evidence/logs/parallelism-ruling.txt): pool POOL=3 = min(nproc 4, MemAvailable ~15 GiB / 4 GiB), shared by three
# concurrent jobs through the host-wide slot locks: (1) the head series' Rule 10 phases, (2) the base series',
# (3) the axioms probe, the final StmtDump and the shadow scan (b). It first waits for the final sweep, which was
# started on the single lock before the ruling arrived and was not interrupted.
E=/home/user/exch/s/inbox/fills/bb1-sim/evidence; DRV=$E/tools/drivers/rule10_bb1sim.sh; PR=$E/tools/seal/poolrun.py
W=/home/user/fill/tcslib; TR=/home/user/fill/treeF; export POOL=3
until grep -q '"done"' $E/build/final-sweep/results.jsonl 2>/dev/null; do sleep 20; done
echo "sweep done $(date -u +%FT%TZ); pool $POOL; MemAvailable-kB $(awk '/MemAvailable/{print $2}' /proc/meminfo)"
bash $DRV head touched collect pretest seals scan > $E/rule10/driver-head.out 2>&1 &
bash $DRV base touched collect baseseals > $E/rule10/driver-base.out 2>&1 &
( python3 -I $PR $W $E/axioms/order.txt $TR $E/axioms/runs > $E/axioms/runner.out 2>&1; echo "axioms rc=$?"
  python3 -I $PR $W $E/stmtdump/final/order.txt $TR $E/stmtdump/final > $E/stmtdump/final/runner.out 2>&1; echo "stmtdump rc=$?"
  python3 -I $PR $W $E/clash/shadow/order.txt $TR $E/clash/shadow/runs > $E/clash/shadow/runner.out 2>&1; echo "shadow rc=$?" ) &
wait
echo "QUEUE DONE $(date -u +%FT%TZ)"
