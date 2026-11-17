#!/usr/bin/env bash
# final_queue.sh (bb1-sim, lead): every Lean check of the final, in one sequential queue at the check head: the
# final sweep (the 13 DOWN modules and the 5 helpers), the head series' Rule 10 phases, the base series, the axioms
# probe, the final StmtDump and the shadow scan (b). History: a first run was killed mid-way by a worker restart
# (evidence/rule10/driver-before-restart.out); a second was stopped by the lead to add four proof sketches
# (docstrings only), which changed the head; this is the third, at the final head.
E=/home/user/exch/s/inbox/fills/bb1-sim/evidence; DRV=$E/tools/drivers/rule10_bb1sim.sh; RF=$E/tools/seal/runner_full.py
W=/home/user/fill/tcslib; TR=/home/user/fill/treeF
B=$E/build/final-sweep; mkdir -p $B; git -C $W rev-parse HEAD > $B/HEAD.txt; git -C $W status --short > $B/status.txt
cp $E/build/sweep-set.txt $B/order.txt
python3 -I $E/tools/review/runner.py $W $B/order.txt $TR $B > $B/runner.out 2>&1; echo "sweep rc=$?"
bash $DRV head touched collect pretest seals scan
bash $DRV base touched collect baseseals
python3 -I $RF $W $E/axioms/order.txt $TR $E/axioms/runs > $E/axioms/runner.out 2>&1; echo "axioms rc=$?"
python3 -I $RF $W $E/stmtdump/final/order.txt $TR $E/stmtdump/final > $E/stmtdump/final/runner.out 2>&1; echo "stmtdump rc=$?"
python3 -I $RF $W $E/clash/shadow/order.txt $TR $E/clash/shadow/runs > $E/clash/shadow/runner.out 2>&1; echo "shadow rc=$?"
echo "QUEUE DONE $(date -u +%FT%TZ)"
superseded by final_pool.sh after the Lean-parallelism ruling; this script's run was stopped after it had started the final sweep
