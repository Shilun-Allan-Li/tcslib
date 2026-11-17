#!/usr/bin/env bash
# runworker.sh <tag> <queue> <rundir> (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. One parallel runner_full.py worker
# (user override of the one-Lean rule, see seals/PARALLEL.txt): its own lock slot, RUN_TAG and the 4.5 GiB memory guard.
set -u
E=/home/user/dw10/exch/inbox/audits/dw10-seal-inventory/evidence
export LEAN_LOCK=/home/user/dw10/lead/.lean.lock.$1 RUN_TAG=$1 MEM_MIN_GB=${MEM_MIN_GB:-4.5} LAKE_PACKAGES=/home/user/dw10/lead/.lake/packages
mkdir -p $3
echo "worker $1 start $(date -u +%FT%TZ) queue $2" >> $3/runner-$1.out
python3 -I $E/tools/seal/runner_full.py /home/user/dw10/lead $2 /home/user/dw10/tree $3 >> $3/runner-$1.out 2>&1
echo "worker $1 rc=$? end $(date -u +%FT%TZ)" >> $3/runner-$1.out
