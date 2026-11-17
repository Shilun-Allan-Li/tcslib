#!/usr/bin/env bash
# devcheck.sh <A|B|N> <tag>: development check of PlProbe/BB1SimStepM (N = native without -o via
# runner_full; A/B = devseal variant PlProbe/Sealed/BB1SimStepM_<A|B>.lean). Logs under
# evidence/subagents/probe/scratch/dev-<tag>-<variant>/.
E=/home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/subagents/probe
WT=/home/user/fill/wt-probe
V=$1; T=$2
if [ "$V" = N ]; then M=PlProbe/BB1SimStepM; else
  python3 -I $E/tools/devseal.py $WT/PlProbe/BB1SimStepM.lean $WT/PlProbe/Sealed/BB1SimStepM_$V.lean $V
  M=PlProbe/Sealed/BB1SimStepM_$V; fi
D=$E/scratch/dev-$T-$V; mkdir -p $D; echo $M > $D/order.txt
python3 -I /home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/tools/seal/runner_full.py $WT $D/order.txt /home/user/fill/treeP $D
grep -v done $D/results.jsonl | python3 -I -c "import json,sys; r=json.loads(sys.stdin.readline()); print('rc',r['rc'],'errors',r['errors'],'secs',r['seconds'])"
grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error[:(]' $D/mods/*.log
cat $D/mods/*.log
