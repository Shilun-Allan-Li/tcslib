#!/usr/bin/env bash
# scratch.sh <Module path without .lean> <logdir-name>: one development check with runner_full.py
# (no -o, -DmaxErrors=0, under the host lock); log under evidence/subagents/probe/scratch/<name>/.
E=/home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/subagents/probe
mkdir -p "$E/scratch/$2"
echo "$1" > "$E/scratch/$2/order.txt"
python3 -I /home/user/exch/s/inbox/fills/bb1-sim-statements/evidence/tools/seal/runner_full.py \
  /home/user/fill/wt-probe "$E/scratch/$2/order.txt" /home/user/fill/treeP "$E/scratch/$2"
tail -1 "$E/scratch/$2/results.jsonl" >/dev/null
head -c 600 <(grep -v '"done"' "$E/scratch/$2/results.jsonl")
echo
cat "$E/scratch/$2/mods/"*.log
