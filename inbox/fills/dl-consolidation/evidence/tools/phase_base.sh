#!/usr/bin/env bash
# Base controls, after the base tree build: seals (PolyExpr.eval sealed, then open for the files
# that fail), explicit-unfold scans, extended declaration dump. One Lean process at a time.
set -u
L=/workspace/exchange/inbox/fills/dl-consolidation/evidence/logs
B=/workspace/dlc-base
while ! grep -q "SWEEP COMPLETE\|SWEEP STOPPED" $L/base-tree.log 2>/dev/null; do sleep 30; done
grep -q "SWEEP COMPLETE" $L/base-tree.log || { echo "base tree failed"; exit 1; }
rm -f $L/seal-base.jsonl $L/seal-base.out $L/seal-base-evalopen.jsonl $L/seal-base-evalopen.out
python3 /workspace/dlc-tools/seal_run.py $B base $L/seal-base.jsonl $(cat /workspace/dlc-work/base-files.txt)
FAILING=$(python3 -c "
import json
print(' '.join(json.loads(l)['file'] for l in open('$L/seal-base.jsonl') if json.loads(l)['status']!=0))")
[ -n "$FAILING" ] && python3 /workspace/dlc-tools/seal_run.py $B base-evalopen $L/seal-base-evalopen.jsonl --eval-open $FAILING
rm -f $L/rwids-base.log $L/rwids-base.tsv
bash /workspace/dlc-tools/rwids_run.sh $B lean_proof/dlc/rwids/base $L/rwids-base.log $L/rwids-base.tsv
rm -f $L/decl-dump-base-ext.log
WT=$B /workspace/dlc-tools/check.sh lean_proof/dlc/DeclDumpBase $L/decl-dump-base-ext.log
echo "PHASE BASE DONE $(date -u +%FT%TZ)"
