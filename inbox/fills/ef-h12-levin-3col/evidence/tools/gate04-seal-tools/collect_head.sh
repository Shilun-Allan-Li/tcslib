#!/usr/bin/env bash
# collect_head.sh <outdir>: automatic seal candidates at the worktree head only (two passes, as collect.sh)
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
G=$SP/g04r6; WT=$SP/wt-g04r4; T=$G/tools; O=$1
rm -rf $O
bash $T/run_collect.sh $WT $SP/g04r6-oleans $O > $O.out1 2>&1 || exit 3
python3 -I $T/scan.py $WT $G/changed-files.txt $O/tcslib-constants.tsv $O /dev/null /dev/null --srclemmas $O/srclemmas > /dev/null
bash $T/run_collect.sh $WT $SP/g04r6-oleans $O > $O.out2 2>&1 || exit 3
python3 -I $T/unsealable.py $O
echo done
