#!/usr/bin/env bash
# run-dev-build.sh <queue> <logdir> (fill-bb1-machine): build a queue on dl-oleans through scripts/lean_check_tree.sh
# (runner.py, stops on first failure); backups must be taken first with backup_cum.py.
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad; E=$SP/dl-review/fill-bb1-machine
export TMPDIR=$SP/bb1m-work/tmp
cd $E
echo "start $(date -u +%FT%TZ)"
python3 -I tools-used/review/runner.py $SP/wt-fill-bb1-machine $1 $SP/dl-oleans $2
echo "runner exit $? $(date -u +%FT%TZ)"
