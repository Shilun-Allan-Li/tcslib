#!/usr/bin/env bash
# One v3 screen run at the delivered head (wt-head), niced, under the machine-wide screen lock.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/g4-cont4; WT=$R/wt-head; OUT=$R/out/27-screen-head.txt
P=campaign/fills/s13d/inputs/s13d-fill-g4-cont4/screen-population.txt
echo "waiting for lock from $(date -u +%FT%TZ)" > $OUT.status
until mkdir $S/locks/screen.lock 2>/dev/null; do sleep 15; done
trap 'rmdir $S/locks/screen.lock; echo "lock released $(date -u +%FT%TZ)" >> $OUT.status' EXIT
echo "lock acquired $(date -u +%FT%TZ); head $(git -C $WT rev-parse HEAD); status: $(git -C $WT status --porcelain | wc -l) changes" >> $OUT.status
cd $WT
t0=$(date +%s)
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' $P) > $OUT 2> $OUT.err
rc=$?
echo "exit $rc; wall $(( $(date +%s) - t0 )) s; end $(date -u +%FT%TZ); worktree changes after: $(git -C $WT status --porcelain | wc -l)" >> $OUT.status
