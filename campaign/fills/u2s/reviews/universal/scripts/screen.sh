#!/bin/bash
# Run the v3 copy-text screen once at the delivered head (wt-head), under the machine-wide screen lock.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/u2-universal
WT=$R/wt-head
POP=$S/wt-hk/campaign/fills/u2s/inputs/u2s-fill-universal/screen-population.txt
OUT=$R/out/24-screen-head.txt
until mkdir $S/locks/screen.lock 2>/dev/null; do sleep 15; done
trap 'rmdir $S/locks/screen.lock' EXIT
cd $WT || exit 1
echo "head=$(git rev-parse HEAD) status=$(git status --porcelain | wc -l) start=$(date -u +%FT%TZ)" > $R/out/24-screen-head.meta
/usr/bin/time -l nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' $POP) > $OUT 2> $R/out/24-screen-head.time
echo "exit=$? end=$(date -u +%FT%TZ)" >> $R/out/24-screen-head.meta
