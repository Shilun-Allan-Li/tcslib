#!/usr/bin/env bash
# The restricted screen (pairs involving NDNormalForm) at the delivery head, under the machine-wide screen lock.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/nf-cont1-fill
L=$S/locks/screen
echo "waiting for the screen lock $(date -u +%FT%TZ)" > $R/out/20-screen-nf.log
until mkdir "$L" 2>/dev/null; do sleep 30; done
trap 'rmdir "$L" 2>/dev/null' EXIT
echo "lock acquired $(date -u +%FT%TZ)" >> $R/out/20-screen-nf.log
cd $R/wt-head || exit 1
P=campaign/fills/c1/inputs/c1-fill-nf-cont1/screen-population.txt
/usr/bin/time -l nice -n 10 python3 -I $R/scripts/screen-nf-pairs.py . $(grep -v '^#' $P) > $R/out/20-screen-nf.txt 2> $R/out/20-screen-nf.err
echo "exit=$? done $(date -u +%FT%TZ)" >> $R/out/20-screen-nf.log
