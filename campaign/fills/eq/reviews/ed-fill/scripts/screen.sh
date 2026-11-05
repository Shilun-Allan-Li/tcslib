#!/usr/bin/env bash
# Head screen on a frozen copy of the population, under the machine-wide screen lock.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
until mkdir $S/locks/screen 2>/dev/null; do sleep 30; done
echo "lock acquired $(date -u +%FT%TZ)" > $R/out/17-screen-head.meta
trap 'rmdir $S/locks/screen; echo "lock released $(date -u +%FT%TZ)" >> $R/out/17-screen-head.meta' EXIT
cd $R/screen-head
/usr/bin/time -l nice -n 10 python3 -I $R/scripts/copy-text-screen-v3.py . $(cat $R/out/17-population.txt) > $R/out/17-screen-head.txt 2> $R/out/17-screen-head.time
echo "exit=$?" >> $R/out/17-screen-head.time
