#!/usr/bin/env bash
# Both v3 screens (before = the overlay's state, after = the delivered head), one at a time, niced, under the screen lock.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/c1-core-cont2; P=$R/wt-base/campaign/fills/c1/inputs/c1-fill-core-cont2
SCR=$R/wt-base/scripts/copy-text-screen-v3.py
until mkdir $S/locks/screen.lock 2>/dev/null; do sleep 15; done
trap 'rmdir $S/locks/screen.lock' EXIT
FILES=$(grep -v '^#' $P/screen-population.txt)
run() { # name root
  echo "$1 start $(date -u +%FT%TZ)" >> $R/out/29-30-screens.log
  /usr/bin/time -p nice -n 10 python3 -I $SCR $2 $FILES > $R/out/$1.txt 2> $R/out/$1.txt.err; echo $? > $R/out/$1.txt.status
  echo "$1 end $(date -u +%FT%TZ) status $(cat $R/out/$1.txt.status)" >> $R/out/29-30-screens.log
}
run 29-screen-before $R/screen-before-root
run 30-screen-after $R/wt-head
