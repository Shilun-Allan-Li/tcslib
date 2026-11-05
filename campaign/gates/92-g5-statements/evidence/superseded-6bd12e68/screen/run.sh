#!/bin/bash
D=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/g5ps/screen
until mkdir /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen 2>/dev/null; do sleep 30; done
trap 'rmdir /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen' EXIT
for n in base head; do
  pop=$(grep -v '^#' $D/population.txt | while read f; do [ -e $D/$n/$f ] && echo $f; done)
  ( cd $D/$n && nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $pop ) > $D/screen-$n.txt 2>&1
  echo "$n exit $?" >> $D/status.txt
done
