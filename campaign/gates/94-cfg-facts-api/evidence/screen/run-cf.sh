#!/bin/bash
D=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/g5ps/screens2
until mkdir /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen 2>/dev/null; do sleep 30; done
trap 'rmdir /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen' EXIT
pop=$(grep -v '^#' $D/pop-cf.txt | while read f; do [ -e $D/cf/$f ] && echo $f; done)
( cd $D/cf && nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $pop ) > $D/screen-cf-cf.txt 2>&1
echo "cf cf (3cc6c9ee) exit $? $(date -u +%FT%TZ)" >> $D/status.txt
