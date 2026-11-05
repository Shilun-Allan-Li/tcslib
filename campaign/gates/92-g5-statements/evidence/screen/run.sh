#!/bin/bash
D=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/g5ps/screens2
until mkdir /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen 2>/dev/null; do sleep 30; done
trap 'rmdir /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen' EXIT
scr() { pop=$(grep -v '^#' $D/pop-$2.txt | while read f; do [ -e $D/$1/$f ] && echo $f; done); ( cd $D/$1 && nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $pop ) > $D/screen-$2-$1.txt 2>&1; echo "$2 $1 exit $? $(date -u +%FT%TZ)" >> $D/status.txt; }
scr base g5; scr g5 g5; scr base cf; scr cf cf
