#!/usr/bin/env bash
# usage: sweep.sh <listfile> <logdir> <tsv>
export PATH=$HOME/.elan/bin:$PATH
cd /workspace/fill
( while read -r m; do
    [ -z "$m" ] && continue
    lg="$2/$(echo $m | tr / .).log"
    python3 /workspace/tools/chk.py "$m" > "$lg" 2>&1; st=$?
    echo -e "$m\t$st\t$(tail -1 "$lg")" >> "$3"
    if [ $st -ne 0 ]; then echo "STOPPED at $m" >> "$3"; exit 1; fi
  done < "$1"; exit 0 ) ; echo "SWEEP-EXIT $?" >> "$3"
