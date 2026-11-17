#!/usr/bin/env bash
# Sub-agent B: run wtcheck on the remaining homes, one after the other (detached driver).
B=/home/user/s1/evidence/subagents/B
cd /home/user/s1/wt-b
export PATH=$HOME/.elan/bin:$PATH
n=$1; shift
for m in "$@"; do
  o=$B/run$(printf %02d $n)-$(basename $m).out
  python3 -I /home/user/s1/tools/wtcheck.py --wt /home/user/s1/wt-b --tree /home/user/s1/oleans/b \
    --log $B/logs --target TCSlib/$m > $o 2>&1
  echo rc=$? >> $o
  n=$((n+1))
done
echo ALLDONE >> $B/run-rest.done
