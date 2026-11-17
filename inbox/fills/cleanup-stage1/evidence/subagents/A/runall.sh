#!/bin/bash
# Sequential wtcheck driver for sub-agent A (one wtcheck at a time; continues after a failure).
N=$1; shift
cd /home/user/s1/wt-a
export PATH=$HOME/.elan/bin:$PATH
for t in "$@"; do
  echo "=== START $t $(date -u +%FT%TZ)"
  python3 -I /home/user/s1/tools/wtcheck.py --wt /home/user/s1/wt-a --tree /home/user/s1/oleans/a \
    --log /home/user/s1/evidence/subagents/A/logs --target "$t"
  echo "=== END $t rc=$? $(date -u +%FT%TZ)"
done
echo "=== ALLDONE"
