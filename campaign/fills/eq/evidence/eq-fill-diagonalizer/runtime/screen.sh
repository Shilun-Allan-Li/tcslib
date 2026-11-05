#!/usr/bin/env bash
# Run the v3 copy screen on a frozen tree: screen.sh <frozen-root> <output>
cd "$1" || exit 2
start=$(date +%s)
nice -n 10 python3 -I /home/user/tcslib/scripts/copy-text-screen-v3.py . $(cat /home/user/tcslib/evidence/screens/population.txt) > "$2"
rc=$?
echo "exit=$rc secs=$(( $(date +%s) - start ))" > "$2.meta"
