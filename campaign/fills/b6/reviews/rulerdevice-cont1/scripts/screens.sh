#!/usr/bin/env bash
# Run the v3 copy-text screen on the brief's 12-file population at the base and at the head, one
# at a time, under nice -n 10, each only when no other copy-text screen runs.
S=$S
R=$S/review/f5-cont1-fill
P=campaign/fills/b6/inputs/b6-fill-rulerdevice-cont1
run() { # $1 worktree, $2 out
  while pgrep -f copy-text-screen-v3 >/dev/null; do sleep 15; done
  cd "$R/$1" || exit 1
  t0=$(date +%s)
  nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' $R/wt-base/$P/screen-population.txt) > "$2" 2> "$2.err"
  echo "rc=$? $(( $(date +%s) - t0 )) s $(date '+%F %T') at $(git rev-parse --short HEAD) in $1" > "$2.status"
}
run wt-base $R/out/31-screen-before.txt
run wt-head $R/out/32-screen-after.txt
echo done
