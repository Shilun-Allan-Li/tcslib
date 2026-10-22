#!/usr/bin/env bash
# Run the v3 copy-text screen on the 13-file population at the overlay (before) and at the head
# (after), one at a time, under nice -n 10, each only when no other copy-text screen runs.
S=$S
R=$S/review/u2s-cont1-fill
P=campaign/fills/u2s/inputs/u2s-fill-startup-cont1
run() { # $1 worktree, $2 out
  while pgrep -f copy-text-screen-v3 >/dev/null; do sleep 15; done
  cd "$R/$1" || exit 1
  t0=$(date +%s)
  nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' $R/wt-ovl/$P/screen-population.txt) > "$2" 2> "$2.err"
  echo "rc=$? $(( $(date +%s) - t0 )) s $(date '+%F %T') at $(git rev-parse --short HEAD) in $1 ($(git status --porcelain --untracked-files=no | wc -l | tr -d ' ') modified)" > "$2.status"
}
run wt-ovl $R/out/29-screen-before.txt
run wt-head $R/out/30-screen-after.txt
echo done
