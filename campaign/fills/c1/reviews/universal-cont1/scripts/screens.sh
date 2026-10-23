#!/usr/bin/env bash
# The v3 copy-text screen on the brief's 11-file population at the overlay (first edit) and at the
# head, one at a time, under nice -n 10, each only while holding $S/locks/screen.lock.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/c1-universal-cont1
P=campaign/fills/c1/inputs/c1-fill-universal-cont1
run() { # $1 worktree, $2 out
  until mkdir $S/locks/screen.lock 2>/dev/null; do sleep 15; done
  trap 'rmdir $S/locks/screen.lock 2>/dev/null' EXIT
  cd "$R/$1" || { rmdir $S/locks/screen.lock; exit 1; }
  t0=$(date +%s)
  nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' $R/wt-base/$P/screen-population.txt) > "$2" 2> "$2.err"
  rc=$?
  echo "rc=$rc $(( $(date +%s) - t0 )) s $(date '+%F %T') at $(git rev-parse --short HEAD) in $1" > "$2.status"
  rmdir $S/locks/screen.lock
  trap - EXIT
}
run wt-ovl $R/out/36-screen-before.txt
run wt-head $R/out/37-screen-after.txt
echo done
