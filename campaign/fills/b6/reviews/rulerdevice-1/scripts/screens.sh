#!/usr/bin/env bash
# Runs this review's two v3 screens one at a time, each only when no other screen runs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/b6-f5-fill
run() { # wt population out
  while pgrep -f copy-text-screen-v3 >/dev/null; do sleep 15; done
  local t0=$(date +%s)
  ( cd "$1" && nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . $(grep -v '^#' "$2") > "$3" 2> "$3.err" ); local st=$?
  echo "exit $st, $(( $(date +%s) - t0 )) s, $(date)" > "$3.status"
}
run $R/wt-base audits/evidence/b6-fill-rulerdevice/screen-population.txt $R/out/39-screen-before.txt
run $R/wt-head audits/evidence/b6-fill-rulerdevice/screen-population.txt $R/out/40-screen-after.txt
echo ALL DONE
