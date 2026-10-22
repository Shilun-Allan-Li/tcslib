#!/usr/bin/env bash
# Runs the v3 screen at the base and then at the head, one at a time, each only when no other screen runs.
R="$1"; POP="$2"
waitfree() { while pgrep -f 'copy-text-screen-v[3]' >/dev/null; do sleep 15; done; }
run() { # $1 worktree, $2 tag
  waitfree
  local s=$(date +%s)
  ( cd "$R/$1" && nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' "$POP") > "$R/out/screen-$2.txt" 2> "$R/out/screen-$2.err" )
  echo "exit $? elapsed $(( $(date +%s) - s ))s started $(date -r $s '+%H:%M:%S')" > "$R/out/screen-$2.status"
}
run wt-base before
run wt-head after
