#!/usr/bin/env bash
# chk.sh <module path without .lean> : check one module in the S1 worktree against postland-oleans
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
cd $SP/wt-shared-s1
m="$1"; log=$SP/shared-s1/logs/$(echo "$m" | tr / _).log
s=$(date +%s)
PATH="$HOME/.elan/bin:$PATH" TCSLIB_OLEANS=$SP/postland-oleans bash scripts/lean_check_tree.sh "$m" > "$log" 2>&1 &
pid=$!; echo "$pid $m" >> $SP/s1work/pids.txt
wait $pid; rc=$?
echo "[rc=$rc time=$(( $(date +%s)-s ))s]" >> "$log"
grep -E "error|FAIL|sorry" "$log" | head -30; tail -1 "$log"
exit $rc
