#!/usr/bin/env bash
# guarded_check.sh <module> <log>: run check.py; kill the lean process if it runs > 110 s.
wt=/home/user/wt-bp; mod="$1"; log="$2"
python3 -I /home/user/work/tools/check.py $wt "$mod" "$log" > /tmp/guard.$$ 2>&1 &
pid=$!
while kill -0 $pid 2>/dev/null && ! pgrep -f "tcslib-check-oleans/$mod.olean" >/dev/null; do sleep 1; done
for i in $(seq 1 110); do kill -0 $pid 2>/dev/null || break; sleep 1; done
if kill -0 $pid 2>/dev/null; then pkill -f "tcslib-check-oleans/$mod.olean"; echo "GUARD: killed $mod after 110 s"; fi
wait $pid; head -40 /tmp/guard.$$; rm -f /tmp/guard.$$
