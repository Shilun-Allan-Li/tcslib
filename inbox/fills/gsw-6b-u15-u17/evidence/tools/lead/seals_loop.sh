#!/usr/bin/env bash
# Run seals.py to completion (it pauses itself after ~230 s; resumable). usage: seals_loop.sh ARGS...
cd /workspace/gsw2/repo
for i in $(seq 1 60); do
  out=$(python3 -I /workspace/gsw2/tools/lead/seals.py "$@")
  echo "$out"
  echo "$out" | grep -q '^DONE' && exit 0
  echo "$out" | grep -q 'CENSUS FAILED' && exit 1
done
exit 1
