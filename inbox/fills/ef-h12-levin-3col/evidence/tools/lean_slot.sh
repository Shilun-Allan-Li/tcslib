#!/usr/bin/env bash
# Run scripts/lean_check_tree.sh for one module while holding one of the shared
# pool's slot locks (/home/user/work/pool-slots/slot{0..N-1}); N = pool size.
# Usage: TCSLIB_OLEANS=<tree> lean_slot.sh <repo-root> <module-without-.lean>
set -u
N=$(cat /home/user/work/pool-slots/SIZE 2>/dev/null || echo 3)
root="$1"; mod="$2"
while true; do
  for i in $(seq 0 $((N-1))); do
    exec 9>"/home/user/work/pool-slots/slot$i"
    if flock -n 9; then
      echo "[slot $i] $(date -u +%FT%TZ) start $mod (tree ${TCSLIB_OLEANS:-default})" >> /home/user/work/pool-slots/usage.log
      cd "$root" && PATH="$HOME/.elan/bin:$PATH" bash scripts/lean_check_tree.sh "$mod"
      rc=$?
      echo "[slot $i] $(date -u +%FT%TZ) end $mod rc=$rc" >> /home/user/work/pool-slots/usage.log
      exit $rc
    fi
    exec 9>&-
  done
  sleep 2
done
