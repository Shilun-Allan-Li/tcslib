#!/usr/bin/env bash
# Shared Lean pool: acquire one of 3 slots (flock), then run scripts/lean_check_tree.sh <module>
# in the current repo with the caller's TCSLIB_OLEANS. Usage: lean_pool.sh <module-path-without-.lean>
export PATH=$HOME/.elan/bin:$PATH
while true; do
  for s in /home/user/work/pool/s1 /home/user/work/pool/s2 /home/user/work/pool/s3; do
    exec {fd}>"$s"
    if flock -n "$fd"; then
      echo "# pool slot $s pid=$$ module=$1 oleans=$TCSLIB_OLEANS $(date -u +%FT%TZ)" >> /home/user/work/ev/logs/pool.log
      /usr/bin/time -v bash scripts/lean_check_tree.sh "$1"; rc=$?
      flock -u "$fd"; exit $rc
    fi
    exec {fd}>&-
  done
  sleep 1
done
