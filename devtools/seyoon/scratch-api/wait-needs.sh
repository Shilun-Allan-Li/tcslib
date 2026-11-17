#!/usr/bin/env bash
# wait-needs.sh <needs file>: wait until every module listed is logged exit=0 in the cloud0
# bootstrap log, or the bootstrap stops, completes, or dies. Prints the outcome.
. "${TCSLIB_SCRATCH:?set TCSLIB_SCRATCH}/env.sh"
L=$TCSLIB_SCRATCH/fills/replay/bootstrap-oleans-cloud0.log
while true; do
  miss=$(grep -v -x -F -f <(grep ' exit=0 errors=' $L | cut -d' ' -f1) "$1" | wc -l)
  [ "$miss" -eq 0 ] && { echo "READY: all of $(wc -l < "$1") logged; $(date +%H:%M)"; exit 0; }
  grep -q '^# stopped' <(tail -3 $L) && { echo "STOPPED: $(tail -1 $L)"; exit 1; }
  pgrep -f 'bootstrap_par.py wt-hk oleans-cloud0' >/dev/null || { echo "NOT RUNNING ($miss missing)"; exit 2; }
  sleep 20
done
