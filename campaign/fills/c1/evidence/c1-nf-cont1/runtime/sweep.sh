#!/usr/bin/env bash
# sweep.sh <order-file> <log> [summary]
# Runs scripts/lean_check_tree.sh over each module of the order file, one at a time,
# logging start/end (UTC), wall time, max RSS and exit status per module.
set -u
source ~/.elan/env
cd /home/user/tcslib
ORDER="$1"; LOG="$2"; SUM="${3:-${2%.log}-summary.tsv}"
: > "$LOG"; printf 'module\tstart\tend\twall_s\tmaxrss_kb\texit\tsorry_warnings\n' > "$SUM"
fails=0
while read -r m; do
  [ -z "$m" ] && continue
  s=$(date -u +%FT%T.%3NZ); s0=$(date +%s.%N)
  echo "=== BEGIN $m $s" >> "$LOG"
  tf=$(mktemp)
  /usr/bin/time -v -o "$tf" bash scripts/lean_check_tree.sh "$m" > "$tf.out" 2>&1
  st=$?
  cat "$tf.out" >> "$LOG"
  e=$(date -u +%FT%T.%3NZ); e0=$(date +%s.%N)
  rss=$(awk -F': ' '/Maximum resident/{print $2}' "$tf")
  ns=$(grep -c "declaration uses 'sorry'" "$tf.out")
  echo "=== END $m $e exit=$st wall=$(python3 -c "print(round($e0-$s0,2))")s maxrss_kb=$rss" >> "$LOG"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$m" "$s" "$e" "$(python3 -c "print(round($e0-$s0,2))")" "$rss" "$st" "$ns" >> "$SUM"
  rm -f "$tf" "$tf.out"
  if [ "$st" -ne 0 ]; then fails=$((fails+1)); echo "SWEEP STOP at $m" >> "$LOG"; break; fi
done < "$ORDER"
echo "=== SWEEP DONE fails=$fails $(date -u +%FT%TZ)" >> "$LOG"
