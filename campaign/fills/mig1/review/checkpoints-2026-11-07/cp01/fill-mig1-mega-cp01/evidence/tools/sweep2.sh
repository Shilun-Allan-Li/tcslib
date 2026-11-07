#!/usr/bin/env bash
# sweep.sh <order file> <log dir> : compile each module in order through scripts/lean_check_tree.sh
# (one Lean process at a time, nice -n 10), logging start/end, max RSS, exit, raw output.
# Stops at the first failing module.
. /work/mig1/env.sh
ORDER=$1; LD=$2; mkdir -p "$LD/raw"; S="$LD/summary.log"
cd "$TCSLIB_REPO" || exit 1
echo "# sweep of $(wc -l < "$ORDER") modules at $(git rev-parse HEAD) dirty=$(git status --porcelain -- TCSlib | wc -l) start $(date -u +%FT%TZ)" >> "$S"
n=0
while read -r m; do
  [ -z "$m" ] && continue
  f="$LD/raw/$(echo "$m" | tr '/' '.').out"; t0=$(date -u +%FT%TZ); s0=$(date +%s)
  /work/mig1/withslot.sh /usr/bin/time -v -o "$f.time" nice -n 10 bash scripts/lean_check_tree.sh "$m" > "$f" 2>&1; st=$?
  rss=$(awk -F': ' '/Maximum resident/{print $2}' "$f.time")
  e=$(grep -c 'error:' "$f"); w=$(grep -c "declaration uses 'sorry'" "$f")
  echo "$m start=$t0 end=$(date -u +%FT%TZ) secs=$(( $(date +%s) - s0 )) maxrss_kb=$rss exit=$st errors=$e sorry_warnings=$w" >> "$S"
  n=$((n+1))
  if [ $st -ne 0 ]; then echo "# STOPPED at $m (exit $st) after $n modules $(date -u +%FT%TZ)" >> "$S"; exit 1; fi
done < "$ORDER"
echo "# modules=$n failed=0 end $(date -u +%FT%TZ)" >> "$S"
