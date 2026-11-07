#!/usr/bin/env bash
# chk.sh <tag> <module>...: compile modules (writing oleans into $TCSLIB_OLEANS) one at a time via
# scripts/lean_check_tree.sh under the slot lock; raw output to $EV/logs/elab/<tag>-<module>.out
. /work/mig1/env.sh; cd "$TCSLIB_REPO"; tag=$1; shift
for m in "$@"; do
  f="$EV/logs/elab/$tag-$(basename $m).out"; s0=$(date +%s)
  /work/mig1/withslot.sh /usr/bin/time -v -o "$f.time" nice -n 10 bash scripts/lean_check_tree.sh "$m" > "$f" 2>&1; st=$?
  echo "$m exit=$st errors=$(grep -c 'error:' $f) sorry=$(grep -c "declaration uses 'sorry'" $f) warnings=$(grep -c 'warning:' $f) secs=$(( $(date +%s)-s0 )) maxrss=$(awk -F': ' '/Maximum resident/{print $2}' $f.time) $(date -u +%FT%TZ)" | tee -a "$EV/logs/elab/$tag.summary"
  [ $st -ne 0 ] && { grep -A12 'error' "$f" | head -60; exit 1; }
done
exit 0
