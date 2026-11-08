#!/usr/bin/env bash
# chaincheck.sh <pr number> <chain file>: compile a PR's changed modules and everything on an
# import path between them (the chain, from chain.py) into a copy of the snapshot oleans-cloud0,
# in order, through devtools/seyoon/leanelab-o.sh (throttled; never lake build). Stops at the first
# module with a nonzero exit or an `error:` line: leanelab-o.sh does not delete the copied olean, so
# a later module would otherwise read the campaign's stale one. Logs per module, with times, under
# $TCSLIB_SCRATCH/evidence/<pr>/chain/. The overlay is $TCSLIB_SCRATCH/oleans-chk<pr> (rebuilt).
. "${TCSLIB_SCRATCH:?set TCSLIB_SCRATCH}/env.sh"
N=$1; CH=$2; S=$TCSLIB_SCRATCH; WT=$S/wt-$N; OV=$S/oleans-chk$N; E=$S/evidence/$N/chain
T=$S/wt-hk/devtools/seyoon
rm -rf "$OV" "$E"; mkdir -p "$E"
cp -R "$S/oleans-cloud0" "$OV" || exit 1
cp "$CH" "$E/order.txt"
( echo "# chain check of #$N at $(git -C "$WT" rev-parse HEAD) ($(wc -l < "$CH" | tr -d ' ') modules) into $(basename "$OV"); $(date -u)"
  while read -r m; do
    t0=$(date +%s)
    bash "$T/leanelab-o.sh" "$WT" "$OV" "$m.lean" "$OV" > "$E/$(basename "$m").out" 2>&1; st=$?
    e=$(grep -c 'error' "$E/$(basename "$m").out")
    s=$(grep -c "declaration uses 'sorry'" "$E/$(basename "$m").out")
    echo "$m exit=$st errors=$e sorry=$s secs=$(( $(date +%s) - t0 ))"
    if [ $st -ne 0 ] || grep -q 'error:' "$E/$(basename "$m").out"; then
      grep 'error' "$E/$(basename "$m").out" | head -8
      echo "# stopped at $m"; exit 1
    fi
  done < "$CH"
  echo "# chain passed; $(date -u)" ) > "$E/log.txt" 2>&1
st=$?
tail -12 "$E/log.txt"
exit $st
