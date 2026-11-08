#!/usr/bin/env bash
# Replay msg6 (Final approved weighted-pair bound; branch lean/dedup-sg1, stacked on passed MSG5 source): its downstream closure (26 modules),
# fresh .oleans into oleans-msg6, a copy of oleans-msg5, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-msg6.txt"
LOG="$S/fills/replay/replay-msg6.log"
PINS="TCSlib/Complexity/CookLevin/Hardness.lean:04828f7da0a93ca047dc40f4e7998c8ec54ec856"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor d0c4a292e781b55617e05b33fdd423bb059fd735 HEAD || { echo "precheck: the head must contain passed MSG5 source; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only d0c4a292e781b55617e05b33fdd423bb059fd735 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from passed MSG5 source must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-msg5.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "26" ] || { echo "precheck: the replay list must have 26 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg6" ] && { echo "precheck: $S/oleans-msg6 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-msg5" ] || { echo "precheck: oleans-msg5 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-msg5" "$S/oleans-msg6" || exit 1
cd "$WT" || exit 1
{ echo "# replay-msg6 at $(git rev-parse --short HEAD): Final approved weighted-pair bound ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-msg6"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-msg6 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"; sst=$?
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
# the exit status: nonzero unless every listed module passed and the static check found no mismatch
tail -1 "$LOG" | grep -qx "# modules=26 failed=0" || { echo "replay: a module failed, or the count is not 26" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
