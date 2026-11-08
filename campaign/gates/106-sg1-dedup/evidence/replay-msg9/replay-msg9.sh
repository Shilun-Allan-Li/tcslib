#!/usr/bin/env bash
# Replay msg9 (Actual merged F6 two-module tail; original full replay remains separately pinned; branch lean/dedup-sg1, stacked on the whole passed msg8 source plus Seyoon-merged F6): its downstream closure (2 modules),
# fresh .oleans into oleans-msg9, a copy of oleans-msg8, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/order-msg9.txt"
LOG="$S/fills/replay/replay-msg9.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:b9a7162841b98bdab13be5c03ae48e1954fa16c9"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 078263a74fe90b92aa6228cf20e43726138afbe6 HEAD || { echo "precheck: the head must contain the whole passed msg8 source plus Seyoon-merged F6; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 078263a74fe90b92aa6228cf20e43726138afbe6 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the whole passed msg8 source plus Seyoon-merged F6 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-msg8.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg9" ] && { echo "precheck: $S/oleans-msg9 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-msg8" ] || { echo "precheck: oleans-msg8 is missing; nothing copied" >&2; exit 2; }
cp -cR "$S/oleans-msg8" "$S/oleans-msg9" || exit 1
cd "$WT" || exit 1
{ echo "# replay-msg9 at $(git rev-parse --short HEAD): Actual merged F6 two-module tail; original full replay remains separately pinned ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-msg9"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    rm -f "$S/oleans-msg9/$m.olean" "$S/oleans-msg9/$m.ilean" "$S/oleans-msg9/$m.c" "$S/oleans-msg9/$m.trace"
    out=$(TCSLIB_OLEANS=$S/oleans-msg9 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=2 failed=0" || { echo "replay: a module failed, or the count is not 2" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
