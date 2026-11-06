#!/usr/bin/env bash
# Replay lh3 (#218, H landing with the RN-1 re-points, on the campaign after #211; branch lean/b6h-landing, stacked on the campaign after #211 (oleans-lcamp5)): its downstream closure (2 modules),
# fresh .oleans into oleans-lh3, a copy of oleans-lcamp5, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-h"
LIST="/home/user/tcslib-scratch/fills/replay/down-lh3.txt"
LOG="$S/fills/replay/replay-lh3.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:72303077a41ed13583ea80d6cef35b4d1b3304fb"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/b6h-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor b46bdb46c7479f231408f4330644d09f8ebfb1cd HEAD || { echo "precheck: the head must contain the campaign after #211 (oleans-lcamp5); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only b46bdb46c7479f231408f4330644d09f8ebfb1cd HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #211 (oleans-lcamp5) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lg8.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lh3" ] && { echo "precheck: $S/oleans-lh3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp5" ] || { echo "precheck: oleans-lcamp5 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp5" "$S/oleans-lh3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lh3 at $(git rev-parse --short HEAD): #218, H landing with the RN-1 re-points, on the campaign after #211 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lh3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lh3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
