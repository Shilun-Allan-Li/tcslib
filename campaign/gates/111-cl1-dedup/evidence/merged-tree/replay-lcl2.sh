#!/usr/bin/env bash
# Replay lcl2 (#220, CL-1, on the campaign after #216; branch lean/dedup-cl1, stacked on the campaign after #216 (oleans-lcamp3)): its downstream closure (60 modules),
# fresh .oleans into oleans-lcl2, a copy of oleans-lcamp3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-cl1"
LIST="/home/user/tcslib-scratch/fills/replay/down-lcl2.txt"
LOG="$S/fills/replay/replay-lcl2.log"
PINS="TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean:a4030d8548f65f58d232382b4ad80309c5a74dd4
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:4cbb3299b77b6e17cfcead37d250adcbdeae0c25
TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean:5555d7e8301cbda531e64f9800ebfb2f725a8c95"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-cl1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD || { echo "precheck: the head must contain the campaign after #216 (oleans-lcamp3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #216 (oleans-lcamp3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "60" ] || { echo "precheck: the replay list must have 60 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcl2" ] && { echo "precheck: $S/oleans-lcl2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp3" ] || { echo "precheck: oleans-lcamp3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp3" "$S/oleans-lcl2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcl2 at $(git rev-parse --short HEAD): #220, CL-1, on the campaign after #216 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcl2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcl2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=60 failed=0" || { echo "replay: a module failed, or the count is not 60" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
