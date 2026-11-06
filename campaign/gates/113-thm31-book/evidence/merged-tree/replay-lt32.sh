#!/usr/bin/env bash
# Replay lt32 (#223, the book-form time hierarchy, on the campaign after #218/#219; branch lean/thm31-book, stacked on the campaign after #218, #219 (oleans-lcamp6)): its downstream closure (14 modules),
# fresh .oleans into oleans-lt32, a copy of oleans-lcamp6, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-t31"
LIST="/home/user/tcslib-scratch/fills/replay/down-lt32.txt"
LOG="$S/fills/replay/replay-lt32.log"
PINS="TCSlib/Complexity/TimeHierarchy.lean:50904f92525c9220f4bf7fc19a972b6e645a6db5
TCSlib/Complexity/TimeHierarchy/Diagonal.lean:654b1c51bc47e340cb1295d77edbb1ffc1c546d8"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/thm31-book 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 7a66896024c86de6399955a399faf501e04ac2f1 HEAD || { echo "precheck: the head must contain the campaign after #218, #219 (oleans-lcamp6); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 7a66896024c86de6399955a399faf501e04ac2f1 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #218, #219 (oleans-lcamp6) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp6.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "14" ] || { echo "precheck: the replay list must have 14 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lt32" ] && { echo "precheck: $S/oleans-lt32 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp6" ] || { echo "precheck: oleans-lcamp6 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp6" "$S/oleans-lt32" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lt32 at $(git rev-parse --short HEAD): #223, the book-form time hierarchy, on the campaign after #218/#219 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lt32"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lt32 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=14 failed=0" || { echo "replay: a module failed, or the count is not 14" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
