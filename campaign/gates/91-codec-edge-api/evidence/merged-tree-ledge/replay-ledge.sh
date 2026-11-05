#!/usr/bin/env bash
# Replay ledge (#184 (the codec's edge mode) merged with the campaign after #182; branch lean/codec-edge, stacked on the campaign tip after #182): its downstream closure (61 modules),
# fresh .oleans into oleans-ledge, a copy of oleans-larm2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-edge"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-ledge.txt"
LOG="$S/fills/replay/replay-ledge.log"
PINS="TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean:b99e64615f92db5a9272121acea0d55a8b3153d6
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:7e1d6fd27ba62095f9b129ff32d5161400754a30
TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean:802337187a4da619618956807434520fd1b4539e
TCSlib/Complexity/SpaceComplexity/Codec/Machine.lean:b9557f7c837b75e44e1ee1164e90217670f2052f
TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean:5f705433291795264cfa997eb1229e6cb678be9d
TCSlib/Complexity/SpaceComplexity/Codec/Run.lean:84cd5a6ba4fd0cd67b673b5a2af13a5b398c2695
TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:9c5c46b8c54dab7b3b71c0ee24498f7db978bc93"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/codec-edge 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0ae63311e075f444ab0370ef61a1fd879878abce HEAD || { echo "precheck: the head must contain the campaign tip after #182; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0ae63311e075f444ab0370ef61a1fd879878abce HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #182 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-larm2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "61" ] || { echo "precheck: the replay list must have 61 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-ledge" ] && { echo "precheck: $S/oleans-ledge already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-larm2" ] || { echo "precheck: oleans-larm2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-larm2" "$S/oleans-ledge" || exit 1
cd "$WT" || exit 1
{ echo "# replay-ledge at $(git rev-parse --short HEAD): #184 (the codec's edge mode) merged with the campaign after #182 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-ledge"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-ledge nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=61 failed=0" || { echo "replay: a module failed, or the count is not 61" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
