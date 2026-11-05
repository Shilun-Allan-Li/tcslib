#!/usr/bin/env bash
# Replay larm2 (#182 merged with the campaign after #181; branch lean/arm-embed, stacked on the campaign tip after #181): its downstream closure (138 modules),
# fresh .oleans into oleans-larm2, a copy of oleans-lsm5, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-sav"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-larm2.txt"
LOG="$S/fills/replay/replay-larm2.log"
PINS="TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean:fca167dd9670621605f06cec5d3ca33d2bcfc361
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean:50a76150d3f147df9555241006d9855248d2d7c7
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean:87a15ca7072bef95d0562cb3d9a9078722fde458
TCSlib/Complexity/SpaceComplexity/Machines/Program.lean:617bae27a7b301e33390169163e86d08b85b8810
TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean:9d0ae0d3ac4c90401f5ded53c89e86336f5f73d1"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/arm-embed 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor d1ddea26b27bb57e0c9ad70b0caceed493382fc9 HEAD || { echo "precheck: the head must contain the campaign tip after #181; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only d1ddea26b27bb57e0c9ad70b0caceed493382fc9 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #181 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lsm5.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "138" ] || { echo "precheck: the replay list must have 138 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-larm2" ] && { echo "precheck: $S/oleans-larm2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lsm5" ] || { echo "precheck: oleans-lsm5 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lsm5" "$S/oleans-larm2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-larm2 at $(git rev-parse --short HEAD): #182 merged with the campaign after #181 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-larm2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-larm2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=138 failed=0" || { echo "replay: a module failed, or the count is not 138" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
