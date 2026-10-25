#!/usr/bin/env bash
# Replay lu2api (U2's API: two field-equation families, pairEncode_drop, spaceUsedByTape_eq_card; branch lean/u2-api, stacked on the campaign tip after #160 (90688cbb, the tree of oleans-lrcan3)): its downstream closure (325 modules),
# fresh .oleans into oleans-lu2api, a copy of oleans-lrcan3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-u2api"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lu2api.txt"
LOG="$S/fills/replay/replay-lu2api.log"
PINS="TCSlib/Complexity/TuringMachine/Build/InputDevice.lean:ae350de2e7ada6e6319933c9946a08b212b946b1
TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean:ec3551f1b3166f33cc89eec81065e2fad268a0a9
TCSlib/Complexity/TuringMachine/Deterministic.lean:13d5c294f8dbe8c3132ac00f85de03c39e0d0150"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/u2-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 90688cbb645fcf1ef66ff6112c83bd8f0413000b HEAD || { echo "precheck: the head must contain the campaign tip after #160 (90688cbb, the tree of oleans-lrcan3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 90688cbb645fcf1ef66ff6112c83bd8f0413000b HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #160 (90688cbb, the tree of oleans-lrcan3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lrcan3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "325" ] || { echo "precheck: the replay list must have 325 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lu2api" ] && { echo "precheck: $S/oleans-lu2api already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lrcan3" ] || { echo "precheck: oleans-lrcan3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lrcan3" "$S/oleans-lu2api" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lu2api at $(git rev-parse --short HEAD): U2's API: two field-equation families, pairEncode_drop, spaceUsedByTape_eq_card ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lu2api"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lu2api nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
