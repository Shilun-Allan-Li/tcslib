#!/usr/bin/env bash
# Replay lg4c3 (the G4 cont3 checkpoint landing (Build/ZoneRebalance), at the campaign's merged state after #133-#140 and #143; branch lean/g4-cont3-partial, stacked on #132's merge (e9e97970, the tree of oleans-l132b)): its downstream closure (16 modules),
# fresh .oleans into oleans-lg4c3, a copy of oleans-l132b, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g4c3land"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lg4c3.txt"
LOG="$S/fills/replay/replay-lg4c3.log"
PINS="TCSlib/Complexity/ClassNP.lean:3aff019c5c63f2e5e827e0ca3236263859d43bf1
TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:0d09053ee9ea7d7387279c1229531feab7f6a8af
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:5aad120332514e0403db2f509eae99e476446bb5
TCSlib/Complexity/SpaceComplexity/WindowClock.lean:b50cdbb19b1ac9c6018c074d25a7358c8f95b826
TCSlib/Complexity/TuringMachine.lean:9bda1ca2ef8d9d59786d37bbdbd67f1af87509bf
TCSlib/Complexity/TuringMachine/BufferWords.lean:78eaf8b7997787a0f74a7a810bb3c2e9af07e4de
TCSlib/Complexity/TuringMachine/Build/InputDevice.lean:83e1e66af89bfd814982e99338d4f9d330515616
TCSlib/Complexity/TuringMachine/Build/InputWindow.lean:9e6f659de2f27453d3fd449ef8d7120baa30e285
TCSlib/Complexity/TuringMachine/Build/Rewind.lean:1d1acb3f8c7d2f7d256bd40855d3f6d541b45dbc
TCSlib/Complexity/TuringMachine/Build/StepClock.lean:39e4a7709d3c302406f8af2261a8e925400ea243
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:1abbb8716d0450ea9b7cc10ef15e6204ed920b4a"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g4-cont3-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor e9e97970fb4dbe587b1758e8d3fb4a523d6cd24e HEAD || { echo "precheck: the head must contain #132's merge (e9e97970, the tree of oleans-l132b); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only e9e97970fb4dbe587b1758e8d3fb4a523d6cd24e HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #132's merge (e9e97970, the tree of oleans-l132b) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-l132b.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "16" ] || { echo "precheck: the replay list must have 16 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg4c3" ] && { echo "precheck: $S/oleans-lg4c3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-l132b" ] || { echo "precheck: oleans-l132b is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-l132b" "$S/oleans-lg4c3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg4c3 at $(git rev-parse --short HEAD): the G4 cont3 checkpoint landing (Build/ZoneRebalance), at the campaign's merged state after #133-#140 and #143 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg4c3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg4c3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
