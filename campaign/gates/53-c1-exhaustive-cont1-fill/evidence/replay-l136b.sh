#!/usr/bin/env bash
# Replay l136b (PR #136 with gate 53's minor-1 docstring fix, the frozen target's
# proof sketch; branch lean/c1-exhaustive-fill, stacked on the campaign tip after #132 (e9e97970)): its downstream
# closure (4 modules, the same list as l136), fresh .oleans into oleans-l136b, a copy of oleans-l132b, via
# scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule). The precheck pins the changed
# files' blobs; ExhaustiveReplay's pin is the patched blob (git hash-object of 75b2e94c's blob with
# review/gate53/fix-minor1-sketch.diff applied), the other two are l136's. Added to l136's prechecks: the head
# contains l136's head 75b2e94c, and its Lean diff from 75b2e94c is ExhaustiveReplay alone.
# The campaign tip moved after e9e97970 (#140, e2bc85eb: TuringMachine/BufferWords and the TuringMachine facade);
# neither is upstream of the four modules, so the chain from oleans-l132b still gives their merged state. If the
# campaign is merged into #136 again before this runs, the base hash, the diff set and the chain must be redone.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-e1land"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-l136.txt"
LOG="$S/fills/replay/replay-l136b.log"
PINS="TCSlib/Complexity/ClassNP.lean:3aff019c5c63f2e5e827e0ca3236263859d43bf1
TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:0d09053ee9ea7d7387279c1229531feab7f6a8af
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:5aad120332514e0403db2f509eae99e476446bb5"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/c1-exhaustive-fill 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor e9e97970fb4dbe587b1758e8d3fb4a523d6cd24e HEAD || { echo "precheck: the head must contain the campaign tip after #132 (e9e97970); nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 75b2e94cff797b887b983a0fb70abcbe1fd49212 HEAD || { echo "precheck: the head must contain l136's head (75b2e94c); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 75b2e94cff797b887b983a0fb70abcbe1fd49212 HEAD -- '*.lean')" = "TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean" ] || { echo "precheck: the Lean diff from l136's head (75b2e94c) must be ExhaustiveReplay alone; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only e9e97970fb4dbe587b1758e8d3fb4a523d6cd24e HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #132 (e9e97970) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-l132b.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "4" ] || { echo "precheck: the replay list must have 4 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-l136b" ] && { echo "precheck: $S/oleans-l136b already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-l132b" ] || { echo "precheck: oleans-l132b is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-l132b" "$S/oleans-l136b" || exit 1
cd "$WT" || exit 1
{ echo "# replay-l136b at $(git rev-parse --short HEAD): PR #136 with gate 53's docstring fix ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-l136b"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-l136b nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
