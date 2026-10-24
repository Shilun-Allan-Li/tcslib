#!/usr/bin/env bash
# Replay lrcan3 (#160, C1's replay canonizer, round 2 (gate 72 fixes), on the tree after #159; branch lean/c1-replaycanon, stacked on the campaign tip after #159 (bcd4e8e9, the tree of oleans-lphf)): its downstream closure (4 modules),
# fresh .oleans into oleans-lrcan3, a copy of oleans-lphf, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-c1land"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lrcan3.txt"
LOG="$S/fills/replay/replay-lrcan3.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:0e4ef015aa135c740652624769544a440dffe85c
TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:33ba1a4b78b3564878703126c924b810d63b7825"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/c1-replaycanon 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor aa92ea2a193eed994bcd81e77885e08db11e04f7 HEAD || { echo "precheck: the head must contain the campaign tip after #159 (bcd4e8e9, the tree of oleans-lphf); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only aa92ea2a193eed994bcd81e77885e08db11e04f7 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #159 (bcd4e8e9, the tree of oleans-lphf) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lphf.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "4" ] || { echo "precheck: the replay list must have 4 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lrcan3" ] && { echo "precheck: $S/oleans-lrcan3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lphf" ] || { echo "precheck: oleans-lphf is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lphf" "$S/oleans-lrcan3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lrcan3 at $(git rev-parse --short HEAD): #160, C1's replay canonizer, round 2 (gate 72 fixes), on the tree after #159 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lrcan3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lrcan3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
