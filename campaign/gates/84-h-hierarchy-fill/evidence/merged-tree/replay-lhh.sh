#!/usr/bin/env bash
# Replay lhh (H's landing, the nondeterministic time hierarchy, on the tree after #173; branch lean/h-hierarchy-landing, stacked on the campaign tip after #173 (the tree of oleans-leqcp1)): its downstream closure (2 modules),
# fresh .oleans into oleans-lhh, a copy of oleans-leqcp1, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-hland"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lhh.txt"
LOG="$S/fills/replay/replay-lhh.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:87f207da2919c058a947793dd033a49f74249f42"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/h-hierarchy-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor b2e011634208cb916294332563fd4a5b2bb4eb86 HEAD || { echo "precheck: the head must contain the campaign tip after #173 (the tree of oleans-leqcp1); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only b2e011634208cb916294332563fd4a5b2bb4eb86 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #173 (the tree of oleans-leqcp1) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-leqcp1.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lhh" ] && { echo "precheck: $S/oleans-lhh already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-leqcp1" ] || { echo "precheck: oleans-leqcp1 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-leqcp1" "$S/oleans-lhh" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lhh at $(git rev-parse --short HEAD): H's landing, the nondeterministic time hierarchy, on the tree after #173 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lhh"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lhh nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
