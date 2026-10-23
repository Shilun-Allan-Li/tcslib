#!/usr/bin/env bash
# Replay lun2 (#154, the UN landing, on the tree after #147 and #149 to #153; branch lean/un-cont1-landing, stacked on #152's head (274bdae9, the tree of oleans-lcanon7)): its downstream closure (2 modules),
# fresh .oleans into oleans-lun2, a copy of oleans-lcanon7, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-unland"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lun2.txt"
LOG="$S/fills/replay/replay-lun2.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:aca1d8e3c90aa92b4e1fecee511ba13a5cd25de8"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/un-cont1-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 274bdae9781797ed80db27971d00a1eae5df9a93 HEAD || { echo "precheck: the head must contain #152's head (274bdae9, the tree of oleans-lcanon7); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 274bdae9781797ed80db27971d00a1eae5df9a93 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #152's head (274bdae9, the tree of oleans-lcanon7) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lcanon7.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lun2" ] && { echo "precheck: $S/oleans-lun2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcanon7" ] || { echo "precheck: oleans-lcanon7 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcanon7" "$S/oleans-lun2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lun2 at $(git rev-parse --short HEAD): #154, the UN landing, on the tree after #147 and #149 to #153 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lun2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lun2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
