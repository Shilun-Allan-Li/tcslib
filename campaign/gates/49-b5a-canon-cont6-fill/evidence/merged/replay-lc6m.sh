#!/usr/bin/env bash
# Replay lc6m (canonizer cont6 landing at the merged campaign state: CodeSimulator's downstream closure, NTimeHierarchy now included; branch lean/canon-cont6-partial, stacked on the campaign tip after #130 (3de011c1)): its downstream closure (10 modules),
# fresh .oleans into oleans-lc6m, a copy of oleans-lseam2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-c6"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lc6m.txt"
LOG="$S/fills/replay/replay-lc6m.log"
PINS="TCSlib/Complexity/TuringMachine/CodeSimulator.lean:a66e63c35167045e1d4d26ed21f2a59280436337"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/canon-cont6-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3de011c12bb05b97f572e6a7854a68f212125a4a HEAD || { echo "precheck: the head must contain the campaign tip after #130 (3de011c1); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3de011c12bb05b97f572e6a7854a68f212125a4a HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #130 (3de011c1) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lseam2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "10" ] || { echo "precheck: the replay list must have 10 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lc6m" ] && { echo "precheck: $S/oleans-lc6m already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lseam2" ] || { echo "precheck: oleans-lseam2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lseam2" "$S/oleans-lc6m" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lc6m at $(git rev-parse --short HEAD): canonizer cont6 landing at the merged campaign state: CodeSimulator's downstream closure, NTimeHierarchy now included ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lc6m"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lc6m nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
