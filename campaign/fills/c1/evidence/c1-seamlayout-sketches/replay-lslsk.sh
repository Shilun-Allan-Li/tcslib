#!/usr/bin/env bash
# Replay lslsk (the seam layout's proof sketches (docstrings only); branch lean/c1-seamlayout-sketches, stacked on the campaign branch after #154 (99d04262, the tree of oleans-lun2)): its downstream closure (7 modules),
# fresh .oleans into oleans-lslsk, a copy of oleans-lun2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-slsk"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lslsk.txt"
LOG="$S/fills/replay/replay-lslsk.log"
PINS="TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean:a9f7d1e3936663cac853474baf66246fcee6b393"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/c1-seamlayout-sketches 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 99d04262ea00d7b01809c88e41aa651281c7af93 HEAD || { echo "precheck: the head must contain the campaign branch after #154 (99d04262, the tree of oleans-lun2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 99d04262ea00d7b01809c88e41aa651281c7af93 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign branch after #154 (99d04262, the tree of oleans-lun2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lun2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "7" ] || { echo "precheck: the replay list must have 7 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lslsk" ] && { echo "precheck: $S/oleans-lslsk already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lun2" ] || { echo "precheck: oleans-lun2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lun2" "$S/oleans-lslsk" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lslsk at $(git rev-parse --short HEAD): the seam layout's proof sketches (docstrings only) ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lslsk"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lslsk nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
