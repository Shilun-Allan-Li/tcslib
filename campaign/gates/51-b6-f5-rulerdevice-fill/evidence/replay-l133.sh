#!/usr/bin/env bash
# Replay l133 (PR #133, the ruler device boundary test (B6 F5 phase 1); branch lean/b6-f5-partial, stacked on the campaign tip after #132 (e9e97970)): its downstream closure (4 modules),
# fresh .oleans into oleans-l133, a copy of oleans-l132b, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-f5land"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-l133.txt"
LOG="$S/fills/replay/replay-l133.log"
PINS="TCSlib/Complexity/TuringMachine/Build/InputDevice.lean:7e6e4574b730bad437d264c9fc56297374dff154"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/b6-f5-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor e9e97970fb4dbe587b1758e8d3fb4a523d6cd24e HEAD || { echo "precheck: the head must contain the campaign tip after #132 (e9e97970); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only e9e97970fb4dbe587b1758e8d3fb4a523d6cd24e HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #132 (e9e97970) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-l132b.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "4" ] || { echo "precheck: the replay list must have 4 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-l133" ] && { echo "precheck: $S/oleans-l133 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-l132b" ] || { echo "precheck: oleans-l132b is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-l132b" "$S/oleans-l133" || exit 1
cd "$WT" || exit 1
{ echo "# replay-l133 at $(git rev-parse --short HEAD): PR #133, the ruler device boundary test (B6 F5 phase 1) ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-l133"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-l133 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
