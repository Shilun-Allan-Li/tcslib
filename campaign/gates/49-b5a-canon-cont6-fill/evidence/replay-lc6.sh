#!/usr/bin/env bash
# Replay lc6 (canonizer cont6 partial landing, stacked on #130: CodeSimulator and its downstream closure; branch lean/canon-cont6-partial, stacked on #130 (U2-S landing) 0530e5c6): its downstream closure (9 modules),
# fresh .oleans into oleans-lc6, a copy of oleans-lu2s, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-c6"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lc6.txt"
LOG="$S/fills/replay/replay-lc6.log"
PINS="TCSlib/Complexity/TuringMachine/CodeSimulator.lean:a66e63c35167045e1d4d26ed21f2a59280436337"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/canon-cont6-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0530e5c60fb7c0d0f2e48734ea7768411315d293 HEAD || { echo "precheck: the head must contain #130 (U2-S landing) 0530e5c6; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0530e5c60fb7c0d0f2e48734ea7768411315d293 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #130 (U2-S landing) 0530e5c6 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lu2s.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "9" ] || { echo "precheck: the replay list must have 9 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lc6" ] && { echo "precheck: $S/oleans-lc6 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lu2s" ] || { echo "precheck: oleans-lu2s is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lu2s" "$S/oleans-lc6" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lc6 at $(git rev-parse --short HEAD): canonizer cont6 partial landing, stacked on #130: CodeSimulator and its downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lc6"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lc6 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
