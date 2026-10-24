#!/usr/bin/env bash
# Replay lf3c2 (F3 cont2's landing, the configuration-count runner; branch lean/f3c2-landing, stacked on the campaign tip after #156 (21d53053, the tree of oleans-lphl2)): its downstream closure (2 modules),
# fresh .oleans into oleans-lf3c2, a copy of oleans-lphl2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-f3c2land"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lf3c2.txt"
LOG="$S/fills/replay/replay-lf3c2.log"
PINS="TCSlib/Complexity/SpaceComplexity/WindowClock.lean:85de9ad54305cb741451c46c979ed8f57ee0e5e5"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/f3c2-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 21d53053a1c23aedf0c1d88b830845437ac897b1 HEAD || { echo "precheck: the head must contain the campaign tip after #156 (21d53053, the tree of oleans-lphl2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 21d53053a1c23aedf0c1d88b830845437ac897b1 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #156 (21d53053, the tree of oleans-lphl2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lphl2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lf3c2" ] && { echo "precheck: $S/oleans-lf3c2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lphl2" ] || { echo "precheck: oleans-lphl2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lphl2" "$S/oleans-lf3c2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lf3c2 at $(git rev-parse --short HEAD): F3 cont2's landing, the configuration-count runner ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lf3c2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lf3c2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
