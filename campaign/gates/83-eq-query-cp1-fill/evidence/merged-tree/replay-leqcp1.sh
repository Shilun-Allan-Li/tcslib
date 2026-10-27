#!/usr/bin/env bash
# Replay leqcp1 (E-Q checkpoint 1's landing, on the tree after #171; branch lean/eq-cp1-landing, stacked on the campaign tip after #171 (the tree of oleans-lwords)): its downstream closure (2 modules),
# fresh .oleans into oleans-leqcp1, a copy of oleans-lwords, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-eqland"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-leqcp1.txt"
LOG="$S/fills/replay/replay-leqcp1.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean:f965eac02e06549e8239c7476b31c0ced4f3d11b"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/eq-cp1-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 1b800c087cee5c3fc0c7b999c5f5a2871147fbe7 HEAD || { echo "precheck: the head must contain the campaign tip after #171 (the tree of oleans-lwords); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 1b800c087cee5c3fc0c7b999c5f5a2871147fbe7 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #171 (the tree of oleans-lwords) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lwords.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-leqcp1" ] && { echo "precheck: $S/oleans-leqcp1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lwords" ] || { echo "precheck: oleans-lwords is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lwords" "$S/oleans-leqcp1" || exit 1
cd "$WT" || exit 1
{ echo "# replay-leqcp1 at $(git rev-parse --short HEAD): E-Q checkpoint 1's landing, on the tree after #171 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-leqcp1"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-leqcp1 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
