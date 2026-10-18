#!/usr/bin/env bash
# Replay lu2s (U2-S partial landing: UniversalK, SelfUniversal and the TuringMachine facade; branch lean/u2s-partial, stacked on the campaign tip 018233ab): its downstream closure (3 modules),
# fresh .oleans into oleans-lu2s, a copy of oleans-lx2b, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-u2s"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lu2s.txt"
LOG="$S/fills/replay/replay-lu2s.log"
PINS="TCSlib/Complexity/TuringMachine/UniversalK.lean:50123141daecb5cd740fce9f8c559c4194f2dd15"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/u2s-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 018233abfbd077729492a784033dbbafb5551890 HEAD || { echo "precheck: the head must contain the campaign tip 018233ab; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 018233abfbd077729492a784033dbbafb5551890 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip 018233ab must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lx2b.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "3" ] || { echo "precheck: the replay list must have 3 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lu2s" ] && { echo "precheck: $S/oleans-lu2s already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lx2b" ] || { echo "precheck: oleans-lx2b is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lx2b" "$S/oleans-lu2s" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lu2s at $(git rev-parse --short HEAD): U2-S partial landing: UniversalK, SelfUniversal and the TuringMachine facade ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lu2s"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lu2s nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
