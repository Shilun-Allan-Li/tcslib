#!/usr/bin/env bash
# Replay lx2b (#126 restacked, with gate 45 minor 1: NTimeDiagonalizer and the Diagonalization facade; branch lean/ntime-diag-bf, stacked on #125 e6917ea0): its downstream closure (2 modules),
# fresh .oleans into oleans-lx2b, a copy of oleans-lg4c1b, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-x2-b"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lx2.txt"
LOG="$S/fills/replay/replay-lx2b.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean:3cdc4f33a1650df104c752f2783bf5dc734be3b3"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/ntime-diag-bf 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor e6917ea008008de856ddcb03f847a4c1ce329c02 HEAD || { echo "precheck: the head must contain #125 e6917ea0; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only e6917ea008008de856ddcb03f847a4c1ce329c02 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #125 e6917ea0 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lg4c1b.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lx2b" ] && { echo "precheck: $S/oleans-lx2b already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lg4c1b" ] || { echo "precheck: oleans-lg4c1b is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lg4c1b" "$S/oleans-lx2b" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lx2b at $(git rev-parse --short HEAD): #126 restacked, with gate 45 minor 1: NTimeDiagonalizer and the Diagonalization facade ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lx2b"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lx2b nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
