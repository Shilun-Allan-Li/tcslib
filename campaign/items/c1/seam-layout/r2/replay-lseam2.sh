#!/usr/bin/env bash
# Replay lseam2 (#124 round 2: SeamLayout and the TuringMachine facade; branch lean/seam-layout, stacked on #126 5fd5dce8): its downstream closure (2 modules),
# fresh .oleans into oleans-lseam2, a copy of oleans-lx2b, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-seam-b"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lseam.txt"
LOG="$S/fills/replay/replay-lseam2.log"
PINS="TCSlib/Complexity/TuringMachine.lean:87ebb35302469e587c372b18cf4a14f9245d028a
TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean:d0af5ae631aa092dfaf4ebd099e7d8033d339359"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/seam-layout 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 5fd5dce80780d5cc36f53a048b024b118e619ca7 HEAD || { echo "precheck: the head must contain #126 5fd5dce8; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 5fd5dce80780d5cc36f53a048b024b118e619ca7 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #126 5fd5dce8 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lx2b.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lseam2" ] && { echo "precheck: $S/oleans-lseam2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lx2b" ] || { echo "precheck: oleans-lx2b is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lx2b" "$S/oleans-lseam2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lseam2 at $(git rev-parse --short HEAD): #124 round 2: SeamLayout and the TuringMachine facade ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lseam2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lseam2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
