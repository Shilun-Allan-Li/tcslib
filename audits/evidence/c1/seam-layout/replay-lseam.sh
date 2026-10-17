#!/usr/bin/env bash
# Replay for the seam-layout contract (lean/seam-layout, stacked on C1-W's landing c567568f):
# Build/SeamLayout and its downstream closure (2 modules: the new module and the TuringMachine
# facade), fresh .oleans into oleans-lseam, a copy of oleans-lc1w (C1-W's replay), via
# scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule). Run by the
# user. The precheck pins the two files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-seam"
LIST="$S/fills/replay/down-lseam.txt"
LOG="$S/fills/replay/replay-lseam.log"
PINS="TCSlib/Complexity/TuringMachine.lean:5534843832e1ee5ba5dbc4b981678f9afd12e408
TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean:58263b1d5b333f22658a8b6a06fae61f6581c5a4"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/seam-layout 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor c567568f950117d15c41226a9244f3d9f08c189a HEAD || { echo "precheck: the head must contain C1-W's head c567568f; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only c567568f950117d15c41226a9244f3d9f08c189a HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 0a5878ed must be exactly SeamLayout and the TuringMachine facade; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lc1w.log" 2>/dev/null | grep -qx "# modules=2 failed=0" || { echo "precheck: C1-W's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lseam" ] && { echo "precheck: $S/oleans-lseam already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lc1w" ] || { echo "precheck: oleans-lc1w is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lc1w" "$S/oleans-lseam" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lseam at $(git rev-parse --short HEAD): SeamLayout and its downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lseam"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lseam nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
