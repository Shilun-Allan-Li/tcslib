#!/usr/bin/env bash
# Replay for the §13d G4 continuation-1 partial's landing (lean/g4-cont1-partial, stacked on the
# seam-layout contract 0355da56): Build/ZoneRebalance and its downstream closure (2 modules: it and
# the TuringMachine facade), fresh .oleans into oleans-lg4c1, a copy of oleans-lseam, via
# scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule). Run by the
# user. The precheck pins ZoneRebalance's blob.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g4l"
LIST="$S/fills/replay/down-lg4c1.txt"
LOG="$S/fills/replay/replay-lg4c1.log"
PINS="TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:e88edbda6df8397f897962a5225895a39bd363c1"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g4-cont1-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0355da56c95a078e006fdb2d7a43d34d150c19e7 HEAD || { echo "precheck: the head must contain the seam-layout head 0355da56; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0355da56c95a078e006fdb2d7a43d34d150c19e7 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 0a5878ed must be exactly ZoneRebalance; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lseam.log" 2>/dev/null | grep -qx "# modules=2 failed=0" || { echo "precheck: the seam-layout replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg4c1" ] && { echo "precheck: $S/oleans-lg4c1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lseam" ] || { echo "precheck: oleans-lseam is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lseam" "$S/oleans-lg4c1" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg4c1 at $(git rev-parse --short HEAD): ZoneRebalance and its downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg4c1"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg4c1 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
