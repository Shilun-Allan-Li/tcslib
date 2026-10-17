#!/usr/bin/env bash
# Replay for X2 (lean/ntime-diag-bf, stacked on the G4 partial's landing 4ab012d9): BF as a
# hypothesis of exists_diagonalizer. Diagonalization/NTimeDiagonalizer and its downstream closure
# (2 modules: it and the Diagonalization facade), fresh .oleans into oleans-lx2, a copy of
# oleans-lg4c1, via scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay
# rule). Run by the user. The precheck pins NTimeDiagonalizer's blob.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-x2"
LIST="$S/fills/replay/down-lx2.txt"
LOG="$S/fills/replay/replay-lx2.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean:026b52daefb23153137fc6331d7e3e1b80aaa92f"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/ntime-diag-bf 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 4ab012d97dfa8ff13e0e07024bafe30b19743be7 HEAD || { echo "precheck: the head must contain the G4 landing 4ab012d9; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 4ab012d97dfa8ff13e0e07024bafe30b19743be7 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 0a5878ed must be exactly NTimeDiagonalizer; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lg4c1.log" 2>/dev/null | grep -qx "# modules=2 failed=0" || { echo "precheck: the G4 landing's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lx2" ] && { echo "precheck: $S/oleans-lx2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lg4c1" ] || { echo "precheck: oleans-lg4c1 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lg4c1" "$S/oleans-lx2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lx2 at $(git rev-parse --short HEAD): NTimeDiagonalizer and its downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lx2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lx2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
