#!/usr/bin/env bash
# Replay mfup1 (Approved first-entry and remaining zero-space facts plus owner move; branch lean/mig1-followup-api, stacked on campaign after approved readers): its downstream closure (401 modules),
# fresh .oleans into oleans-mfup1, a copy of oleans-mac4, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-followup"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mfup1.txt"
LOG="$S/fills/replay/replay-mfup1.log"
PINS="TCSlib/Complexity/TuringMachine/Build/Catalog.lean:cac399b0a0c245a68498cf71001a3bb410cdc731
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:af1b70fb848bfae21f7447ca1151d2a6f823e526
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:e3573774d715f1a5d9c5bfbb2879babb34bbe77b
TCSlib/Complexity/TuringMachine/Encoding.lean:184022251fb5edc240b7a9fde6d98b0dd8160741
TCSlib/Complexity/TuringMachine/Finite.lean:405f6d71fc719cb85be376b0949715fae6c1c485"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/mig1-followup-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3023dc1408c3d216fc07a7cbba9ae30135b861ed HEAD || { echo "precheck: the head must contain campaign after approved readers; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3023dc1408c3d216fc07a7cbba9ae30135b861ed HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after approved readers must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mra2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "401" ] || { echo "precheck: the replay list must have 401 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mfup1" ] && { echo "precheck: $S/oleans-mfup1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac4" ] || { echo "precheck: oleans-mac4 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-mac4" "$S/oleans-mfup1" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mfup1 at $(git rev-parse --short HEAD): Approved first-entry and remaining zero-space facts plus owner move ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mfup1"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-mfup1 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"; sst=$?
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
# the exit status: nonzero unless every listed module passed and the static check found no mismatch
tail -1 "$LOG" | grep -qx "# modules=401 failed=0" || { echo "replay: a module failed, or the count is not 401" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
