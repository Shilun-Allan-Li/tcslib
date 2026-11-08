#!/usr/bin/env bash
# Replay mf61 (F6 full upstream and dependent union, current campaign Lean; branch codex/f6-space-universal, stacked on complete mac4 matching #230 merge): the full upstream/dependent union (229 modules),
# fresh .oleans into oleans-mf61, a copy of oleans-mac4, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-f6"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/order-mf61.txt"
LOG="$S/fills/replay/replay-mf61.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:7ee1f78a59820d6e75baad0d06719dff6aeabcec"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/codex/f6-space-universal 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3023dc1408c3d216fc07a7cbba9ae30135b861ed HEAD || { echo "precheck: the head must contain complete mac4 matching #230 merge; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3023dc1408c3d216fc07a7cbba9ae30135b861ed HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from complete mac4 matching #230 merge must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mra2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "229" ] || { echo "precheck: the replay list must have 229 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mf61" ] && { echo "precheck: $S/oleans-mf61 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac4" ] || { echo "precheck: oleans-mac4 is missing; nothing copied" >&2; exit 2; }
cp -cR "$S/oleans-mac4" "$S/oleans-mf61" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mf61 at $(git rev-parse --short HEAD): F6 full upstream and dependent union, current campaign Lean ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mf61"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-mf61 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=229 failed=0" || { echo "replay: a module failed, or the count is not 229" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
