#!/usr/bin/env bash
# Replay mlin2 (mlin2 current merged tree; branch lean/space-linear-ne-np, stacked on campaign after NatBits): its downstream closure (2 modules),
# fresh .oleans into oleans-mlin2, a copy of oleans-mac2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-epad"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mlin2.txt"
LOG="$S/fills/replay/replay-mlin2.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:7cb7b5fe256f732e6ad5568621749b9ecd2136e0"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/space-linear-ne-np 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3555163f40d9c101a2ef4e81407c1bda58fe5ca4 HEAD || { echo "precheck: the head must contain campaign after NatBits; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3555163f40d9c101a2ef4e81407c1bda58fe5ca4 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after NatBits must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/114-natbits-dedup/evidence/current/campaign-after-epad/replay.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mlin2" ] && { echo "precheck: $S/oleans-mlin2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac2" ] || { echo "precheck: oleans-mac2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-mac2" "$S/oleans-mlin2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mlin2 at $(git rev-parse --short HEAD): mlin2 current merged tree ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mlin2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-mlin2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=2 failed=0" || { echo "replay: a module failed, or the count is not 2" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
