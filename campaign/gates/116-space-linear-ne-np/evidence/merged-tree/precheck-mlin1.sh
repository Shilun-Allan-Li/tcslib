#!/usr/bin/env bash
# Replay mlin1 (linear-space NP consumer; branch lean/space-linear-ne-np, stacked on campaign after E-PAD): its downstream closure (2 modules),
# fresh .oleans into oleans-mlin1, a copy of oleans-mac1, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-epad"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mlin1.txt"
LOG="$S/fills/replay/replay-mlin1.log"
PINS="TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:7cb7b5fe256f732e6ad5568621749b9ecd2136e0"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/space-linear-ne-np 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 7df0d047d501a1d08982d17d20208faf49d39131 HEAD || { echo "precheck: the head must contain campaign after E-PAD; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 7df0d047d501a1d08982d17d20208faf49d39131 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after E-PAD must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mepad1.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mlin1" ] && { echo "precheck: $S/oleans-mlin1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac1" ] || { echo "precheck: oleans-mac1 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
