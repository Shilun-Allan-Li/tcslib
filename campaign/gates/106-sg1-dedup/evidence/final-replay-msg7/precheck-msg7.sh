#!/usr/bin/env bash
# Replay msg7 (Final public raw on-image contract repoint; branch lean/dedup-sg1, stacked on passed MSG6 source): its downstream closure (2 modules),
# fresh .oleans into oleans-msg7, a copy of oleans-msg6, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-msg7.txt"
LOG="$S/fills/replay/replay-msg7.log"
PINS="TCSlib/Complexity/ClassNP/Tautology.lean:43f4b62bf7603c4c046cc23990494bc95ee72c5c"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 63a3ce018e96c8c114b9c82f8d5fce6021c7d03c HEAD || { echo "precheck: the head must contain passed MSG6 source; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 63a3ce018e96c8c114b9c82f8d5fce6021c7d03c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from passed MSG6 source must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-msg6.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg7" ] && { echo "precheck: $S/oleans-msg7 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-msg6" ] || { echo "precheck: oleans-msg6 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED
exit 0
