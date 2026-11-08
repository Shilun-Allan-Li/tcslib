#!/usr/bin/env bash
# Replay msg5 (SG1 sixteen canonical proof repoints and approved prefix import; branch lean/dedup-sg1, stacked on campaign after approved readers): its downstream closure (329 modules),
# fresh .oleans into oleans-msg5, a copy of oleans-mac4, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-msg5.txt"
LOG="$S/fills/replay/replay-msg5.log"
PINS="TCSlib/Complexity/ClassNP/SAT.lean:00701cefd55eb3cfdcde9adf9d2d8b7f9001bc8c
TCSlib/Complexity/ClassNP/Tautology.lean:44e3f879ced36807d3b82bd75996ea8ad7ceafed
TCSlib/Complexity/CookLevin/Hardness.lean:8b31498fe253e34853015c9e7a81fb3fa1aa6873
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:b2beab0b25899e955adc0117b87abf4fe9fe8f85
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:560e6cb050ee97872beafd80c417a98eb296f600"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 6860be5977689d7e50a92aebf9c2d97f0699c0c8 HEAD || { echo "precheck: the head must contain campaign after approved readers; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 6860be5977689d7e50a92aebf9c2d97f0699c0c8 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after approved readers must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mra2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "329" ] || { echo "precheck: the replay list must have 329 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg5" ] && { echo "precheck: $S/oleans-msg5 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac4" ] || { echo "precheck: oleans-mac4 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED
exit 0
