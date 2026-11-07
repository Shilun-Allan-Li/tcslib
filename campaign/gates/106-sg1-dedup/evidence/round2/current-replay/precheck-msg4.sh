#!/usr/bin/env bash
# Replay msg4 (SG-1 cut-proof repair current merged tree; branch lean/dedup-sg1, stacked on campaign after separation consumer): its downstream closure (329 modules),
# fresh .oleans into oleans-msg4, a copy of oleans-mac3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-msg4.txt"
LOG="$S/fills/replay/replay-msg4.log"
PINS="TCSlib/Complexity/ClassNP/SAT.lean:744ffdd46da65b0d7bda69cd7269cfc934a260b4
TCSlib/Complexity/ClassNP/Tautology.lean:44e3f879ced36807d3b82bd75996ea8ad7ceafed
TCSlib/Complexity/CookLevin/Hardness.lean:70c09f23b3769906f846f6ac4aadc553b819557e
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:b2beab0b25899e955adc0117b87abf4fe9fe8f85
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:560e6cb050ee97872beafd80c417a98eb296f600"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor e3adffac67377a8b6e23bed74bfdbb44a123dd86 HEAD || { echo "precheck: the head must contain campaign after separation consumer; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only e3adffac67377a8b6e23bed74bfdbb44a123dd86 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after separation consumer must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mlin2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "329" ] || { echo "precheck: the replay list must have 329 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg4" ] && { echo "precheck: $S/oleans-msg4 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac3" ] || { echo "precheck: oleans-mac3 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
