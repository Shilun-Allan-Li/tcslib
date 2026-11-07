#!/usr/bin/env bash
# Replay msg1 (SG-1 #215; branch lean/dedup-sg1, stacked on complete Mac campaign bootstrap): its downstream closure (329 modules),
# fresh .oleans into oleans-msg1, a copy of oleans-mac0, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-msg1.txt"
LOG="$S/fills/replay/replay-msg1.log"
PINS="TCSlib/Complexity/ClassNP/Tautology.lean:44e3f879ced36807d3b82bd75996ea8ad7ceafed
TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean:ef8863adb3120d5053d2ccdef4a35a2f6ec3fee0
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:b2beab0b25899e955adc0117b87abf4fe9fe8f85
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:560e6cb050ee97872beafd80c417a98eb296f600"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 680760723d72826469d0fc294e4d7ee2ecac3e6c HEAD || { echo "precheck: the head must contain complete Mac campaign bootstrap; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 680760723d72826469d0fc294e4d7ee2ecac3e6c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from complete Mac campaign bootstrap must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/bootstrap-oleans-mac0.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "329" ] || { echo "precheck: the replay list must have 329 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg1" ] && { echo "precheck: $S/oleans-msg1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac0" ] || { echo "precheck: oleans-mac0 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
