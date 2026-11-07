#!/usr/bin/env bash
# Replay mmig1 (MIG1 draft foundation proof migration; branch lean/mig1-mega-landing, stacked on campaign after separation consumer): its downstream closure (394 modules),
# fresh .oleans into oleans-mmig1, a copy of oleans-mac3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-epad"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mmig1.txt"
LOG="$S/fills/replay/replay-mmig1.log"
PINS="TCSlib/Complexity/ClassP/TimeConstructible.lean:1b75ba4be98ee5d668c43bbc3e39d2a654277dab
TCSlib/Complexity/RAMSimulation/WordSize.lean:14bd24ba8e70c2cfd59fc32041eb18d2f695a07b
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8f7f7afaee878c26944f787b83d2ff697379d7cd
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:e08d31000ec29acbb18caae0150eca304152ccc8
TCSlib/Complexity/TuringMachine/Build/Loop.lean:6e3e74fc8880c4f3dd123637ee6bbb660bc92a56
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:bd3ac0a1acb34954675feb590621bd3bae8ea77e
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:03341e89975ac823406eb6db2b25bd187689d557
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:123a5538616a3456ac3bcc2c7c4b67abdc3f4eea
TCSlib/Complexity/TuringMachine/Composition.lean:d8a0abb9203da554e33f6906f8577d6dec561e4d
TCSlib/Complexity/TuringMachine/Encoding.lean:4fb2e649ec51133e20d000a416f5c26bebbefd2b
TCSlib/Complexity/TuringMachine/Simulation.lean:5f673d7537e7f3c0aa5b8d4f8ff611b0e9344046"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/mig1-mega-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 16401686e1b4d26f1533511faff8dd1b9bc6ad5f HEAD || { echo "precheck: the head must contain campaign after separation consumer; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 16401686e1b4d26f1533511faff8dd1b9bc6ad5f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after separation consumer must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mlin2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "394" ] || { echo "precheck: the replay list must have 394 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mmig1" ] && { echo "precheck: $S/oleans-mmig1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac3" ] || { echo "precheck: oleans-mac3 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
