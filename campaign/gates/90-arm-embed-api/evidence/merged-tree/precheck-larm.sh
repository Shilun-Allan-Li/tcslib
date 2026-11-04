#!/usr/bin/env bash
# Replay larm (#182; branch lean/arm-embed, stacked on the campaign tip after #176): its downstream closure (138 modules),
# fresh .oleans into oleans-larm, a copy of oleans-leqc3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-sav"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-larm.txt"
LOG="$S/fills/replay/replay-larm.log"
PINS="TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean:fca167dd9670621605f06cec5d3ca33d2bcfc361
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean:50a76150d3f147df9555241006d9855248d2d7c7
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean:edb73d3c81715e2732d8e2bfbc08180c223f14a2
TCSlib/Complexity/SpaceComplexity/Machines/Program.lean:617bae27a7b301e33390169163e86d08b85b8810
TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean:9d0ae0d3ac4c90401f5ded53c89e86336f5f73d1"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/arm-embed 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 5d2a16e6e409020bc0baeb47d4955ef077609bba HEAD || { echo "precheck: the head must contain the campaign tip after #176; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 5d2a16e6e409020bc0baeb47d4955ef077609bba HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #176 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-leqc3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "138" ] || { echo "precheck: the replay list must have 138 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-larm" ] && { echo "precheck: $S/oleans-larm already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-leqc3" ] || { echo "precheck: oleans-leqc3 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
