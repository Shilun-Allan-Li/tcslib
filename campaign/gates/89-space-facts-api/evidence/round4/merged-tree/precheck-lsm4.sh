#!/usr/bin/env bash
# Replay lsm4 (#181 round 4; branch lean/logspace-move, stacked on the campaign tip after #176): its downstream closure (137 modules),
# fresh .oleans into oleans-lsm4, a copy of oleans-leqc3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-ls1"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lsm4.txt"
LOG="$S/fills/replay/replay-lsm4.log"
PINS="TCSlib/Complexity/Randomized/BPLInP.lean:7852de457f178254f906fa04fc20edd8a0bf548f
TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean:ce34fbdcc1d213e0113acc22f02bc26c3f951842
TCSlib/Complexity/SpaceComplexity/Basic.lean:0bf0cf32885f0fb6e468ca6c57a3319e0d48b484
TCSlib/Complexity/SpaceComplexity/Constructible.lean:b629cc8f04d881fb461804ca0d6c6f9aac6a5bef
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean:7fa88231af8724d95c04deebb1880d334ff530ec
TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean:46e38faf9114296504ec5e5469760663426e4c98
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean:490cfb042a8072f95faaa2e260f199980d987eb8
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean:f25b356f377e838c4f48fb25a6417df840c3861d
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean:52645a402e93d26edd029f5ee8eb957a900a5ed7
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean:3dd1bdec000f90a0f00aa0906a5bce522048de25
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean:821ba9472b12cd30fb59cbc90a10746f32dbe7d7
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace.lean:9a51e01883a85374cef680bcca8cee5663a68ad3
TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean:eb600666daa7d7887ef98f57f84f0ed3311d7fac
TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean:cfc4df3690898ea498c93f74310e6d9cca88883e"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/logspace-move 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 109d1158cf5f20e1a45e76599acc050802333a13 HEAD || { echo "precheck: the head must contain the campaign tip after #176; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 109d1158cf5f20e1a45e76599acc050802333a13 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #176 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-leqc3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "137" ] || { echo "precheck: the replay list must have 137 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lsm4" ] && { echo "precheck: $S/oleans-lsm4 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-leqc3" ] || { echo "precheck: oleans-leqc3 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
