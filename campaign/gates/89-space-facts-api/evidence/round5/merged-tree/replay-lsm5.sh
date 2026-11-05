#!/usr/bin/env bash
# Replay lsm5 (#181 round 5; branch lean/logspace-move, stacked on the campaign tip after #176): its downstream closure (209 modules),
# fresh .oleans into oleans-lsm5, a copy of oleans-leqc3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-ls1"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lsm5.txt"
LOG="$S/fills/replay/replay-lsm5.log"
PINS="TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean:77949047f7b16d6d2b226a2708bdfc682ec2e051
TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean:0471b42cce46a9134f5ed07795050207cb051f50
TCSlib/Complexity/Randomized/BPLInP.lean:689c48a19322dc6998374f8428a6f1a9054e29ad
TCSlib/Complexity/Randomized/RandomWalkPad.lean:c98002abab943c4f28ae09194fdd8ed1c5a62485
TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean:699403b54bf17a2fa521d9525dad34b4537ade39
TCSlib/Complexity/SpaceComplexity/Basic.lean:0bf0cf32885f0fb6e468ca6c57a3319e0d48b484
TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean:ed566da263b766b9af2d25a3576e3f350a1bf6f5
TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean:a11799a4d8d6de8011a283b0c59e4e85b8367b14
TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:fc2ba916fab76bec928a9e029e881f5e2f2c6d76
TCSlib/Complexity/SpaceComplexity/Constructible.lean:b629cc8f04d881fb461804ca0d6c6f9aac6a5bef
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean:7fa88231af8724d95c04deebb1880d334ff530ec
TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean:46e38faf9114296504ec5e5469760663426e4c98
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean:e885abdadeeb4d7fd5deeb587550c91b8f5354e1
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean:f25b356f377e838c4f48fb25a6417df840c3861d
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean:a1f376ee5666fe60e3ae305b35930b9d5b1f4abf
TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean:52645a402e93d26edd029f5ee8eb957a900a5ed7
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean:3dd1bdec000f90a0f00aa0906a5bce522048de25
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean:821ba9472b12cd30fb59cbc90a10746f32dbe7d7
TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean:1a1b72c357d0e9f0a61e34a5d806533ae58a86b1
TCSlib/Complexity/SpaceComplexity/Machines/NARMLogspace.lean:9a51e01883a85374cef680bcca8cee5663a68ad3
TCSlib/Complexity/SpaceComplexity/Machines/NARMProof.lean:eb600666daa7d7887ef98f57f84f0ed3311d7fac
TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean:cfc4df3690898ea498c93f74310e6d9cca88883e
TCSlib/Complexity/SpaceComplexity/WindowClock.lean:09e189b41d16a3ec881cafb724f5fdda3f33721f
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:6338fe1464660a69309cdde631eb482e55fd8079
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:0d232852433ade293e1d7842291e877b89b72ac2"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/logspace-move 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3fb5851ce68b6dd1171b6f6899ec1f045dab6ae0 HEAD || { echo "precheck: the head must contain the campaign tip after #176; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3fb5851ce68b6dd1171b6f6899ec1f045dab6ae0 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #176 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-leqc3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "209" ] || { echo "precheck: the replay list must have 209 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lsm5" ] && { echo "precheck: $S/oleans-lsm5 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-leqc3" ] || { echo "precheck: oleans-leqc3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-leqc3" "$S/oleans-lsm5" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lsm5 at $(git rev-parse --short HEAD): #181 round 5 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lsm5"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lsm5 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=209 failed=0" || { echo "replay: a module failed, or the count is not 209" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
