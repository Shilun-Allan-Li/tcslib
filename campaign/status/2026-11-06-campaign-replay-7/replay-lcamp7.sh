#!/usr/bin/env bash
# Replay lcamp7 (the campaign after #214 and #223 (merged); branch complexity/arora-barak-ch3-4, stacked on the campaign after #218, #219 (oleans-lcamp6)): its downstream closure (120 modules),
# fresh .oleans into oleans-lcamp7, a copy of oleans-lcamp6, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-camp"
LIST="/home/user/tcslib-scratch/fills/replay/down-lcamp7.txt"
LOG="$S/fills/replay/replay-lcamp7.log"
PINS="TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean:925274f9fedf528e9ee9deb63ce7ffbf1d8998a1
TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean:e7b6cc11cb358bbef7d7b9cc26f0d5b1255fe620
TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean:299c4ffec36915a9e342335b88cb7cd7b0de86dd
TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean:d856700cf0e1ee63a922ae0e94e1d8df185129f6
TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct.lean:3ccc6d78a2352ac676258ce0a9ae22bb70529091
TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean:c718cf5d31595ba654cd628f70588f2c288f2e95
TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean:5321df8c3fdadcfaabcae11d35b54ff6527b8092
TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean:5424f86436f2fddaad2ceddd85979a12ac863894
TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:587531b82a5d66d5a38b5e48a0e018828ecc55b3
TCSlib/Complexity/SpaceComplexity/Codec/Engine.lean:8b68ee89b751f4d9da68a1a6bc7736659b8969fb
TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean:218a014c05d63e482fe930b14c459c9792497880
TCSlib/Complexity/SpaceComplexity/Codec/Layout2.lean:2f631b1c136b3735538c5350c1bd5ee256015d67
TCSlib/Complexity/SpaceComplexity/Codec/StepDecider.lean:6f569d0ba08f97a31e94506b31ac887548d42bb9
TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean:94d1a57a8bcd11651ef220e21bd2f477c7e28cbc
TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean:b2c89b6c5957b23ec11c2c1d6e2c87f2ed47852d
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean:1de162d3ce821177c30bdb461e289f724c33169a
TCSlib/Complexity/SpaceComplexity/ExpBFS/Relax.lean:885e154a54df71f0bb4fcb91f5ce4e39086dbeab
TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean:a0ad92fd7809b92bafb5528ccd9ef5c3f8948059
TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean:c71c3ced7be7e9f4b9f77e4674becec18a3d6426
TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean:7c5f7fcca1d6c6e5292f6705b884ebfdd9121883
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:9111e2069624f206efa49610e4b4ad4b38d095cf
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean:afccaa998fa745c4eba9bdaa1a68b51c4ed33aab
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRun.lean:4c874f6747c91e328c6a50355d4053fad091065e
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean:759c78fb52b8a7b0b6a6786917db5547e0d0b75f
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:49beea19a99b315091069373112b8a2b99713cbd
TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean:8e7259576c51690ce2024472c2a8bbce44f8826b
TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean:1432573fdada8c2e7149a110a7d71d8f9cf72e01
TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean:5a07e46264af96af733cca8404659a1a4326fa2d
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean:0f411942adafd94ab6e92c4c196825214aba265a
TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean:2f9b774462277ff908e5fa40486eda9ed1783edd
TCSlib/Complexity/SpaceComplexity/Machines/NARMExample.lean:32e9bab1670c246a10054db0cb26cd394da4ca37
TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean:08b9be44ad0d637d77f8965093c91fc426e46244
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean:9a280e6d45439615a14551dd13ddc557921d13ec
TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean:8d9bc731cd3c5705990a686b8adb092217a6ce69
TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean:4994472c82fab4b353e957a5d2c1c5303e9b926d
TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean:e49c5ec465ef7196982bf3a373575710c41a51d6
TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean:e7c3700e7c839378a1a314dac4d4b5c9f6c02f71
TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean:7e3ed8fb6781c935898df4166fc1e632dedd33d0
TCSlib/Complexity/TimeHierarchy.lean:50904f92525c9220f4bf7fc19a972b6e645a6db5
TCSlib/Complexity/TimeHierarchy/Diagonal.lean:473d72f35a519e230accd2406f48bdbcd9e7d428"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "72fcfbef3c1deb331aedc95d4a158a9ed4c56524" ] || { echo "precheck: $WT is not at 72fcfbef3c1deb331aedc95d4a158a9ed4c56524" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 7027deadb4f232d5765414c00a7550fbd93c80b3 HEAD || { echo "precheck: the head must contain the campaign after #218, #219 (oleans-lcamp6); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 7027deadb4f232d5765414c00a7550fbd93c80b3 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #218, #219 (oleans-lcamp6) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp6.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "120" ] || { echo "precheck: the replay list must have 120 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcamp7" ] && { echo "precheck: $S/oleans-lcamp7 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp6" ] || { echo "precheck: oleans-lcamp6 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp6" "$S/oleans-lcamp7" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcamp7 at $(git rev-parse --short HEAD): the campaign after #214 and #223 (merged) ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcamp7"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcamp7 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=120 failed=0" || { echo "replay: a module failed, or the count is not 120" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
