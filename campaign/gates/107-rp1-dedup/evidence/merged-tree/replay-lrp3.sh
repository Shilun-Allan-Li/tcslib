#!/usr/bin/env bash
# Replay lrp3 (#216, RP-1, merged with the campaign after #208/#212/#213; branch lean/dedup-rp1, stacked on the campaign after #208, #212, #213 (oleans-lcamp2)): its downstream closure (53 modules),
# fresh .oleans into oleans-lrp3, a copy of oleans-lcamp2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-rp1"
LIST="/home/user/tcslib-scratch/fills/replay/down-lrp3.txt"
LOG="$S/fills/replay/replay-lrp3.log"
PINS="TCSlib/Complexity/ClassPSPACE/TQBFHardMachine.lean:1ad7891373f537d35ae897a763480ba150284258
TCSlib/Complexity/Randomized/BPLInP.lean:55b06b3b5fdfdb4f129912aad004e97d60e71b7b
TCSlib/Complexity/Randomized/BPLInPCount.lean:18a9cf33245ef2959816eeffeb7372a8d2f6df54
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean:0b9a4a831d1fb87a49ab6c8faedc37db9f99e6a9
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean:1cf0278d862100ff0cd0d999d469f40996172e92
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenRadius.lean:dad3a22033c61ef2669953329f94b4ebe5e5ac6b
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenStage.lean:fab553600356b779249af104adb90b7eb25fcd95
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenWalk.lean:d82e8c6548309fbe90eae665732d7250ad661a45
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean:3066bf69ca7c0942b95f3fb2821cea222425a479
TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean:896e12dac231e0ed4fa0aceb3fdc6dc52a231700
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean:a507cf09b43132d3ece206d5a1c4be15cac84607
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean:ed3857f7b55b665df0d26dc4738ae6a8adfe77a4
TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean:78814e59e44912a0d59ce3a9cd92e25349f39f74
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean:8da4bc53b70397c0640942064cec52de987fc9d5"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-rp1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 3a1c8740d7baf9eb3584f2ae3ecaed5cfe40e994 HEAD || { echo "precheck: the head must contain the campaign after #208, #212, #213 (oleans-lcamp2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 3a1c8740d7baf9eb3584f2ae3ecaed5cfe40e994 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #208, #212, #213 (oleans-lcamp2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "53" ] || { echo "precheck: the replay list must have 53 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lrp3" ] && { echo "precheck: $S/oleans-lrp3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp2" ] || { echo "precheck: oleans-lcamp2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp2" "$S/oleans-lrp3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lrp3 at $(git rev-parse --short HEAD): #216, RP-1, merged with the campaign after #208/#212/#213 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lrp3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lrp3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=53 failed=0" || { echo "replay: a module failed, or the count is not 53" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
