#!/usr/bin/env bash
# Replay lcamp2 (the campaign after #208, #212 and #213 (merged); branch complexity/arora-barak-ch3-4, stacked on the campaign after #209): its downstream closure (195 modules),
# fresh .oleans into oleans-lcamp2, a copy of oleans-lnth, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-camp"
LIST="/home/user/tcslib-scratch/fills/replay/down-lcamp2.txt"
LOG="$S/fills/replay/replay-lcamp2.log"
PINS="TCSlib/Complexity/Randomized/BPLInPCount.lean:f1170da3b87823f0c1bd49ada3f9cab0e7662304
TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean:7cc29979e37fac794e068ddeba89c4b5f60b7167
TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean:fe88fe1488f3d5d3e3688b10f4ef5937b200f026
TCSlib/Complexity/SpaceComplexity.lean:fa412aa6e769198cd263ee35441a95e3d61d69a3
TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean:044345da2ff571954753a259ee1a0f52d713acef
TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean:148e95d9142e8e51814d9489254af3c4a10ef506
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:efbbbbef1a91a42ec2438e3f59476d9abf582088
TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean:f48bd13dfd1f102ebf65980073a52ce2c0422a90
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean:96172f8c58899663f5a1fa4bcedf9b3defbb86eb
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean:ef71ec26cbb361af84be84751e3ec4936e6f14c0
TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean:aef4257663a9836dc4c456eca255cffa557d0cd2
TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean:5255444df46cc7aed84a5fd19cf21a364f7a4dda
TCSlib/Complexity/SpaceComplexity/Savitch.lean:0c14e432aa98f8277b0e823e160de8f19f8dd0b2
TCSlib/Complexity/SpaceComplexity/SavitchARM/Correct.lean:de68ce1eafcecd911790641966653475472d1b16
TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean:558d617474ac2c44f26b15ac82099ceab60e160a
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:3d26b552b14b456d247122c79d117f1707532d0d"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/complexity/arora-barak-ch3-4 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0b05cc3aaf2e48a8b8a676d8c6b7214a61848a06 HEAD || { echo "precheck: the head must contain the campaign after #209; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0b05cc3aaf2e48a8b8a676d8c6b7214a61848a06 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #209 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lnth.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "195" ] || { echo "precheck: the replay list must have 195 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcamp2" ] && { echo "precheck: $S/oleans-lcamp2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lnth" ] || { echo "precheck: oleans-lnth is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lnth" "$S/oleans-lcamp2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcamp2 at $(git rev-parse --short HEAD): the campaign after #208, #212 and #213 (merged) ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcamp2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcamp2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=195 failed=0" || { echo "replay: a module failed, or the count is not 195" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
