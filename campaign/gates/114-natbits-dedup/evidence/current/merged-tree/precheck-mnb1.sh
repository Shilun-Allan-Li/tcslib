#!/usr/bin/env bash
# Replay mnb1 (NatBits #222; branch lean/dedup-natbits, stacked on complete Mac campaign bootstrap): its downstream closure (344 modules),
# fresh .oleans into oleans-mnb1, a copy of oleans-mac0, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-natbits"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mnb1.txt"
LOG="$S/fills/replay/replay-mnb1.log"
PINS="TCSlib/Complexity/CircuitComplexity/Meyer.lean:f176feda6aa6f1b314fd7be7303032b546a9e167
TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean:f27d92e5f11a0aef6a5485b3865490b8802a29ce
TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:0ebadde8fa81dc2747df90d28423cc1aaf01e57a
TCSlib/Complexity/CookLevin/Hardness.lean:0998d738c6edf27a53c70f4d412decc2c8dc5dbe
TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean:442078d656b63ddf66af569d0c29c0dd28e77aeb
TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean:4cea80dce5d8d214b29ef54c8d29ed9a6c6c537a
TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean:8a9da5fac6b27b820607588e1dc98a625a441690
TCSlib/Complexity/Randomized/UniformSample.lean:9dc08dd80a54c588e971f6f1bafe914fd98dd11c
TCSlib/Complexity/SpaceComplexity/Codec/Word.lean:5de22c6db1682fd91a14b037eb7e7eb71dba892a
TCSlib/Complexity/SpaceComplexity/Constructible.lean:b830f01aaecb070061354707f4e8066a3df752e6
TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean:ebe2da70df1574482fbcdacd1dd8cbe2bfaed272
TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean:5d7b664ba9b6823b737f9546326f424e1c9065bf
TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean:610c35ae599a0dea8f7ef2b0b23cb3feed5e624b
TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean:ef8863adb3120d5053d2ccdef4a35a2f6ec3fee0
TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean:f31a7a8b3be0d9b7b5a5883522e6d70a68e592cd
TCSlib/Complexity/TuringMachine.lean:e817d6f2a075c8f7edf3fe04162b365bcb526476
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:d900b690eb6b87595c42bf68b5992d2522da8360
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:5d1f674b069c5fb54cb8626c8393abe56cfb0b50
TCSlib/Complexity/TuringMachine/Build/InputLength.lean:af10cbf106e60a5ad2b43b39913ef465ad9cfd1d
TCSlib/Complexity/TuringMachine/Build/RecordTable.lean:7d447bf88178bdba42c19448ee0f20134e87189e
TCSlib/Complexity/TuringMachine/Encoding.lean:c11a2803cdddde11b92b2cc2c74e4cd99eed07d3
TCSlib/Complexity/TuringMachine/NatBits.lean:0bfe1d6c07f81087b970d88f48d63a33bf377cd3"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-natbits 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 680760723d72826469d0fc294e4d7ee2ecac3e6c HEAD || { echo "precheck: the head must contain complete Mac campaign bootstrap; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 680760723d72826469d0fc294e4d7ee2ecac3e6c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from complete Mac campaign bootstrap must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/bootstrap-oleans-mac0.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "344" ] || { echo "precheck: the replay list must have 344 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mnb1" ] && { echo "precheck: $S/oleans-mnb1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac0" ] || { echo "precheck: oleans-mac0 is missing; nothing copied" >&2; exit 2; }
echo PRECHECK-PASSED; exit 0
