#!/usr/bin/env bash
# Replay mmig2 (MIG1 screened final autonomous proof repairs; branch lean/mig1-mega-landing, stacked on campaign after separation consumer): its downstream closure (394 modules),
# fresh .oleans into oleans-mmig2, a copy of oleans-mac3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-epad"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mmig2.txt"
LOG="$S/fills/replay/replay-mmig2.log"
PINS="TCSlib/Complexity/ClassP/TimeConstructible.lean:1b75ba4be98ee5d668c43bbc3e39d2a654277dab
TCSlib/Complexity/RAMSimulation/WordSize.lean:aea14858d3ad820b26cb2f5c663f43b0e4e2c3bc
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:ae360c114e73d7bf7df236b739c049211084760c
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:e08d31000ec29acbb18caae0150eca304152ccc8
TCSlib/Complexity/TuringMachine/Build/Loop.lean:42bf15c07961e145f6ea60844f4fd018d73dacfb
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:8facbb793b6afa9c249aca3d963c276e6044f1d5
TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean:01a6029a38cb16f17085baf88ed361882f8d5a03
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:03341e89975ac823406eb6db2b25bd187689d557
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:123a5538616a3456ac3bcc2c7c4b67abdc3f4eea
TCSlib/Complexity/TuringMachine/Composition.lean:d8a0abb9203da554e33f6906f8577d6dec561e4d
TCSlib/Complexity/TuringMachine/Encoding.lean:4fb2e649ec51133e20d000a416f5c26bebbefd2b
TCSlib/Complexity/TuringMachine/Simulation.lean:f5eafd52412d701fc4966d7dc54e0fcdfdaf9622"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/mig1-mega-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 93e191691318432578b44a06b7d1398ec143a533 HEAD || { echo "precheck: the head must contain campaign after separation consumer; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 93e191691318432578b44a06b7d1398ec143a533 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after separation consumer must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mlin2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "394" ] || { echo "precheck: the replay list must have 394 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mmig2" ] && { echo "precheck: $S/oleans-mmig2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac3" ] || { echo "precheck: oleans-mac3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-mac3" "$S/oleans-mmig2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mmig2 at $(git rev-parse --short HEAD): MIG1 screened final autonomous proof repairs ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mmig2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-mmig2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=394 failed=0" || { echo "replay: a module failed, or the count is not 394" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
