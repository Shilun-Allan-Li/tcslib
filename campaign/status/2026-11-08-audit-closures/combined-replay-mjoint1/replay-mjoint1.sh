source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
#!/usr/bin/env bash
# Replay mjoint1 (combined SG-1 and MIG-1 prospective merged-tree closure; branch validation-only-local-combined, stacked on current campaign with both audited PRs): its downstream closure (394 modules),
# fresh .oleans into oleans-mjoint1, a copy of oleans-mac6, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-camp"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/order-mjoint1.txt"
LOG="$S/fills/replay/replay-mjoint1.log"
PINS="TCSlib/Complexity/ClassNP/SAT.lean:a1e156389744052d8c639ac6e456c50014b00245
TCSlib/Complexity/ClassNP/Tautology.lean:43f4b62bf7603c4c046cc23990494bc95ee72c5c
TCSlib/Complexity/ClassP/TimeConstructible.lean:1b75ba4be98ee5d668c43bbc3e39d2a654277dab
TCSlib/Complexity/CookLevin/Hardness.lean:433d0ce6e17ed264f0d7f650a8692d4da4744b4f
TCSlib/Complexity/RAMSimulation/WordSize.lean:aea14858d3ad820b26cb2f5c663f43b0e4e2c3bc
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:6f531738ca8c3195d2d22b9a7be21662a8dc84bc
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:e08d31000ec29acbb18caae0150eca304152ccc8
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:b2beab0b25899e955adc0117b87abf4fe9fe8f85
TCSlib/Complexity/TuringMachine/Build/Loop.lean:01074b43fa0eceefcc6f416de9fc5b1312a0c31f
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:8e06171554e996ab8e6f58078b2395ebc194a10f
TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean:01a6029a38cb16f17085baf88ed361882f8d5a03
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:1c5b891e3010779d763f831a40622c2a33929151
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:123a5538616a3456ac3bcc2c7c4b67abdc3f4eea
TCSlib/Complexity/TuringMachine/Composition.lean:96b61fd02edcec3c0f1c2e5db0444afefb77b9d3
TCSlib/Complexity/TuringMachine/Encoding.lean:e3870facaec7ff216f762b3f815023b06eeea8b9
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:560e6cb050ee97872beafd80c417a98eb296f600
TCSlib/Complexity/TuringMachine/Simulation.lean:a9cb5440e7cefcfb189a7f4e39123894ed8d52b2"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" rev-parse HEAD)" = "11b09440347ca8274562d58b5f90a11cfce56e29" ] || { echo "precheck: local prospective combined merge pin changed; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 8f14c7f1f67ccfb1c03613531abd91fea40c4d46 HEAD || { echo "precheck: the head must contain current campaign with both audited PRs; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 8f14c7f1f67ccfb1c03613531abd91fea40c4d46 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from current campaign with both audited PRs must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-msg9.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "394" ] || { echo "precheck: the replay list must have 394 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mjoint1" ] && { echo "precheck: $S/oleans-mjoint1 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac6" ] || { echo "precheck: oleans-mac6 is missing; nothing copied" >&2; exit 2; }
cp -cR "$S/oleans-mac6" "$S/oleans-mjoint1" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mjoint1 at $(git rev-parse --short HEAD): combined SG-1 and MIG-1 prospective merged-tree closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mjoint1"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    rm -f "$S/oleans-mjoint1/$m.olean" "$S/oleans-mjoint1/$m.ilean" "$S/oleans-mjoint1/$m.c" "$S/oleans-mjoint1/$m.trace"
    out=$(TCSLIB_OLEANS=$S/oleans-mjoint1 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
