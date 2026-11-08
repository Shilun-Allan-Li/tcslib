#!/usr/bin/env bash
# Replay mmig3 (MIG final approved reader/first-entry integration; actual currentfull394; branch lean/mig1-mega-landing, stacked on current campaign750 / wholeMAC5 at merged#234): its downstream closure (394 modules),
# fresh .oleans into oleans-mmig3, a copy of oleans-mac5, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-epad"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/order-mmig3.txt"
LOG="$S/fills/replay/replay-mmig3.log"
PINS="TCSlib/Complexity/ClassP/TimeConstructible.lean:1b75ba4be98ee5d668c43bbc3e39d2a654277dab
TCSlib/Complexity/RAMSimulation/WordSize.lean:aea14858d3ad820b26cb2f5c663f43b0e4e2c3bc
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:6f531738ca8c3195d2d22b9a7be21662a8dc84bc
TCSlib/Complexity/TuringMachine/Build/CertShell.lean:e08d31000ec29acbb18caae0150eca304152ccc8
TCSlib/Complexity/TuringMachine/Build/Loop.lean:01074b43fa0eceefcc6f416de9fc5b1312a0c31f
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:8e06171554e996ab8e6f58078b2395ebc194a10f
TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean:01a6029a38cb16f17085baf88ed361882f8d5a03
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:1c5b891e3010779d763f831a40622c2a33929151
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:123a5538616a3456ac3bcc2c7c4b67abdc3f4eea
TCSlib/Complexity/TuringMachine/Composition.lean:96b61fd02edcec3c0f1c2e5db0444afefb77b9d3
TCSlib/Complexity/TuringMachine/Encoding.lean:e3870facaec7ff216f762b3f815023b06eeea8b9
TCSlib/Complexity/TuringMachine/Simulation.lean:a9cb5440e7cefcfb189a7f4e39123894ed8d52b2"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/mig1-mega-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 750987d674899d97db3c73c7278c891fa8772b40 HEAD || { echo "precheck: the head must contain current campaign750 / wholeMAC5 at merged#234; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 750987d674899d97db3c73c7278c891fa8772b40 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from current campaign750 / wholeMAC5 at merged#234 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mfup2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "394" ] || { echo "precheck: the replay list must have 394 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mmig3" ] && { echo "precheck: $S/oleans-mmig3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac5" ] || { echo "precheck: oleans-mac5 is missing; nothing copied" >&2; exit 2; }
cp -cR "$S/oleans-mac5" "$S/oleans-mmig3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mmig3 at $(git rev-parse --short HEAD): MIG final approved reader/first-entry integration; actual currentfull394 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mmig3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    rm -f "$S/oleans-mmig3/$m.olean" "$S/oleans-mmig3/$m.ilean" "$S/oleans-mmig3/$m.c" "$S/oleans-mmig3/$m.trace"
    out=$(TCSLIB_OLEANS=$S/oleans-mmig3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
