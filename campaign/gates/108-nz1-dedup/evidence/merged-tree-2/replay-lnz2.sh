#!/usr/bin/env bash
# Replay lnz2 (#217, NZ-1 with ExpectedTime's probability form, on the campaign after #216; branch lean/dedup-nz1, stacked on the campaign after #216 (oleans-lcamp3)): its downstream closure (261 modules),
# fresh .oleans into oleans-lnz2, a copy of oleans-lcamp3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-nz1"
LIST="/home/user/tcslib-scratch/fills/replay/down-lnz2.txt"
LOG="$S/fills/replay/replay-lnz2.log"
PINS="TCSlib/Complexity/CircuitComplexity/Advice.lean:d14a903d564f4a307014292a03a802ecb8fba1bd
TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:e40e533378d2c42f5fbfde869746c3d961c4c0f1
TCSlib/Complexity/ClassNP/NDNormalForm.lean:f4a4ec59a03ca2c6ce1bda3866bfeeb564ce5968
TCSlib/Complexity/ClassNP/NTIME.lean:a312c47f7d80cb7507ddcaa9062a2649d38830cb
TCSlib/Complexity/Randomized/BPTIMEThreshold.lean:de3ab2dd4f4e8d6e9747c9cec82dac2a3eac2a13
TCSlib/Complexity/Randomized/ExpectedTime.lean:47021ff8bf0764a977a4cf90613e43b4f4997a4e
TCSlib/Complexity/TuringMachine/Build/Loop.lean:ba37b2207459885eb94b4ad2c80cb1dc7a400aec
TCSlib/Complexity/TuringMachine/Nondeterministic.lean:7fdd1de1a4329b3a902fd05305a016fb67d5ff4f"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-nz1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD || { echo "precheck: the head must contain the campaign after #216 (oleans-lcamp3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 2e258a770245a98ca9bae0f0d28c63781c5adba4 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #216 (oleans-lcamp3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lcamp3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "261" ] || { echo "precheck: the replay list must have 261 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lnz2" ] && { echo "precheck: $S/oleans-lnz2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lcamp3" ] || { echo "precheck: oleans-lcamp3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lcamp3" "$S/oleans-lnz2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lnz2 at $(git rev-parse --short HEAD): #217, NZ-1 with ExpectedTime's probability form, on the campaign after #216 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lnz2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lnz2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=261 failed=0" || { echo "replay: a module failed, or the count is not 261" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
