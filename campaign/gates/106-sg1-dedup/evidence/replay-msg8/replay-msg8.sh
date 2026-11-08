#!/usr/bin/env bash
# Replay msg8 (SG1 R4 existing backward-liveness adapters; currentfull329 replay; branch lean/dedup-sg1, stacked on currentcampaign750/wholeMAC5 at#234): its downstream closure (329 modules),
# fresh .oleans into oleans-msg8, a copy of oleans-mac5, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-sg1"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/order-msg8.txt"
LOG="$S/fills/replay/replay-msg8.log"
PINS="TCSlib/Complexity/ClassNP/SAT.lean:a1e156389744052d8c639ac6e456c50014b00245
TCSlib/Complexity/ClassNP/Tautology.lean:43f4b62bf7603c4c046cc23990494bc95ee72c5c
TCSlib/Complexity/CookLevin/Hardness.lean:433d0ce6e17ed264f0d7f650a8692d4da4744b4f
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:b2beab0b25899e955adc0117b87abf4fe9fe8f85
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean:560e6cb050ee97872beafd80c417a98eb296f600"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/dedup-sg1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 750987d674899d97db3c73c7278c891fa8772b40 HEAD || { echo "precheck: the head must contain currentcampaign750/wholeMAC5 at#234; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 750987d674899d97db3c73c7278c891fa8772b40 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from currentcampaign750/wholeMAC5 at#234 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mfup2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "329" ] || { echo "precheck: the replay list must have 329 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-msg8" ] && { echo "precheck: $S/oleans-msg8 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac5" ] || { echo "precheck: oleans-mac5 is missing; nothing copied" >&2; exit 2; }
cp -cR "$S/oleans-mac5" "$S/oleans-msg8" || exit 1
cd "$WT" || exit 1
{ echo "# replay-msg8 at $(git rev-parse --short HEAD): SG1 R4 existing backward-liveness adapters; currentfull329 replay ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-msg8"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-msg8 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=329 failed=0" || { echo "replay: a module failed, or the count is not 329" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
