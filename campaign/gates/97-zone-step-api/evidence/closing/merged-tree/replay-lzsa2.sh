#!/usr/bin/env bash
# Replay lzsa2 (#197's closing commit (gate 97's minors); branch lean/zone-step-api, stacked on the campaign (snapshot oleans-cloud0)): its downstream closure (111 modules),
# fresh .oleans into oleans-lzsa2, a copy of oleans-cloud0, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-197"
LIST="/home/user/tcslib-scratch/fills/replay/down-lzsa2.txt"
LOG="$S/fills/replay/replay-lzsa2.log"
PINS="TCSlib/Complexity/TuringMachine.lean:b52984260cfcf24da6928445e38747a3968d62ef
TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:d7d40bdd2fa62dab0c4eca7ae02df0f8170f96f4
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:f3c27ef923fa25d69c66e22c1a4d38812d6b231d
TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean:a94e820be04d994c3e7259669507cec15977476e"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/zone-step-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor fda12d4a73adbb8c61aac433f1b59c3e305a219a HEAD || { echo "precheck: the head must contain the campaign (snapshot oleans-cloud0); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only fda12d4a73adbb8c61aac433f1b59c3e305a219a HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign (snapshot oleans-cloud0) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/bootstrap-oleans-cloud0.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "111" ] || { echo "precheck: the replay list must have 111 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lzsa2" ] && { echo "precheck: $S/oleans-lzsa2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-cloud0" ] || { echo "precheck: oleans-cloud0 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-cloud0" "$S/oleans-lzsa2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lzsa2 at $(git rev-parse --short HEAD): #197's closing commit (gate 97's minors) ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lzsa2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lzsa2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=111 failed=0" || { echo "replay: a module failed, or the count is not 111" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
