#!/usr/bin/env bash
# Replay mra2 (approved reader APIs current merged tree; branch lean/ab34-reading-api, stacked on campaign after separation consumer): its downstream closure (394 modules),
# fresh .oleans into oleans-mra2, a copy of oleans-mac3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-natbits"
LIST="/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/down-mra2.txt"
LOG="$S/fills/replay/replay-mra2.log"
PINS="TCSlib/Complexity/TuringMachine/Build/Primitives.lean:37165dcf8dcfff4140a786e36aa8c827aa0d5878
TCSlib/Complexity/TuringMachine/Build/Wrappers.lean:af54cbd6247438070ca2f7f37debd8615bbc1d3a
TCSlib/Complexity/TuringMachine/Composition.lean:13b5591983b46d64925ce88c7a586fceaf362f7a
TCSlib/Complexity/TuringMachine/Encoding.lean:c1d171e6fa550e6f9dce58f96021552307dbd8c0
TCSlib/Complexity/TuringMachine/Simulation.lean:bf0bb4900665e7ca0559d6ed1a7e936c0f7b5510"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/ab34-reading-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor e3adffac67377a8b6e23bed74bfdbb44a123dd86 HEAD || { echo "precheck: the head must contain campaign after separation consumer; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only e3adffac67377a8b6e23bed74bfdbb44a123dd86 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from campaign after separation consumer must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mlin2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "394" ] || { echo "precheck: the replay list must have 394 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-mra2" ] && { echo "precheck: $S/oleans-mra2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac3" ] || { echo "precheck: oleans-mac3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-mac3" "$S/oleans-mra2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mra2 at $(git rev-parse --short HEAD): approved reader APIs current merged tree ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-mra2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-mra2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
