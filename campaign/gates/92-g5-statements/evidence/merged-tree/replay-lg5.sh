#!/usr/bin/env bash
# Replay lg5 (#189 (G5's statements) merged with the campaign after #184; branch lean/g5-statements, stacked on the campaign tip after #184): its downstream closure (325 modules),
# fresh .oleans into oleans-lg5, a copy of oleans-ledge, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g5"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lg5.txt"
LOG="$S/fills/replay/replay-lg5.log"
PINS="TCSlib/Complexity/TuringMachine.lean:579fcc579bba922b098b4ad9c3afd0f976718877
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:06d9339d3f17bc38bda991ccd68185d1fcb57eff
TCSlib/Complexity/TuringMachine/Encoding.lean:c0fe678412984e3ea7e99f2cfb16533a08e39449
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean:e95cd630f4eb2303c3f1a1cc789013b73a24cbee
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean:6cf70886a3f50df59554948a90980c755ae8167b
TCSlib/Complexity/TuringMachine/UniversalTlogT.lean:666b3f8324c616500a5febfa3ee317f45d446366"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g5-statements 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 057da7a70512f7d5e089601f81e66b4c84e7a17f HEAD || { echo "precheck: the head must contain the campaign tip after #184; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 057da7a70512f7d5e089601f81e66b4c84e7a17f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #184 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-ledge.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "325" ] || { echo "precheck: the replay list must have 325 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg5" ] && { echo "precheck: $S/oleans-lg5 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-ledge" ] || { echo "precheck: oleans-ledge is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-ledge" "$S/oleans-lg5" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg5 at $(git rev-parse --short HEAD): #189 (G5's statements) merged with the campaign after #184 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg5"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg5 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=325 failed=0" || { echo "replay: a module failed, or the count is not 325" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
