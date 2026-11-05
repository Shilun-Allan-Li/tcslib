#!/usr/bin/env bash
# Replay lcf2 (the configuration facts PR (renamed lemma) merged with the campaign after #184; branch lean/cfg-facts, stacked on the campaign tip after #184): its downstream closure (83 modules),
# fresh .oleans into oleans-lcf2, a copy of oleans-ledge, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-cf"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lcf2.txt"
LOG="$S/fills/replay/replay-lcf2.log"
PINS="TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:d0317a6b6b282e05f3b1e15c6cde2b33172d8a63
TCSlib/Complexity/TuringMachine.lean:1db25237e8fe9d4fad3d97fb0427ee4a447bc4e3
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:f05a7a82fbf173537e7e40316b978e1377ffefc7
TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean:aa46f40096b924d308276cc02c7368b6dbda4354
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:9e687b1694cb8772cc78d490d4434a3edd67f2c5
TCSlib/Complexity/TuringMachine/CfgFacts.lean:57ab9954ccb04b458be931a1f2a86d4b426fbcf7"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/cfg-facts 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 057da7a70512f7d5e089601f81e66b4c84e7a17f HEAD || { echo "precheck: the head must contain the campaign tip after #184; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 057da7a70512f7d5e089601f81e66b4c84e7a17f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #184 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-ledge.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "83" ] || { echo "precheck: the replay list must have 83 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcf2" ] && { echo "precheck: $S/oleans-lcf2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-ledge" ] || { echo "precheck: oleans-ledge is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-ledge" "$S/oleans-lcf2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcf2 at $(git rev-parse --short HEAD): the configuration facts PR (renamed lemma) merged with the campaign after #184 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcf2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcf2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=83 failed=0" || { echo "replay: a module failed, or the count is not 83" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
