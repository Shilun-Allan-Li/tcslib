#!/usr/bin/env bash
# Replay lnpc3 (NP's closure in PClosure and TMSAT's hardened step; branch lean/np-closure, stacked on the campaign tip after #175 (the tree of oleans-lscp3)): its downstream closure (66 modules),
# fresh .oleans into oleans-lnpc3, a copy of oleans-lscp3, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-npcfix"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lnpc3.txt"
LOG="$S/fills/replay/replay-lnpc3.log"
PINS="TCSlib/Complexity/ClassNP/PClosure.lean:7acc5fab39d646e29369cf7e39ef5537aa6e95ba
TCSlib/Complexity/ClassNP/TMSAT.lean:d5f4e37fdda98c0cbba2a32ab30cb52c25798a31"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/np-closure 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor c06adb6cf580dc6d6f7a044d56bb6f0477237fa9 HEAD || { echo "precheck: the head must contain the campaign tip after #175 (the tree of oleans-lscp3); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only c06adb6cf580dc6d6f7a044d56bb6f0477237fa9 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #175 (the tree of oleans-lscp3) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lscp3.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "66" ] || { echo "precheck: the replay list must have 66 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lnpc3" ] && { echo "precheck: $S/oleans-lnpc3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lscp3" ] || { echo "precheck: oleans-lscp3 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lscp3" "$S/oleans-lnpc3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lnpc3 at $(git rev-parse --short HEAD): NP's closure in PClosure and TMSAT's hardened step ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lnpc3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lnpc3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=66 failed=0" || { echo "replay: a module failed, or the count is not 66" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
