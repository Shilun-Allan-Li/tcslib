#!/usr/bin/env bash
# Replay lspapi (the space API (Deterministic, Finite), on the merged tree after #145, #146 and #148; branch lean/spaceused-api, stacked on #144's merge (0416ffea, the tree of oleans-lsk2)): its downstream closure (324 modules),
# fresh .oleans into oleans-lspapi, a copy of oleans-lsk2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-spapi"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lspapi.txt"
LOG="$S/fills/replay/replay-lspapi.log"
PINS="TCSlib/Complexity/TuringMachine.lean:2568b022b9b2672afa4696a7175d95d36730dd3f
TCSlib/Complexity/TuringMachine/Build/InputDevice.lean:c6b99e698126f4eb41abf24468ddd105d5dac8d2
TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean:05d4e353e5e1460a8940f1fc6667d1e8e568ad97
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:1abbb8716d0450ea9b7cc10ef15e6204ed920b4a
TCSlib/Complexity/TuringMachine/Deterministic.lean:48e3393640ccd88585288b01353ec2d02dcf466d
TCSlib/Complexity/TuringMachine/Finite.lean:86af3005951710522d919c1edbdd42834ae6ed4d"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/spaceused-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0416ffea214a1d577d1f23866882918c5225d81f HEAD || { echo "precheck: the head must contain #144's merge (0416ffea, the tree of oleans-lsk2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0416ffea214a1d577d1f23866882918c5225d81f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #144's merge (0416ffea, the tree of oleans-lsk2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lsk2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "324" ] || { echo "precheck: the replay list must have 324 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lspapi" ] && { echo "precheck: $S/oleans-lspapi already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lsk2" ] || { echo "precheck: oleans-lsk2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lsk2" "$S/oleans-lspapi" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lspapi at $(git rev-parse --short HEAD): the space API (Deterministic, Finite), on the merged tree after #145, #146 and #148 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lspapi"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lspapi nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
