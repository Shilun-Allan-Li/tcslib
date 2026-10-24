#!/usr/bin/env bash
# Replay lphl2 (#156 round 2: the phase-host re-points of gate 69's major, on #156's previous head
# a4d9b024, the tree of oleans-lphl): the five changed files' downstream closure (23 modules),
# fresh .oleans into oleans-lphl2, a copy of oleans-lphl, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-phlast"
LIST="$S/fills/replay/down-lphl2.txt"
LOG="$S/fills/replay/replay-lphl2.log"
PINS="TCSlib/Complexity/SpaceComplexity/Inclusions.lean:aeb0a6832883a168e7f2e3c3f96a1811a291cd98
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:ed59e7e6c4cc54942fb4cd6261bf6c4dc19d4088
TCSlib/Complexity/TuringMachine/Build/StepBlock.lean:1f063406fc86c3522e5bbd62ea03b3816501d61e
TCSlib/Complexity/TuringMachine/Build/WindowRun.lean:91d4f9634c5c60c90bf216b1b4a256a472500c5f
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:1d4721de62a86b9edc0fed2c279ffbcde0e5bf6c"
BASE=a4d9b02450d910a18ce2eaee689f30485bfcc769
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/phasehost-last 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor "$BASE" HEAD || { echo "precheck: the head must contain #156's previous head (the tree of oleans-lphl); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only "$BASE" HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #156's previous head must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lphl.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "23" ] || { echo "precheck: the replay list must have 23 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lphl2" ] && { echo "precheck: $S/oleans-lphl2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lphl" ] || { echo "precheck: oleans-lphl is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lphl" "$S/oleans-lphl2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lphl2 at $(git rev-parse --short HEAD): #156 round 2, the phase-host re-points ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lphl2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lphl2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
