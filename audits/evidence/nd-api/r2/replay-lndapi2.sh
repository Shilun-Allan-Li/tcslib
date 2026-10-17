#!/usr/bin/env bash
# Replay for the ND inventory API's round 2 (lean/nd-api-r2, stacked on #121's round-2 head
# 0a5878ed): Encoding, CodeParser, CodeFormat, Simulation, Build/StepBlock, Build/CounterLoop,
# Build/VirtualInput, NDCodeSimulator, the ClassNP facade and their downstream closure (313 modules), fresh .oleans into oleans-lndapi2, a copy of oleans-lndiag2
# (#121 round 2's replay), via scripts/lean_check_tree.sh. The root TCSlib module is not listed
# (replay rule). Run by the user. The precheck pins the nine files' blob hashes.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-ndapi2"
LIST="$S/fills/replay/down-lndapi2.txt"
LOG="$S/fills/replay/replay-lndapi2.log"
PINS="TCSlib/Complexity/ClassNP.lean:a6f11f0819b7256d0fdef963656291993eb1b8c0
TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean:aa6a9f59160c2adb4ef29ffc702ee4fdf3e29567
TCSlib/Complexity/TuringMachine/Build/StepBlock.lean:4f77af36412abbf8dd8b73a27fcb1df6040dd24d
TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean:56545fff6f9879e59aac75bf24fa0df045e35e90
TCSlib/Complexity/TuringMachine/CodeFormat.lean:9af1b24012387d380359639e2592a9e5d24235d1
TCSlib/Complexity/TuringMachine/CodeParser.lean:95be4d21bc9b927bfaeb17cb6d406334b981a899
TCSlib/Complexity/TuringMachine/Encoding.lean:3948815ec7f3c2691245e0f7ace4eea0f3bd99f7
TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:2d41f8f42288904b84f6e3e869e04ba0b977caea
TCSlib/Complexity/TuringMachine/Simulation.lean:119871d44159fc627e41efebf4f3f94f69790041"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/nd-api-r2 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0a5878edaf7c417839d9d3e61266956ce260749c HEAD || { echo "precheck: the head must contain #121's round-2 head 0a5878ed; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0a5878edaf7c417839d9d3e61266956ce260749c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 0a5878ed must be exactly the nine files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lndiag2.log" 2>/dev/null | grep -qx "# modules=2 failed=0" || { echo "precheck: #121 round 2's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "313" ] || { echo "precheck: the replay list must have 313 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lndapi2" ] && { echo "precheck: $S/oleans-lndapi2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lndiag2" ] || { echo "precheck: oleans-lndiag2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lndiag2" "$S/oleans-lndapi2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lndapi2 at $(git rev-parse --short HEAD): Encoding, CodeParser, CodeFormat, Simulation, StepBlock, CounterLoop, VirtualInput, NDCodeSimulator, the ClassNP facade and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lndapi2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lndapi2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
