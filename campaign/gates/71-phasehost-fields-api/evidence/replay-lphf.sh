#!/usr/bin/env bash
# Replay lphf (the phase host's field equations and the re-points; branch lean/phasehost-fields, stacked on the campaign tip after #156 (21d53053, the tree of oleans-lphl2)): its downstream closure (88 modules),
# fresh .oleans into oleans-lphf, a copy of oleans-lphl2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-phfields"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lphf.txt"
LOG="$S/fills/replay/replay-lphf.log"
PINS="TCSlib/Complexity/SpaceComplexity/Inclusions.lean:7e0d80eab6e6805c81aa4d165d539745b23232b9
TCSlib/Complexity/TuringMachine/Build/NDHost.lean:10123a61fa55ac41f9893b16d23b29a9d4d93283
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:ce6451f8dec75caaab99919cbb1ec1dc882ca228
TCSlib/Complexity/TuringMachine/Build/Seam.lean:ef7737e9389491cc14058cb952a102943e3fe0d9
TCSlib/Complexity/TuringMachine/Build/StepBlock.lean:add8c05fe76dde8c1e7f625d1b0dbfa06689f430
TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean:4f3d46bfb2943073ed3528e84b84f730d4519497
TCSlib/Complexity/TuringMachine/Build/WindowRun.lean:b3c8935b2d8a1e65245f968c68feceee4d6aa442
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:733a9a463e6bac937ef16ff95a8cb4d287bda725"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/phasehost-fields 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor cbdb860cd72a16f09ccd9402d83d921439b11c64 HEAD || { echo "precheck: the head must contain the campaign tip after #156 (21d53053, the tree of oleans-lphl2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only cbdb860cd72a16f09ccd9402d83d921439b11c64 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #156 (21d53053, the tree of oleans-lphl2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lphl2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "88" ] || { echo "precheck: the replay list must have 88 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lphf" ] && { echo "precheck: $S/oleans-lphf already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lphl2" ] || { echo "precheck: oleans-lphl2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lphl2" "$S/oleans-lphf" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lphf at $(git rev-parse --short HEAD): the phase host's field equations and the re-points ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lphf"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lphf nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
