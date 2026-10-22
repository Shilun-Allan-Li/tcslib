#!/usr/bin/env bash
# Replay l132 (UN/U2-S API PR #132: Build/Primitives and Simulation and their downstream closure; branch lean/un-u2s-api, stacked on the campaign tip after #131 (0bf4f085)): its downstream closure (314 modules),
# fresh .oleans into oleans-l132, a copy of oleans-lc6m, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-api3"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-l132.txt"
LOG="$S/fills/replay/replay-l132.log"
PINS="TCSlib/Complexity/TuringMachine/Build/Primitives.lean:952dd5507b1fccf4782c55b797549b62b18004ec
TCSlib/Complexity/TuringMachine/Simulation.lean:40f509d9c4255fac5c86648743d356c916a018d5"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/un-u2s-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 0bf4f0856baec53a519742a82e2d53ef30bfb839 HEAD || { echo "precheck: the head must contain the campaign tip after #131 (0bf4f085); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 0bf4f0856baec53a519742a82e2d53ef30bfb839 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #131 (0bf4f085) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lc6m.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "314" ] || { echo "precheck: the replay list must have 314 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-l132" ] && { echo "precheck: $S/oleans-l132 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lc6m" ] || { echo "precheck: oleans-lc6m is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lc6m" "$S/oleans-l132" || exit 1
cd "$WT" || exit 1
{ echo "# replay-l132 at $(git rev-parse --short HEAD): UN/U2-S API PR #132: Build/Primitives and Simulation and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-l132"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-l132 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
