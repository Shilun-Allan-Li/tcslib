#!/usr/bin/env bash
# Replay lg4c1b (#125 restacked: ZoneRebalance and the TuringMachine facade; branch lean/g4-cont1-partial, stacked on #123 c567568f): its downstream closure (2 modules),
# fresh .oleans into oleans-lg4c1b, a copy of oleans-lc1w, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g4l-b"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lg4c1.txt"
LOG="$S/fills/replay/replay-lg4c1b.log"
PINS="TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:e88edbda6df8397f897962a5225895a39bd363c1"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g4-cont1-partial 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor c567568f950117d15c41226a9244f3d9f08c189a HEAD || { echo "precheck: the head must contain #123 c567568f; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only c567568f950117d15c41226a9244f3d9f08c189a HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #123 c567568f must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lc1w.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg4c1b" ] && { echo "precheck: $S/oleans-lg4c1b already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lc1w" ] || { echo "precheck: oleans-lc1w is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lc1w" "$S/oleans-lg4c1b" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg4c1b at $(git rev-parse --short HEAD): #125 restacked: ZoneRebalance and the TuringMachine facade ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg4c1b"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg4c1b nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
