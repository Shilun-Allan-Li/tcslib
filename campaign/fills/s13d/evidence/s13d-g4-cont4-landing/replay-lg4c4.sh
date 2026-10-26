#!/usr/bin/env bash
# Replay lg4c4 (G4 continuation 4: the zone extension and rebalance rows; branch lean/g4-cont4-landing, stacked on the campaign tip after #161 (the tree of oleans-lu2api)): its downstream closure (2 modules),
# fresh .oleans into oleans-lg4c4, a copy of oleans-lu2api, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-g4c4land"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lg4c4.txt"
LOG="$S/fills/replay/replay-lg4c4.log"
PINS="TCSlib/Complexity/TuringMachine.lean:c4917d8e8faa7200a3bb467a8667c787de83bd04
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:cdcafc9181415869e28f21d6cba7ce9631dd816c"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g4-cont4-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 079a070766688031c177ff97f5eced81e476d18a HEAD || { echo "precheck: the head must contain the campaign tip after #161 (the tree of oleans-lu2api); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 079a070766688031c177ff97f5eced81e476d18a HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #161 (the tree of oleans-lu2api) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lu2api.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg4c4" ] && { echo "precheck: $S/oleans-lg4c4 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lu2api" ] || { echo "precheck: oleans-lu2api is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lu2api" "$S/oleans-lg4c4" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg4c4 at $(git rev-parse --short HEAD): G4 continuation 4: the zone extension and rebalance rows ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg4c4"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg4c4 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
