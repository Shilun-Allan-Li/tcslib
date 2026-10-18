#!/usr/bin/env bash
# Replay for the specification API PR, round 2 (lean/spec-api at its pushed head, with the campaign
# branch merged in) (run by the user): Build/Contract/{Basic,Seam,Catalog}, Build/CfgRecord,
# Build/RecordTable, SpaceComplexity/WindowClock and their downstream closure (85 modules), fresh
# .oleans into oleans-lapi2, a copy of oleans-lg4p (the chained replay of #112 round 1, #113, #114
# and #115, i.e. the campaign tip plus round 1), via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-api"
LIST="$S/fills/replay/down-lapi2.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/spec-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lg4p.log" 2>/dev/null | grep -qx "# modules=2 failed=0" || { echo "precheck: the #115 (G4 partial) replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "85" ] || { echo "precheck: the replay list must have 85 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lapi2" ] && { echo "precheck: $S/oleans-lapi2 already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lg4p" "$S/oleans-lapi2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lapi2 at $(git rev-parse --short HEAD): round 2's six files and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lapi2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lapi2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lapi2.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lapi2.log"
