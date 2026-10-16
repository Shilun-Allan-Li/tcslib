#!/usr/bin/env bash
# Replay for the specification API PR (lean/spec-api) (run by the user): Build/Catalog, Build/CfgRecord,
# Build/RecordTable, Build/Contract/{Basic,Seam,Catalog} and their downstream closure (89 modules),
# fresh .oleans into oleans-lapi, a copy of oleans-lc5p (the replay output of #113, the cont5
# partial, on which #112 is stacked), via scripts/lean_check_tree.sh. The root TCSlib module is not
# listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-api"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/spec-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lc5p.log" 2>/dev/null | grep -qx "# modules=9 failed=0" || { echo "precheck: the #113 (cont5 partial) replay must have passed; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lapi" ] && { echo "precheck: $S/oleans-lapi already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lc5p" "$S/oleans-lapi" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lapi at $(git rev-parse --short HEAD): the six API files and their downstream closure ($(wc -l < $S/fills/replay/down-lapi.txt | tr -d ' ') modules), fresh .oleans into oleans-lapi"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lapi nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$S/fills/replay/down-lapi.txt"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lapi.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lapi.log"
