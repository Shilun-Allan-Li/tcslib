#!/usr/bin/env bash
# Replay for the brief-inventory API (lean/brief-api at its pushed head, stacked on #117) (run by the
# user): Simulation, UniversalStartup, Build/VirtualInput, Build/CfgRecord, Build/CounterLoop,
# Build/Loop and their downstream closure (311 modules), fresh .oleans into oleans-lbapi, a copy of
# oleans-lm11a (#117's replay at b131d239: the tip plus #117), via scripts/lean_check_tree.sh. The
# root TCSlib module is not listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-bapi"
LIST="$S/fills/replay/down-lbapi.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/brief-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 1358ff736bf93d40d3f12ed5c8b61268afd9e1e1 HEAD || { echo "precheck: the head must contain #117 (1358ff73); nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lm11a.log" 2>/dev/null | grep -qx "# modules=86 failed=0" || { echo "precheck: #117's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "311" ] || { echo "precheck: the replay list must have 311 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lbapi" ] && { echo "precheck: $S/oleans-lbapi already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lm11a" "$S/oleans-lbapi" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lbapi at $(git rev-parse --short HEAD): the six API files and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lbapi"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lbapi nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lbapi.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lbapi.log"
