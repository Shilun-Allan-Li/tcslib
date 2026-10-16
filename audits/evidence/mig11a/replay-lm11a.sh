#!/usr/bin/env bash
# Replay for MIG-11a, the row contracts (lean/mig11a-row-contracts at its pushed head, stacked on
# #116's round 2) (run by the user): Build/Catalog, Build/Contract/Catalog, the new
# Build/Contract/Counter, the Build/Contract facade and their downstream closure (86 modules),
# fresh .oleans into oleans-lm11a, a copy of oleans-lcapi (#116 round 2's replay at 93c4c630: the
# tip plus #116), via scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-m11a"
LIST="$S/fills/replay/down-lm11a.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/mig11a-row-contracts 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 93c4c6304198dcb9147ed655ebcd7cb940c6a4b6 HEAD || { echo "precheck: the head must contain #116 round 2 (93c4c630); nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lcapi.log" 2>/dev/null | grep -qx "# modules=320 failed=0" || { echo "precheck: #116 round 2's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "86" ] || { echo "precheck: the replay list must have 86 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lm11a" ] && { echo "precheck: $S/oleans-lm11a already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lcapi" "$S/oleans-lm11a" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lm11a at $(git rev-parse --short HEAD): MIG-11a's four modules and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lm11a"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lm11a nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lm11a.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lm11a.log"
