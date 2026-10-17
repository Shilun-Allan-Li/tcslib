#!/usr/bin/env bash
# Chained replay for #118's round 2 (lean/brief-api at its pushed head 4624fc05: MIG-12's API
# 9872634e, then the gate's repairs to CodeParser, Build/CounterLoop and StateRenaming) (run by
# the user): the three files' downstream closure (274 modules), fresh .oleans into oleans-lbapi3,
# a copy of oleans-lm12api (MIG-12's API replay at 9872634e, 160 of 160), via
# scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-bapi"
LIST="$S/fills/replay/down-lbapi3.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/brief-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 9872634e HEAD || { echo "precheck: the head must contain MIG-12's API 9872634e; nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lm12api.log" 2>/dev/null | grep -qx "# modules=160 failed=0" || { echo "precheck: MIG-12's API replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "274" ] || { echo "precheck: the replay list must have 274 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lbapi3" ] && { echo "precheck: $S/oleans-lbapi3 already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lm12api" "$S/oleans-lbapi3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lbapi3 at $(git rev-parse --short HEAD): CodeParser, CounterLoop, StateRenaming and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lbapi3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lbapi3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lbapi3.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lbapi3.log"
