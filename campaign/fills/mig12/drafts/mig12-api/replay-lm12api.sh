#!/usr/bin/env bash
# Chained replay for MIG-12's API (lean/mig12-api at its pushed head, stacked on #118's 4ae686be)
# (run by the user): SymbolLift, Build/Convention, Build/CounterLoop and their downstream closure
# (160 modules), fresh .oleans into oleans-lm12api, a copy of oleans-lbapi2 (#118's chained
# replay at 36325650, 86 of 86), via scripts/lean_check_tree.sh. The root TCSlib module is not
# listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-m12api"
LIST="$S/fills/replay/down-lm12api.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/mig12-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed branch head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 4ae686be925ad617a0189ddc4ba95523940ea0fb HEAD || { echo "precheck: the head must contain #118's head 4ae686be; nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lbapi2.log" 2>/dev/null | grep -qx "# modules=86 failed=0" || { echo "precheck: #118's chained replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "160" ] || { echo "precheck: the replay list must have 160 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lm12api" ] && { echo "precheck: $S/oleans-lm12api already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lbapi2" "$S/oleans-lm12api" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lm12api at $(git rev-parse --short HEAD): SymbolLift, Convention, CounterLoop and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lm12api"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lm12api nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lm12api.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lm12api.log"
