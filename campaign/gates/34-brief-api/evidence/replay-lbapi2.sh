#!/usr/bin/env bash
# Chained replay for the brief-inventory API's second commit (lean/brief-api at its pushed head,
# 36325650: the G4 continuation's contract-layer lemmas) (run by the user): Build/Contract/Basic,
# Build/Contract/Seam and their downstream closure (86 modules), fresh .oleans into oleans-lbapi2, a
# copy of oleans-lbapi (#118's first replay at 277735f2, 311 of 311), via scripts/lean_check_tree.sh.
# The root TCSlib module is not listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-bapi"
LIST="$S/fills/replay/down-lbapi2.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/brief-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 277735f2 HEAD || { echo "precheck: the head must contain the first replay's 277735f2; nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lbapi.log" 2>/dev/null | grep -qx "# modules=311 failed=0" || { echo "precheck: #118's first replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "86" ] || { echo "precheck: the replay list must have 86 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lbapi2" ] && { echo "precheck: $S/oleans-lbapi2 already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lbapi" "$S/oleans-lbapi2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lbapi2 at $(git rev-parse --short HEAD): Contract/Basic, Contract/Seam and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lbapi2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lbapi2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lbapi2.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lbapi2.log"
