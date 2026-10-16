#!/usr/bin/env bash
# Replay for the G2 maintainer fill PR (lean/g2-fill) (run by the user): Build/Catalog, Build/Zone and their
# downstream closure (87 modules), fresh .oleans into oleans-lg2, a copy of oleans-lcanon4 (the replay output of
# #107, canonizer continuation 4), via scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule).
S=<S>
WT="$S/wt-pg2"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g2-fill 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lcanon4.log" 2>/dev/null | grep -qx "# modules=9 failed=0" || { echo "precheck: the #107 (canonizer cont4) replay must have passed; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg2" ] && { echo "precheck: $S/oleans-lg2 already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lcanon4" "$S/oleans-lg2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg2 at $(git rev-parse --short HEAD): Catalog, Zone and their downstream closure ($(wc -l < $S/fills/replay/down-lg2.txt | tr -d ' ') modules), fresh .oleans into oleans-lg2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$S/fills/replay/down-lg2.txt"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lg2.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lg2.log"
