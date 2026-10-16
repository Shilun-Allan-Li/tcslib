#!/usr/bin/env bash
# Replay for the core specification API PR, round 2 (lean/core-api at its pushed head: the campaign
# tip and #112's round 2 merged in, i.e. stacked on #112) (run by the user): the eleven changed
# modules (Configuration, Deterministic, Finite, Encoding, Simulation, Build/Embed, Build/StepBlock,
# Build/StepClock, Build/Zone, Build/ZoneTape, CodeSimulator) and their downstream closure
# (320 modules), fresh .oleans into oleans-lcapi, a copy of oleans-lapi2 (#112 round 2's replay at
# caa93c12: the tip plus #112), via scripts/lean_check_tree.sh. The root TCSlib module is not
# listed (replay rule).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-capi"
LIST="$S/fills/replay/down-lcapi.txt"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/core-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor caa93c124168f6f0678b47e38a0a0cb403fb7810 HEAD || { echo "precheck: the head must contain #112 round 2 (caa93c12); nothing copied" >&2; exit 2; }
tail -1 "$S/fills/replay/replay-lapi2.log" 2>/dev/null | grep -qx "# modules=85 failed=0" || { echo "precheck: #112 round 2's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "320" ] || { echo "precheck: the replay list must have 320 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcapi" ] && { echo "precheck: $S/oleans-lcapi already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lapi2" "$S/oleans-lcapi" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcapi at $(git rev-parse --short HEAD): the eleven changed modules and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcapi"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcapi nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$S/fills/replay/replay-lcapi.log" 2>&1
tail -n 12 "$S/fills/replay/replay-lcapi.log"
