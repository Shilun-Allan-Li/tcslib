#!/usr/bin/env bash
# Replay lscp (the SCP move to Constructible; branch lean/scp-constructible, stacked on the campaign tip after #174 (the tree of oleans-lnfapi4)): its downstream closure (53 modules),
# fresh .oleans into oleans-lscp, a copy of oleans-lnfapi4, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-scpc"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lscp.txt"
LOG="$S/fills/replay/replay-lscp.log"
PINS="TCSlib/Complexity/SpaceComplexity/Constructible.lean:791f3a48d1198a2c7034ca3afd5e38099a21c9e1
TCSlib/Complexity/SpaceComplexity/Savitch.lean:6ea81136926b2d85f0371a16ca9f21598b258012"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/scp-constructible 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor b7f69d00e3a5b01d6fee89ad061968899f6572c8 HEAD || { echo "precheck: the head must contain the campaign tip after #174 (the tree of oleans-lnfapi4); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only b7f69d00e3a5b01d6fee89ad061968899f6572c8 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #174 (the tree of oleans-lnfapi4) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lnfapi4.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "53" ] || { echo "precheck: the replay list must have 53 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lscp" ] && { echo "precheck: $S/oleans-lscp already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lnfapi4" ] || { echo "precheck: oleans-lnfapi4 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lnfapi4" "$S/oleans-lscp" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lscp at $(git rev-parse --short HEAD): the SCP move to Constructible ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lscp"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lscp nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
