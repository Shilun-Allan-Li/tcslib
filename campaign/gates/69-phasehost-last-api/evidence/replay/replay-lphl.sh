#!/usr/bin/env bash
# Replay lphl (#156, the phase host's last phase, on the tree after #155; branch lean/phasehost-last, stacked on #155's head (6efc5be0, the tree of oleans-lslsk)): its downstream closure (88 modules),
# fresh .oleans into oleans-lphl, a copy of oleans-lslsk, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-phlast"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lphl.txt"
LOG="$S/fills/replay/replay-lphl.log"
PINS="TCSlib/Complexity/TuringMachine/Build/Seam.lean:872703b7f24ad29ddbb136752d20680608fb001e"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/phasehost-last 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 6efc5be0a682b7fe1c831fbff49c22839f67ad24 HEAD || { echo "precheck: the head must contain #155's head (6efc5be0, the tree of oleans-lslsk); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 6efc5be0a682b7fe1c831fbff49c22839f67ad24 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #155's head (6efc5be0, the tree of oleans-lslsk) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lslsk.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "88" ] || { echo "precheck: the replay list must have 88 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lphl" ] && { echo "precheck: $S/oleans-lphl already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lslsk" ] || { echo "precheck: oleans-lslsk is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lslsk" "$S/oleans-lphl" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lphl at $(git rev-parse --short HEAD): #156, the phase host's last phase, on the tree after #155 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lphl"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lphl nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
