#!/usr/bin/env bash
# Replay laplusm (the interpreter startup (A+), on the tree after #168; branch lean/interpreter-startup, stacked on the campaign tip after #168 (the tree of oleans-lu2m)): its downstream closure (5 modules),
# fresh .oleans into oleans-laplusm, a copy of oleans-lu2m, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-aplus"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-laplusm.txt"
LOG="$S/fills/replay/replay-laplusm.log"
PINS="TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean:84c00e33d146df824aa94f2e0aed87593a4014ba
TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:baf1b4543600e6f302af4c2996407cde22370218"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/interpreter-startup 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 13120e0067ce19ee9c09809ef6578f2b38139cf6 HEAD || { echo "precheck: the head must contain the campaign tip after #168 (the tree of oleans-lu2m); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 13120e0067ce19ee9c09809ef6578f2b38139cf6 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #168 (the tree of oleans-lu2m) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lu2m.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "5" ] || { echo "precheck: the replay list must have 5 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-laplusm" ] && { echo "precheck: $S/oleans-laplusm already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lu2m" ] || { echo "precheck: oleans-lu2m is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lu2m" "$S/oleans-laplusm" || exit 1
cd "$WT" || exit 1
{ echo "# replay-laplusm at $(git rev-parse --short HEAD): the interpreter startup (A+), on the tree after #168 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-laplusm"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-laplusm nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
