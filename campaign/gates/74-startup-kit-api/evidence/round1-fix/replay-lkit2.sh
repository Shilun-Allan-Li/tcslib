#!/usr/bin/env bash
# Replay lkit2 (the interpreter's startup kit: Build/InterpreterStartup, NDCodeSimulator and NTimeHierarchy re-pointed; branch lean/startup-kit, stacked on the campaign tip after #161 (the tree of oleans-lu2api)): its downstream closure (5 modules),
# fresh .oleans into oleans-lkit2, a copy of oleans-lu2api, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-kit"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lkit2.txt"
LOG="$S/fills/replay/replay-lkit2.log"
PINS="TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:a99d95dbe67c0419d8f410dfb1b0cd183ab80fac
TCSlib/Complexity/TuringMachine.lean:bee4b566d8d7b17476cb97344aa4d144c05d0718
TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean:7f51abe08cc628c9a22fa3c11c4445aed918921e
TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean:3d012dde0a11348caeda59e466f14841d2c7d413"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/startup-kit 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 8c247ccb199715c263315db0b71fe755eed29533 HEAD || { echo "precheck: the head must contain the campaign tip after #161 (the tree of oleans-lu2api); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 8c247ccb199715c263315db0b71fe755eed29533 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #161 (the tree of oleans-lu2api) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lu2api.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "5" ] || { echo "precheck: the replay list must have 5 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lkit2" ] && { echo "precheck: $S/oleans-lkit2 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lu2api" ] || { echo "precheck: oleans-lu2api is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lu2api" "$S/oleans-lkit2" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lkit2 at $(git rev-parse --short HEAD): the interpreter's startup kit: Build/InterpreterStartup, NDCodeSimulator and NTimeHierarchy re-pointed ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lkit2"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lkit2 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
