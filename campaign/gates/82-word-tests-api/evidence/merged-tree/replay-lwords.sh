#!/usr/bin/env bash
# Replay lwords (the linear word tests, on the tree after #170; branch lean/word-tests, stacked on the campaign tip after #170 (oleans-lb5am's tree, with Relativization's docstring-only change rebuilt in this closure)): its downstream closure (18 modules),
# fresh .oleans into oleans-lwords, a copy of oleans-lb5am, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-words"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lwords.txt"
LOG="$S/fills/replay/replay-lwords.log"
PINS="TCSlib/Complexity/ClassNP/Nondeterminism.lean:176c80af59cc581953c2b562ab8b655917e1644d
TCSlib/Complexity/ClassNP/TMSAT.lean:03e2fae7ee3d9ad5d8d186efa47db0cd6e76c763
TCSlib/Complexity/Diagonalization/EXPCOM.lean:9f313ea73ec641c6de0120f58a69c212a1068dcb
TCSlib/Complexity/TuringMachine.lean:680a63000c60e697751c6a6b61d892614fde3fbb
TCSlib/Complexity/TuringMachine/Build/WordTests.lean:9c5a09482f27f4388dd6da98ae8a8ffaba41fc1a"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/word-tests 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor ba2441f71b013c5594bd6cad2b2f422fdc050c21 HEAD || { echo "precheck: the head must contain the campaign tip after #170 (oleans-lb5am's tree, with Relativization's docstring-only change rebuilt in this closure); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only ba2441f71b013c5594bd6cad2b2f422fdc050c21 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #170 (oleans-lb5am's tree, with Relativization's docstring-only change rebuilt in this closure) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lb5am.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "18" ] || { echo "precheck: the replay list must have 18 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lwords" ] && { echo "precheck: $S/oleans-lwords already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lb5am" ] || { echo "precheck: oleans-lb5am is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lb5am" "$S/oleans-lwords" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lwords at $(git rev-parse --short HEAD): the linear word tests, on the tree after #170 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lwords"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lwords nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
