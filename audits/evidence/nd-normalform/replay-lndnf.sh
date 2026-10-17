#!/usr/bin/env bash
# Chained replay for #120, C1's normal form in its own module (lean/nd-normalform at 6d18902f, stacked
# on #119's 1e45f50a): ClassNP/NDNormalForm (new), Diagonalization/NTimeHierarchy, the ClassNP facade and
# their downstream closure (4 modules, graph2.py), fresh .oleans into oleans-lndnf, a copy of
# oleans-lndapi (#119's replay, 189 of 189), via scripts/lean_check_tree.sh. The root TCSlib module is
# not listed (replay rule). Run by the user. The precheck pins the three files' blob hashes.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-ndnf"
LIST="$S/fills/replay/down-lndnf.txt"
LOG="$S/fills/replay/replay-lndnf.log"
PINS="TCSlib/Complexity/ClassNP.lean:e411fb17c5320cc092250cde41117ebab2a45d36
TCSlib/Complexity/ClassNP/NDNormalForm.lean:5150734a89b935396dee9516911030497f2034d1
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:cbb0cef88552c147346a2128ce0f76f9638e9859"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/nd-normalform 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 1e45f50a3b7c80db7e817eb3f9e06ae72b18235b HEAD || { echo "precheck: the head must contain #119's 1e45f50a; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 1e45f50a3b7c80db7e817eb3f9e06ae72b18235b HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 1e45f50a must be exactly the three files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lndapi.log" 2>/dev/null | grep -qx "# modules=189 failed=0" || { echo "precheck: #119's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "4" ] || { echo "precheck: the replay list must have 4 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lndnf" ] && { echo "precheck: $S/oleans-lndnf already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lndapi" "$S/oleans-lndnf" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lndnf at $(git rev-parse --short HEAD): NDNormalForm, NTimeHierarchy, the ClassNP facade and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lndnf"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lndnf nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
