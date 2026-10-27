#!/usr/bin/env bash
# Replay lu2m (U2's universal machines, on the tree after #166; branch lean/u2-universal-landing, stacked on the campaign tip after #166 (the tree of oleans-lscpm)): its downstream closure (3 modules),
# fresh .oleans into oleans-lu2m, a copy of oleans-lscpm, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=$S
WT="$S/wt-u2land"
LIST="$S/fills/replay/down-lu2m.txt"
LOG="$S/fills/replay/replay-lu2m.log"
PINS="TCSlib/Complexity/TuringMachine.lean:05b6a8b5cef23297c84e424a25df53583c4274b0
TCSlib/Complexity/TuringMachine/SelfUniversal.lean:d1f064d47c683f193b8c0f753a9e34e47dbc74c2
TCSlib/Complexity/TuringMachine/UniversalK.lean:61c420a7495128b9a60384b0c7de0534a69c4522"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/u2-universal-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 26ae1f10d6a480d76dfd5ecf93467dd7fc44abf0 HEAD || { echo "precheck: the head must contain the campaign tip after #166 (the tree of oleans-lscpm); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 26ae1f10d6a480d76dfd5ecf93467dd7fc44abf0 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #166 (the tree of oleans-lscpm) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lscpm.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "3" ] || { echo "precheck: the replay list must have 3 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lu2m" ] && { echo "precheck: $S/oleans-lu2m already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lscpm" ] || { echo "precheck: oleans-lscpm is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lscpm" "$S/oleans-lu2m" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lu2m at $(git rev-parse --short HEAD): U2's universal machines, on the tree after #166 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lu2m"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lu2m nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
