#!/usr/bin/env bash
# Replay lg4c4m (G4 continuation 4 on the tree after #162: the zone rows and the TuringMachine facade; branch lean/g4-cont4-landing, stacked on the campaign tip after #162 (the tree of oleans-lkit2)): its downstream closure (2 modules),
# fresh .oleans into oleans-lg4c4m, a copy of oleans-lkit2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=$S
WT="$S/wt-g4c4land"
LIST="$S/fills/replay/down-lg4c4m.txt"
LOG="$S/fills/replay/replay-lg4c4m.log"
PINS="TCSlib/Complexity/TuringMachine.lean:a9581842178c9aec3ee2cbbd1b5608fa01fa0012
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:00b88de35a1945c72747b2e5f2a4c31fee525f53"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/g4-cont4-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 5a258cc2116dc7b761772a9bb6d9caa675243866 HEAD || { echo "precheck: the head must contain the campaign tip after #162 (the tree of oleans-lkit2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 5a258cc2116dc7b761772a9bb6d9caa675243866 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #162 (the tree of oleans-lkit2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lkit2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg4c4m" ] && { echo "precheck: $S/oleans-lg4c4m already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lkit2" ] || { echo "precheck: oleans-lkit2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lkit2" "$S/oleans-lg4c4m" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg4c4m at $(git rev-parse --short HEAD): G4 continuation 4 on the tree after #162: the zone rows and the TuringMachine facade ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg4c4m"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg4c4m nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
