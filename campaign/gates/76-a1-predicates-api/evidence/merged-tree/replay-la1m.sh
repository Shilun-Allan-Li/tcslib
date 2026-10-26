#!/usr/bin/env bash
# Replay la1m (A1: the chapter predicates' readings, on the tree after #165; branch lean/a1-predicates, stacked on the campaign tip after #165 (the tree of oleans-lg4c4m)): its downstream closure (193 modules),
# fresh .oleans into oleans-la1m, a copy of oleans-lg4c4m, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=$S
WT="$S/wt-a1"
LIST="$S/fills/replay/down-la1m.txt"
LOG="$S/fills/replay/replay-la1m.log"
PINS="TCSlib/Complexity/ClassNP/Transducer.lean:c81498944c2d2c1d2f60c5cc3cad2079178561a6
TCSlib/Complexity/ClassP/TimeConstructible.lean:05c92a4d50ccffe64db88199315d4c00a36d8fbf
TCSlib/Complexity/SpaceComplexity/Basic.lean:46e84e4663c64f2cc5d300aa016b45674ae34f56
TCSlib/Complexity/SpaceComplexity/Constructible.lean:35e5e6e91db9f949ffa07f6f846e7d659f5e958d"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/a1-predicates 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor f0df8ee555dbaa29befbe7ab576e17ccd656c49c HEAD || { echo "precheck: the head must contain the campaign tip after #165 (the tree of oleans-lg4c4m); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only f0df8ee555dbaa29befbe7ab576e17ccd656c49c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #165 (the tree of oleans-lg4c4m) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lg4c4m.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "193" ] || { echo "precheck: the replay list must have 193 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-la1m" ] && { echo "precheck: $S/oleans-la1m already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lg4c4m" ] || { echo "precheck: oleans-lg4c4m is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lg4c4m" "$S/oleans-la1m" || exit 1
cd "$WT" || exit 1
{ echo "# replay-la1m at $(git rev-parse --short HEAD): A1: the chapter predicates' readings, on the tree after #165 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-la1m"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-la1m nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
