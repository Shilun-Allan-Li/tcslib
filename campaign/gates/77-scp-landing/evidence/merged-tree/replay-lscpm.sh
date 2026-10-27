#!/usr/bin/env bash
# Replay lscpm (Savitch's spaceConstructible_poly, on the tree after #167; branch lean/scp-landing, stacked on the campaign tip after #167 (the tree of oleans-lriseqm)): its downstream closure (2 modules),
# fresh .oleans into oleans-lscpm, a copy of oleans-lriseqm, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=$S
WT="$S/wt-scp"
LIST="$S/fills/replay/down-lscpm.txt"
LOG="$S/fills/replay/replay-lscpm.log"
PINS="TCSlib/Complexity/SpaceComplexity/Savitch.lean:07634370100052e10c0910ea94d80e616f524d98"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/scp-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 4c8c2e7e9ac3c0bd063cb3df074558de073bf7bf HEAD || { echo "precheck: the head must contain the campaign tip after #167 (the tree of oleans-lriseqm); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 4c8c2e7e9ac3c0bd063cb3df074558de073bf7bf HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #167 (the tree of oleans-lriseqm) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lriseqm.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lscpm" ] && { echo "precheck: $S/oleans-lscpm already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lriseqm" ] || { echo "precheck: oleans-lriseqm is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lriseqm" "$S/oleans-lscpm" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lscpm at $(git rev-parse --short HEAD): Savitch's spaceConstructible_poly, on the tree after #167 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lscpm"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lscpm nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
