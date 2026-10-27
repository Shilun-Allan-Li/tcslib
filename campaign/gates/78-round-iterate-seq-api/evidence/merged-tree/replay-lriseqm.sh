#!/usr/bin/env bash
# Replay lriseqm (Round.iterate_seq and zr_pinLoop's re-point, on the tree after #164; branch lean/round-iterate-seq, stacked on the campaign tip after #164 (the tree of oleans-la1m)): its downstream closure (91 modules),
# fresh .oleans into oleans-lriseqm, a copy of oleans-la1m, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=$S
WT="$S/wt-riseq"
LIST="$S/fills/replay/down-lriseqm.txt"
LOG="$S/fills/replay/replay-lriseqm.log"
PINS="TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean:23c5142d4dbfb246949c71ebc778dfa029c2c762
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean:8b01a3b9d0d50681992e5ae269a26b4c859685fa"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/round-iterate-seq 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor c4ba87bf2f566d645245ef881da22da9dcce5595 HEAD || { echo "precheck: the head must contain the campaign tip after #164 (the tree of oleans-la1m); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only c4ba87bf2f566d645245ef881da22da9dcce5595 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #164 (the tree of oleans-la1m) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-la1m.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "91" ] || { echo "precheck: the replay list must have 91 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lriseqm" ] && { echo "precheck: $S/oleans-lriseqm already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-la1m" ] || { echo "precheck: oleans-la1m is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-la1m" "$S/oleans-lriseqm" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lriseqm at $(git rev-parse --short HEAD): Round.iterate_seq and zr_pinLoop's re-point, on the tree after #164 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lriseqm"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lriseqm nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
