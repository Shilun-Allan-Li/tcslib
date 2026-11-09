#!/usr/bin/env bash
# Replay mfe-live1-final (FE-LIVE-1 final five-owner closure; branch codex/ab34-fe-live1, stacked on MAC8 baseline): its downstream closure (163 modules),
# fresh .oleans into oleans-fe-live1-final, a copy of oleans-mac8, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch
WT="$S/wt-followup"
LIST="/private/tmp/ab34-fe-live1-final-validation/evidence/replay-order.txt"
LOG="$S/fills/replay/replay-mfe-live1-final.log"
PINS="TCSlib/Complexity/ClassNP/EXP.lean:03e2b27d17e0f58e91f4165d5d31dc842e1c92cd
TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean:82df1342d444db11bfebb278df4f2d67b15040a0
TCSlib/Complexity/CookLevin/Hardness.lean:cffad874af02e21d342021bb516b1ff175937e9e
TCSlib/Complexity/TuringMachine/Build/InputCall.lean:fe1fe8badb95cd73a1563243bda0f4c1d4707a21
TCSlib/Complexity/TuringMachine/Build/InputLength.lean:78c2a820dfd427d51ce8c0b4d855bf5b1d82b331"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/codex/ab34-fe-live1 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 9b5dcf46408db681bcbc721930ef2203fa6bc47d HEAD || { echo "precheck: the head must contain MAC8 baseline; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 9b5dcf46408db681bcbc721930ef2203fa6bc47d HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from MAC8 baseline must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/fills/replay/replay-mjoint1.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "163" ] || { echo "precheck: the replay list must have 163 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-fe-live1-final" ] && { echo "precheck: $S/oleans-fe-live1-final already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-mac8" ] || { echo "precheck: oleans-mac8 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-mac8" "$S/oleans-fe-live1-final" || exit 1
cd "$WT" || exit 1
{ echo "# replay-mfe-live1-final at $(git rev-parse --short HEAD): FE-LIVE-1 final five-owner closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-fe-live1-final"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-fe-live1-final nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"; sst=$?
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
# the exit status: nonzero unless every listed module passed and the static check found no mismatch
tail -1 "$LOG" | grep -qx "# modules=163 failed=0" || { echo "replay: a module failed, or the count is not 163" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
