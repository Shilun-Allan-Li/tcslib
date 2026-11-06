#!/usr/bin/env bash
# Replay ldwa3 (#196 with gate 96's repairs, on the campaign after #197; branch lean/deepen-window-api, stacked on the campaign after #197 (snapshot oleans-lzsa2)): its downstream closure (73 modules),
# fresh .oleans into oleans-ldwa3, a copy of oleans-lzsa2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-196"
LIST="/home/user/tcslib-scratch/fills/replay/down-ldwa3.txt"
LOG="$S/fills/replay/replay-ldwa3.log"
PINS="TCSlib/Complexity/SpaceComplexity.lean:79fd9767cb71a2c52ac214f6c5fd7d59d21f287e
TCSlib/Complexity/SpaceComplexity/Codec/Bridge.lean:6c3353684eac0a6cd5245f70634538398f08eeb1
TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean:bbc05e6d476cbd3fc9faf50b6dc11705c82ede2c
TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean:77d6420ae837696b18b400fed556a94a17046e39
TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean:f9071f8398ce2edf35a29db0cc3a221995108138
TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean:a359ed4d26b2eebddc4e047e02a0c7b038903558
TCSlib/Complexity/SpaceComplexity/SavitchARM/Search.lean:7a3a864c364e51f43a43ddf0c636a7f470456a4c
TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean:60b3453070d7fc36a3059c5bd460abcb9df78c1a
TCSlib/Complexity/SpaceComplexity/SavitchARM/Window.lean:95a88febb191fa1cabe20b88c4cd53cad325fde1
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:c840bc540cd78f19f0d11e28e398e58503eb403a"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/deepen-window-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor df79cdc46f213f49148afda02df5d5479a5dd5e8 HEAD || { echo "precheck: the head must contain the campaign after #197 (snapshot oleans-lzsa2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only df79cdc46f213f49148afda02df5d5479a5dd5e8 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #197 (snapshot oleans-lzsa2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lzsa2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "73" ] || { echo "precheck: the replay list must have 73 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-ldwa3" ] && { echo "precheck: $S/oleans-ldwa3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lzsa2" ] || { echo "precheck: oleans-lzsa2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lzsa2" "$S/oleans-ldwa3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-ldwa3 at $(git rev-parse --short HEAD): #196 with gate 96's repairs, on the campaign after #197 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-ldwa3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-ldwa3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
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
tail -1 "$LOG" | grep -qx "# modules=73 failed=0" || { echo "replay: a module failed, or the count is not 73" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0
