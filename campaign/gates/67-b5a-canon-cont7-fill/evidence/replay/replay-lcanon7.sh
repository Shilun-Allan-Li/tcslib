#!/usr/bin/env bash
# Replay lcanon7 (#152, the canonizer cont7 with its re-point, on the tree after #147, #149 to #151 and #153: the closure of every file changed since oleans-lrc2, #150's CfgRecord included; branch lean/b5a-canon-cont7, stacked on #151's head (dbf0ed2a, the tree of oleans-lrc2)): its downstream closure (61 modules),
# fresh .oleans into oleans-lcanon7, a copy of oleans-lrc2, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-cland"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lcanon7.txt"
LOG="$S/fills/replay/replay-lcanon7.log"
PINS="TCSlib/Complexity/Diagonalization/EXPCOM.lean:fde06470d3005d0c40aaa865e327aff0984a75f6
TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean:986ab6b2825a28d0425678229259f193ecaaa4a2
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:c64567f066dfb7ad4e31c489691605e754f16aad
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:59b94de6f7c0669c438f765d0427b04a0052213c"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/b5a-canon-cont7 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor dbf0ed2a32404ab938013318305644b95e1cb526 HEAD || { echo "precheck: the head must contain #151's head (dbf0ed2a, the tree of oleans-lrc2); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only dbf0ed2a32404ab938013318305644b95e1cb526 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from #151's head (dbf0ed2a, the tree of oleans-lrc2) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lrc2.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "61" ] || { echo "precheck: the replay list must have 61 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lcanon7" ] && { echo "precheck: $S/oleans-lcanon7 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lrc2" ] || { echo "precheck: oleans-lrc2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lrc2" "$S/oleans-lcanon7" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lcanon7 at $(git rev-parse --short HEAD): #152, the canonizer cont7 with its re-point, on the tree after #147, #149 to #151 and #153: the closure of every file changed since oleans-lrc2, #150's CfgRecord included ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lcanon7"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lcanon7 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
