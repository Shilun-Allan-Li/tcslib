#!/usr/bin/env bash
# Replay lb5am (B5a's uniform simulator, on the tree after #169; branch lean/b5a-unisim-landing, stacked on the campaign tip after #169 (the tree of oleans-laplusm)): its downstream closure (10 modules),
# fresh .oleans into oleans-lb5am, a copy of oleans-laplusm, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-b5aland"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lb5am.txt"
LOG="$S/fills/replay/replay-lb5am.log"
PINS="TCSlib/Complexity/Diagonalization/EXPCOM.lean:82990c98e647385d948c4113e7901412d6cf268f
TCSlib/Complexity/Diagonalization/Relativization.lean:5f2b34780f534d045f8048db45b8b9357999d0fc
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:f71f4002384b45d5397b28e955d506bcc3e6938b
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:e0cab06adfd840c1603700377cc4bfdd5f98e254"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/b5a-unisim-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 145202f1eacddfd93407fea8ed57df89aa43f76c HEAD || { echo "precheck: the head must contain the campaign tip after #169 (the tree of oleans-laplusm); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 145202f1eacddfd93407fea8ed57df89aa43f76c HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #169 (the tree of oleans-laplusm) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-laplusm.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "10" ] || { echo "precheck: the replay list must have 10 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lb5am" ] && { echo "precheck: $S/oleans-lb5am already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-laplusm" ] || { echo "precheck: oleans-laplusm is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-laplusm" "$S/oleans-lb5am" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lb5am at $(git rev-parse --short HEAD): B5a's uniform simulator, on the tree after #169 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lb5am"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lb5am nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
