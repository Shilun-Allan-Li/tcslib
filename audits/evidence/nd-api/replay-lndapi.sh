#!/usr/bin/env bash
# Chained replay for #119, the ND inventory API (lean/nd-api at 85f2c916, two commits on #118's
# round-3 head 531b98a2): the eight touched files (Nondeterministic, ClassNP/NTIME, ChoiceReplay,
# NDCodes, Build/NDHost, Build/StepClock, Build/StepBlock, Build/VirtualInput) and their downstream
# closure (111 modules, graph2.py), fresh .oleans
# into oleans-lndapi, a copy of oleans-lbapi4 (#118's round-3 replay, 320 of 320), via
# scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule). Run by the user.
# The precheck pins the six files' blob hashes to the checked commit.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-ndapi"
LIST="$S/fills/replay/down-lndapi.txt"
LOG="$S/fills/replay/replay-lndapi.log"
PINS="TCSlib/Complexity/ClassNP/NTIME.lean:1b21c9c519cdc2e85f175456be663953fc482b4b
TCSlib/Complexity/TuringMachine/Build/NDHost.lean:7485a6fa243dea8d865af6e8c522c8b81ffa793d
TCSlib/Complexity/TuringMachine/Build/StepBlock.lean:04e38f625a5e5aed887ef7c1ad25500e750debc1
TCSlib/Complexity/TuringMachine/Build/StepClock.lean:d7e21718bdaad90792c04780ec8f2b6ea8ea86b3
TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean:8e807a61ef1d8a777e6352264e0bc68a07f9b31d
TCSlib/Complexity/TuringMachine/ChoiceReplay.lean:99ff78af182cdae5df54233bc47108243b754592
TCSlib/Complexity/TuringMachine/NDCodes.lean:53ffa79ee6057823849e41187671869a29cc135c
TCSlib/Complexity/TuringMachine/Nondeterministic.lean:9c8d77e5a3dfe08bd91aac62cc5406f109b1d4c9"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/nd-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 531b98a2728d60545e89f15066c542cf708f9bad HEAD || { echo "precheck: the head must contain #118's round-3 head 531b98a2; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 531b98a2728d60545e89f15066c542cf708f9bad HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 531b98a2 must be exactly the eight files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lbapi4.log" 2>/dev/null | grep -qx "# modules=320 failed=0" || { echo "precheck: #118's round-3 replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "111" ] || { echo "precheck: the replay list must have 111 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lndapi" ] && { echo "precheck: $S/oleans-lndapi already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lbapi4" "$S/oleans-lndapi" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lndapi at $(git rev-parse --short HEAD): the ND inventory API's eight files and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lndapi"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lndapi nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
