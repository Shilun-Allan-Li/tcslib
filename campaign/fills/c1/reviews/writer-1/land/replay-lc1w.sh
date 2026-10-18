#!/usr/bin/env bash
# Replay for C1-W's landing (lean/c1-writer, stacked on #122's head 6a48b93e): Build/NDHost and its
# downstream closure (2 modules: NDHost and the TuringMachine facade), fresh .oleans into
# oleans-lc1w, a copy of oleans-lndapi2 (#122's replay), via scripts/lean_check_tree.sh. The root
# TCSlib module is not listed (replay rule). Run by the user. The precheck pins the two
# files' blobs (NDHost and the facade's NDHost entry).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-landw"
LIST="$S/fills/replay/down-lc1w.txt"
LOG="$S/fills/replay/replay-lc1w.log"
PINS="TCSlib/Complexity/TuringMachine.lean:674829501182bb9d3706637cc715cfbd7d5cec45
TCSlib/Complexity/TuringMachine/Build/NDHost.lean:034ef7d91e8423d844561fc117c83e86bb68b3de"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/c1-writer 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 6a48b93eec0b4fa47c0078d25ecdd712a4fe3605 HEAD || { echo "precheck: the head must contain #122's head 6a48b93e; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 6a48b93eec0b4fa47c0078d25ecdd712a4fe3605 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 0a5878ed must be exactly NDHost and the TuringMachine facade; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lndapi2.log" 2>/dev/null | grep -qx "# modules=313 failed=0" || { echo "precheck: #122's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lc1w" ] && { echo "precheck: $S/oleans-lc1w already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lndapi2" ] || { echo "precheck: oleans-lndapi2 is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lndapi2" "$S/oleans-lc1w" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lc1w at $(git rev-parse --short HEAD): NDHost and its downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lc1w"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lc1w nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
