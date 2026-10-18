#!/usr/bin/env bash
# Chained replay for #121, C1-E's statements (lean/ntime-diag at 13f52659, stacked on #120's
# 6d18902f): Diagonalization/NTimeDiagonalizer (new) and the Diagonalization facade (2 modules,
# graph2.py), fresh .oleans into oleans-lndiag, a copy of oleans-lndnf (#120's replay, 4 of 4), via
# scripts/lean_check_tree.sh. The root TCSlib module is not listed (replay rule). Run by the user.
# The precheck pins the two files' blob hashes.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-ndiag"
LIST="$S/fills/replay/down-lndiag.txt"
LOG="$S/fills/replay/replay-lndiag.log"
PINS="TCSlib/Complexity/Diagonalization.lean:43b823046c16de361fef9074a2cde4ac63f0e908
TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean:29eaf7934f868564a28bc7681928c0038ebb8bbe"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/ntime-diag 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 6d18902f3453eb51be6178d5542304bbafe3302a HEAD || { echo "precheck: the head must contain #120's 6d18902f; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 6d18902f3453eb51be6178d5542304bbafe3302a HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 6d18902f must be exactly the two files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lndnf.log" 2>/dev/null | grep -qx "# modules=4 failed=0" || { echo "precheck: #120's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "2" ] || { echo "precheck: the replay list must have 2 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lndiag" ] && { echo "precheck: $S/oleans-lndiag already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lndnf" "$S/oleans-lndiag" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lndiag at $(git rev-parse --short HEAD): NTimeDiagonalizer, the Diagonalization facade and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lndiag"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lndiag nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
