#!/usr/bin/env bash
# Replay lnfapi3 (NF's NDHost API, the generalized host and writer, on the tree after #172; branch lean/nf-ndhost-api, stacked on the campaign tip after #172 (the tree of oleans-lhh)): its downstream closure (4 modules),
# fresh .oleans into oleans-lnfapi3, a copy of oleans-lhh, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-nfapi"
LIST="/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/down-lnfapi3.txt"
LOG="$S/fills/replay/replay-lnfapi3.log"
PINS="TCSlib/Complexity/TuringMachine/Build/NDHost.lean:958b6ee40e68190dadaf6ad3a655ecb535bb3831"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/nf-ndhost-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor a63188dd46dc41f5c2c31e2e6e267953c92d8aca HEAD || { echo "precheck: the head must contain the campaign tip after #172 (the tree of oleans-lhh); nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only a63188dd46dc41f5c2c31e2e6e267953c92d8aca HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign tip after #172 (the tree of oleans-lhh) must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/fills/replay/replay-lhh.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "4" ] || { echo "precheck: the replay list must have 4 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lnfapi3" ] && { echo "precheck: $S/oleans-lnfapi3 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lhh" ] || { echo "precheck: oleans-lhh is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lhh" "$S/oleans-lnfapi3" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lnfapi3 at $(git rev-parse --short HEAD): NF's NDHost API, the generalized host and writer, on the tree after #172 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lnfapi3"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lnfapi3 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
