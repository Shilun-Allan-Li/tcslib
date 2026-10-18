#!/usr/bin/env bash
# Chained replay for #118's round 3 (prepared locally on the user's ruling of 2026-10-17; run after the push): lean/brief-api
# at a local head that adds exactly the round-3 patches on top of round 2's pushed head 4624fc05:
# `r3-repair.patch` (Configuration and Deterministic, the machine model's live-step API) and
# `r3-repair-2.patch` (Build/CounterLoop and Build/Catalog, the two private-only laws).
# The four files' downstream closure (320 modules; the closure of Configuration alone, since the
# other three are downstream of it), fresh .oleans into oleans-lbapi4, a copy of
# oleans-lbapi3 (round 2's replay at 4624fc05, 274 of 274), via scripts/lean_check_tree.sh.
# The root TCSlib module is not listed (replay rule). Run by the user. Drafted by the round-3 review;
# the precheck pins the four files' blob hashes to the reviewed patches.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-bapi"
LIST="$S/fills/replay/down-lbapi4.txt"
LOG="$S/fills/replay/replay-lbapi4.log"
T=TCSlib/Complexity/TuringMachine
PINS="$T/Build/Catalog.lean:c2802df79735b55693fa060ab0c257bacc7c682b
$T/Build/CounterLoop.lean:963a97ec6daeefea5e62f957fbeb198e0ce36b3e
$T/Configuration.lean:a9f14a780c7702a5262aea9cb37ca0e19b6f8810
$T/Deterministic.lean:efd291b1605e49546badd471ed5b8c0152071d93"
# Prechecks before anything is copied.
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/brief-api 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head (push round 3 first); nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 4624fc05aac80943646e5f0ad393ce0acba60086 HEAD || { echo "precheck: the head must contain round 2's 4624fc05; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 4624fc05aac80943646e5f0ad393ce0acba60086 HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from 4624fc05 must be exactly the four round-3 files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the reviewed round-3 blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "$S/fills/replay/replay-lbapi3.log" 2>/dev/null | grep -qx "# modules=274 failed=0" || { echo "precheck: round 2's replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "320" ] || { echo "precheck: the replay list must have 320 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lbapi4" ] && { echo "precheck: $S/oleans-lbapi4 already exists; remove it for a fresh copy" >&2; exit 2; }
cp -R "$S/oleans-lbapi3" "$S/oleans-lbapi4" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lbapi4 at $(git rev-parse --short HEAD): Configuration, Deterministic, Build/CounterLoop, Build/Catalog and their downstream closure ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lbapi4"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lbapi4 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"
tail -n 12 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
