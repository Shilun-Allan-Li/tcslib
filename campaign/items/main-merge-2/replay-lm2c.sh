#!/usr/bin/env bash
# Replay lm2c: the ROOT BUILD of the merged tree (main into the campaign, PR #179, before the second
# merge to main): the root's whole import closure (887 modules, the root TCSlib last), compiled fresh
# into the empty snapshot oleans-lm2c via scripts/lean_check_tree.sh. The root is listed on purpose
# (a merge to main needs it; as the 2026-10-15 root-build replay). Exits nonzero on any failure.
# Interrupted? Run it again with --resume: it keeps oleans-lm2c, skips every module the log already
# records as passed (exit=0; a module's olean exists only if its check passed, and the head is
# pinned), and continues from the first module that is not, appending to the log.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$S/wt-m2c"
LIST="$S/fills/replay/down-lm2c.txt"
LOG="$S/fills/replay/replay-lm2c.log"
HEAD_PIN=76ad1933296e17389b2d0fff4a94fcbb809d8adf
N=887
MODE="${1:-}"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing done" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$HEAD_PIN" ] || { echo "precheck: $WT is not at $HEAD_PIN; nothing done" >&2; exit 2; }
[ "$(git -C "$WT" rev-parse origin/integrate/main-into-campaign-2)" = "$HEAD_PIN" ] || { echo "precheck: the pushed branch is not at $HEAD_PIN; nothing done" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing done" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "$N" ] || { echo "precheck: the list must have $N modules; nothing done" >&2; exit 2; }
[ "$(tail -1 "$LIST")" = "TCSlib" ] || { echo "precheck: the list must end with the root; nothing done" >&2; exit 2; }
if [ "$MODE" = "--resume" ]; then
  [ -d "$S/oleans-lm2c" ] && [ -f "$LOG" ] || { echo "precheck: --resume needs oleans-lm2c and the log of an earlier run; nothing done" >&2; exit 2; }
  head -1 "$LOG" | grep -q "^# replay-lm2c at ${HEAD_PIN:0:8}" || { echo "precheck: the log is not this head's run; nothing done" >&2; exit 2; }
else
  [ -d "$S/oleans-lm2c" ] && { echo "precheck: $S/oleans-lm2c already exists: use --resume to continue, or remove it for a fresh build" >&2; exit 2; }
fi
[ "$MODE" = "--precheck" ] && { echo PRECHECK-PASSED; exit 0; }
DONE=$(mktemp)
if [ "$MODE" = "--resume" ]; then
  grep -E '^TCSlib[^ ]* exit=0 ' "$LOG" | cut -d' ' -f1 > "$DONE"
  echo "# resumed $(date): $(wc -l < "$DONE" | tr -d ' ') modules already passed" >> "$LOG"
else
  mkdir -p "$S/oleans-lm2c" || exit 1
  echo "# replay-lm2c at $(git -C "$WT" rev-parse --short=8 HEAD): the merged tree's root build ($N modules), fresh .oleans into oleans-lm2c, started $(date)" > "$LOG"
fi
cd "$WT" || exit 1
{ f=0
  while read -r m; do
    grep -qxF "$m" "$DONE" && continue
    out=$(TCSLIB_OLEANS=$S/oleans-lm2c nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    echo "$m exit=$st errors=$(printf '%s\n' "$out" | grep -c "error") sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
} >> "$LOG" 2>&1
rm -f "$DONE"
# the summary counts the whole list: a module passes once it has an exit=0 line (its latest run)
P=$(grep -E '^TCSlib[^ ]* exit=' "$LOG" | awk '{print $1, $2}' | awk '{last[$1]=$2} END{for (m in last) if (last[m]=="exit=0") c++; print c+0}')
{ echo "# finished $(date)"; echo "# modules=$N failed=$((N-P))"; } >> "$LOG"
tail -n 4 "$LOG"
tail -1 "$LOG" | grep -qx "# modules=$N failed=0" || { echo "replay: a module failed or was not reached" >&2; exit 1; }
exit 0
