#!/usr/bin/env bash
# elab.sh <worktree> <olean dir> <file relative to worktree or absolute> <out file>
# Runs leanelab.sh once; records the command, start/end time, exit status.
WT="$1"; OL="$2"; F="$3"; OUT="$4"
T=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/tools/leanelab.sh
{
  echo "# command: bash $T $WT $OL $F"
  echo "# start: $(date '+%Y-%m-%d %H:%M:%S')"
} > "$OUT"
bash "$T" "$WT" "$OL" "$F" >> "$OUT" 2>&1
RC=$?
{
  echo "# end: $(date '+%Y-%m-%d %H:%M:%S')"
  echo "# exit: $RC"
} >> "$OUT"
exit $RC
