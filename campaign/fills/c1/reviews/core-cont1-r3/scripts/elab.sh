#!/usr/bin/env bash
# usage: elab.sh <worktree> <olean dir> <file> <out>: one elaboration via leanelab.sh, with timing.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
t0=$(date +%s)
bash $S/tools/leanelab.sh "$1" "$2" "$3" > "$4" 2>&1; st=$?
echo "exit $st, $(( $(date +%s) - t0 )) s, $(date '+%F %T'), file $3, oleans $(basename $2)" >> "$4"
