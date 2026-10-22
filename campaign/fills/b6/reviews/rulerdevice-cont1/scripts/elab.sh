#!/usr/bin/env bash
# usage: elab.sh <worktree> <olean dir> <file> <out>: one elaboration via leanelab.sh, with timing.
S=$S
t0=$(date +%s)
bash $S/tools/leanelab.sh "$1" "$2" "$3" > "$4" 2>&1; st=$?
echo "exit $st, $(( $(date +%s) - t0 )) s, $(date '+%F %T'), file $3, oleans $(basename $2), worktree $(basename $1) @ $(git -C $1 rev-parse --short HEAD)" >> "$4"
