#!/usr/bin/env bash
# Elaborate Lean files read-only, only through <S>/tools/leanelab.sh (no -o, no olean written).
# Usage: bash elab.sh <S> <packages worktree> <olean snapshot> <outdir> <jobs> <file.lean>...
# For each file F: <outdir>/<basename F>.out (stdout and stderr), .exit and .secs.
set -eo pipefail
S="$1"; WT="$2"; OL="$3"; OUT="$4"; JOBS="$5"; shift 5
mkdir -p "$OUT"
one() {
  local f="$1" b; b=$(basename "$f")
  local t0; t0=$(date +%s)
  if bash "$S/tools/leanelab.sh" "$WT" "$OL" "$f" > "$OUT/$b.out" 2>&1; then
    echo 0 > "$OUT/$b.exit"
  else
    echo $? > "$OUT/$b.exit"
  fi
  echo "$(( $(date +%s) - t0 ))" > "$OUT/$b.secs"
}
export -f one; export S WT OL OUT
printf '%s\n' "$@" | xargs -P "$JOBS" -I{} bash -c 'one "$@"' _ {}
