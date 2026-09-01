#!/bin/zsh
# Direct `lean` invocation on one file (NOT `lake build`) — the same verification
# path the #67 real-file gate uses inside ExtractHavesFile.lean.
# Usage: scripts/lean_check.sh <file.lean>
# Prints Lean diagnostics on stdout; exits nonzero if any "error:" line is present.
set -u
ROOT="${0:A:h}/.."
cd "$ROOT"

LP=".lake/build/lib/lean"
for d in .lake/packages/*/.lake/build/lib/lean(N); do
  LP="$LP:$d"
done
export LEAN_PATH="$LP"

LEANBIN="$(which lean)"
"$LEANBIN" "$1" 2>&1
