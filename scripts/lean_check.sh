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
# During a policy cleanup, fresh oleans of restructured modules live in cleanup/.olean
# (seeded with symlinks to .lake by scripts/policy_build.py); they must come first.
if [[ -d cleanup/.olean/TCSlib ]]; then
  python3 -c 'import sys; sys.path.insert(0, "scripts"); from policy_build import seed_scratch; seed_scratch()'
  LP="$ROOT/cleanup/.olean:$LP"
fi
export LEAN_PATH="$LP"

LEANBIN="$(which lean)"
# One lean process at a time machine-wide (shared with scripts/leanlock.py).
LOCK="$ROOT/cleanup/.lean.lock"
mkdir -p "$ROOT/cleanup"
while ! mkdir "$LOCK" 2>/dev/null; do
  pid="$(cat "$LOCK/pid" 2>/dev/null)"
  if [[ -n "$pid" ]] && ! kill -0 "$pid" 2>/dev/null; then rm -rf "$LOCK"; continue; fi
  sleep 2
done
echo $$ > "$LOCK/pid"
trap 'rm -rf "$LOCK"' EXIT
"$LEANBIN" "$1" 2>&1
