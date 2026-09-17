#!/usr/bin/env bash
# Check one TCSlib module with a direct `lean` invocation (NOT `lake build`,
# which stays banned on the Arora-Barak branch — see AroraBarakChapter1Plan.md,
# decision log), emitting its .olean into a scratch tree so that dependent
# modules can be checked afterwards.
#
# Usage:   scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Composition
#          (module path relative to the repo root, WITHOUT the .lean extension)
# Sweep:   while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done \
#            < scripts/ab_ch1_module_order.txt
#
# Modules must be checked in dependency order (imports first) the first time:
# a fresh clone bootstraps by running the sweep above once, after
# `lake exe cache get` has populated the mathlib build cache. Afterwards,
# re-check the file you changed plus everything after it in the order list.
#
# Pass = exit 0 and no "error:" line in the output. "declaration uses 'sorry'"
# warnings are expected wherever sorries legitimately remain.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
OL="${TCSLIB_OLEANS:-$ROOT/.lake/tcslib-check-oleans}"
LP="$OL"
[ -d "$ROOT/.lake/build/lib/lean" ] && LP="$LP:$ROOT/.lake/build/lib/lean"
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do
  [ -d "$d" ] && LP="$LP:$d"
done
export LEAN_PATH="$LP"
rel="$1"
mkdir -p "$OL/$(dirname "$rel")"
out="$(lean "$rel.lean" -o "$OL/$rel.olean" 2>&1)"
printf '%s\n' "$out"
if printf '%s' "$out" | grep -q "error:"; then
  exit 1
fi
exit 0
