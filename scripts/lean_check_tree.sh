#!/usr/bin/env bash
# Check one TCSlib module with a direct `lean` invocation (NOT `lake build`,
# which stays banned on the Arora-Barak branch — see AroraBarakChapter1Plan.md,
# decision log), emitting its .olean into a scratch tree so that dependent
# modules can be checked afterwards.
#
# Usage:   scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Composition
#          (module path relative to the repo root, WITHOUT the .lean extension)
# Sweep:   ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
#              < scripts/ab_ch1_module_order.txt )
#          The subshell makes the whole sweep exit nonzero on the first failing
#          module (a bare `|| break` would hide the failure in the overall
#          status — epoch-1 audit, finding 1).
#
# Modules must be checked in dependency order (imports first) the first time:
# a fresh clone bootstraps by running the sweep above once, after
# `lake exe cache get` has populated the mathlib build cache. Afterwards,
# re-check the file you changed plus everything after it in the order list.
#
# Pass = exit 0, which requires ALL of (epoch-1 audit, finding 1):
#   - the `lean` process itself exited 0 (a crash without diagnostics fails),
#   - no "error:" line in its output,
#   - a fresh .olean was produced (the stale one is removed up front, so a
#     leftover from an earlier run can never satisfy this check).
# "declaration uses 'sorry'" warnings are expected wherever sorries remain.
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
rm -f "$OL/$rel.olean"
out_log="$(mktemp)"
lean "$rel.lean" -o "$OL/$rel.olean" >"$out_log" 2>&1
status=$?
cat "$out_log"
fail=0
if [ "$status" -ne 0 ]; then
  echo "FAIL($rel): lean exited with status $status"
  fail=1
fi
if grep -q "error:" "$out_log"; then
  echo "FAIL($rel): error diagnostics reported"
  fail=1
fi
if [ ! -s "$OL/$rel.olean" ]; then
  echo "FAIL($rel): no fresh .olean produced"
  fail=1
fi
rm -f "$out_log"
exit "$fail"
