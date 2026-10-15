#!/usr/bin/env bash
# Copy-text screens of Diagonal Part 1, before and after, one at a time and niced (maintainer's
# CPU rule). Read-only on the base; python3 -I only. The screen script is the retrofit screen,
# verbatim (audits/evidence/s13d/g24/scripts/copy-text-screen.py at the base commit).
# Usage: bash screens.sh <D>   (<D> = this folder)
set -euo pipefail
D="$1"; SC="$D/scripts"; A="$D/work/screen-after"
P=(TCSlib/Complexity/TimeHierarchy/Diagonal.lean TCSlib/Complexity/TimeHierarchy/Separation.lean
   TCSlib/Complexity/TimeHierarchy/ClockMachine.lean TCSlib/Complexity/TimeHierarchy/ClockLoop.lean
   TCSlib/Complexity/TimeHierarchy/CodePrefix.lean
   TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
   TCSlib/Complexity/SpaceComplexity/Hierarchy.lean)
rm -rf "$A"
for f in "${P[@]}"; do mkdir -p "$A/$(dirname "$f")"; cp "$D/base/$f" "$A/$f"; done
cp "$D/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean" "$A/TCSlib/Complexity/TimeHierarchy/Diagonal.lean"
hdr() {
  echo "# Diagonal Part 1: copy-text screen, $1"
  echo
  echo "\`nice -n 10 python3 -I scripts/copy-text-screen.py <root> <files>\` (the retrofit screen,"
  echo "verbatim). Root: $2. Population (the edited file, its directory, and the two files that"
  echo "cite its argument's idioms): ${P[*]}."
  echo
}
{ hdr "before (the base)" "<D>/base"; nice -n 10 python3 -I "$SC/copy-text-screen.py" "$D/base" "${P[@]}"; } \
  > "$D/logs/screen-before.txt"
{ hdr "after (the landed Diagonal.lean, the rest from the base)" "<D>/work/screen-after"
  nice -n 10 python3 -I "$SC/copy-text-screen.py" "$A" "${P[@]}"; } > "$D/logs/screen-after.txt"
echo "wrote logs/screen-before.txt and logs/screen-after.txt"
