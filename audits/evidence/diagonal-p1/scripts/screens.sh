#!/usr/bin/env bash
# Copy-text screens of Diagonal Part 1, before and after, one at a time and niced (maintainer's
# CPU rule). Read-only on the base; python3 -I only. The screen script is the retrofit screen v3,
# verbatim (audits/evidence/retrofit/copy-text-screen-v3.py): declaration-keyed, so the generic
# proofs are compared with their same-named received counterparts (gate m2; v1 skipped them).
# Usage: bash screens.sh <D>   (<D> = this folder; the population is scripts/screen-population.txt)
set -euo pipefail
D="$1"; SC="$D/scripts"; A="$D/work/screen-after"
P=(); while read -r f; do P+=("$f"); done < "$SC/screen-population.txt"
[ "${#P[@]}" = 7 ] || { echo "screen population: expected 7 files, got ${#P[@]}"; exit 1; }
rm -rf "$A"
for f in "${P[@]}"; do mkdir -p "$A/$(dirname "$f")"; cp "$D/base/$f" "$A/$f"; done
cp "$D/tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean" "$A/TCSlib/Complexity/TimeHierarchy/Diagonal.lean"
hdr() {
  echo "# Diagonal Part 1: copy-text screen, $1"
  echo
  echo "\`nice -n 10 python3 -I scripts/copy-text-screen-v3.py <root> <files>\` (the retrofit"
  echo "screen v3, verbatim). Root: $2. Population (the edited file, its directory, and the two files"
  echo "that cite its argument's idioms): ${P[*]}."
  echo
}
{ hdr "before (the base)" "<D>/base"
  nice -n 10 python3 -I "$SC/copy-text-screen-v3.py" "$D/base" "${P[@]}"; } > "$D/logs/screen-before.txt"
{ hdr "after (the landed Diagonal.lean, the rest from the base)" "<D>/work/screen-after"
  nice -n 10 python3 -I "$SC/copy-text-screen-v3.py" "$A" "${P[@]}"; } > "$D/logs/screen-after.txt"
echo "wrote logs/screen-before.txt and logs/screen-after.txt"
