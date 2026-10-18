#!/usr/bin/env bash
# The G2–G4 landing's copy-text screens (v3, audits/evidence/retrofit/copy-text-screen-v3.py verbatim),
# before (the tip) and after (the landed files), on the gate's population, one at a time and niced.
# Usage: bash screens3.sh <L>   (<L> = the landing folder). Read-only on work/base and landed/.
set -euo pipefail
G="$1"; SC="$G/scripts"; B=TCSlib/Complexity/TuringMachine/Build; mkdir -p "$G/logs"
P0=($B/Zone.lean $B/Catalog.lean $B/Contract/Catalog.lean)
P1=($B/Zone.lean $B/ZoneTape.lean $B/ZoneRebalance.lean $B/Catalog.lean $B/Contract/Catalog.lean)
hdr() { echo "# §13d G2–G4 landing: copy-text screen (v3), $1"; echo
  echo "\`nice -n 10 python3 -I scripts/copy-text-screen-v3.py <root> <files>\`. Root: $2. Files: $3"; echo; }
{ hdr "before (the tip)" "<G>/work/base" "${P0[*]}"
  nice -n 10 python3 -I "$SC/copy-text-screen-v3.py" "$G/work/base" "${P0[@]}"; } > "$G/logs/screen-before.txt"
{ hdr "after (the landed files)" "<G>/landed" "${P1[*]}"
  nice -n 10 python3 -I "$SC/copy-text-screen-v3.py" "$G/landed" "${P1[@]}"; } > "$G/logs/screen-after.txt"
{ python3 -I "$SC/screendelta.py" "$G/logs/screen-before.txt" "$G/logs/screen-after.txt"
  python3 -I "$SC/pairdiff.py" "$G/logs/screen-after.txt" "$G/logs/screen-before.txt"; } > "$G/logs/screen-delta.log"
echo "wrote logs/screen-{before,after}.txt and logs/screen-delta.log"
