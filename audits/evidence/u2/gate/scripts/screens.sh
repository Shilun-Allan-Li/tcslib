#!/usr/bin/env bash
# Copy-text screens of the U2 unit, before and after, one at a time and niced. The screen is the
# path-keyed v2 (audits/evidence/retrofit/copy-text-screen-v2.py at 186286f7, verbatim).
# Usage: bash screens.sh <G>   (<G> = this folder). Read-only on base/ and landed/.
set -euo pipefail
G="$1"; SC="$G/scripts"; A="$G/work/screen-after"; TM=TCSlib/Complexity/TuringMachine
P=($TM/Build/StepBlockLoop.lean $TM/Build/StepBlock.lean $TM/SelfUniversal.lean $TM/Codes2Tape.lean
   $TM/Encoding.lean $TM/UniversalStartup.lean $TM/Build/InputDevice.lean $TM/CodeSimulator.lean)
rm -rf "$A"
for f in "${P[@]}"; do mkdir -p "$A/$(dirname "$f")"; cp "$G/base/$f" "$A/$f"; done
for f in Build/StepBlockLoop.lean SelfUniversal.lean Codes2Tape.lean UniversalK.lean; do
  cp "$G/landed/$TM/$f" "$A/$TM/$f"; done
hdr() { echo "# U2 unit: copy-text screen (v2), $1"; echo
  echo "\`nice -n 10 python3 -I scripts/copy-text-screen-v2.py <root> <files>\`. Root: $2."
  echo "Files: $3"; echo; }
{ hdr "before (the base)" "<G>/base" "${P[*]}"
  nice -n 10 python3 -I "$SC/copy-text-screen-v2.py" "$G/base" "${P[@]}"; } > "$G/logs/screen-before.txt"
{ hdr "after (the landed files; UniversalK added)" "<G>/work/screen-after" "${P[*]} $TM/UniversalK.lean"
  nice -n 10 python3 -I "$SC/copy-text-screen-v2.py" "$A" "${P[@]}" "$TM/UniversalK.lean"; } \
  > "$G/logs/screen-after.txt"
echo "wrote logs/screen-before.txt and logs/screen-after.txt"
