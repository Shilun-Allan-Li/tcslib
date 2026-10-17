#!/usr/bin/env bash
# Closing-commit repair run for the Diagonal P1 gate's minors m1/m2: re-runs only the repaired
# checks of run.sh (names on base and tip, the 9 negative controls, the v3 screens and delta),
# exactly as run.sh's steps 4 (names), 6 and 7 do. The full run.sh runs fresh at the landing tip.
set -euo pipefail
S="$1"; REPO="$2"; OL="$3"; D="$S/diag-p1"; SC="$D/scripts"; W="$D/work"; LG="$D/logs"
REL=TCSlib/Complexity/TimeHierarchy/Diagonal.lean; BASE_REV=$(cat "$D/base/HEAD")
san() { sed "s|$D|<D>|g; s|$S|<S>|g"; }
tip=$(git -C "$REPO" rev-parse origin/complexity/arora-barak-ch3-4)
rm -rf "$W/tipexport"; mkdir -p "$W/tipexport"
git -C "$REPO" archive "$tip" TCSlib TCSlib.lean | tar -x -C "$W/tipexport"
cmp "$W/tipexport/$REL" "$D/base/$REL"
{ echo "# names.py on the base (${BASE_REV:0:8})"
  python3 -I "$SC/names.py" "$D/base" "$D/base/$REL" "$D/tree/$REL" | san
  echo; echo "# names.py on the tip's tree (${tip:0:8}; git archive)"
  python3 -I "$SC/names.py" "$W/tipexport" "$D/base/$REL" "$D/tree/$REL" | san; } > "$LG/names.log"
[ "$(grep -c "^NAMES: PASS" "$LG/names.log")" = 2 ]; echo "names: PASS on base and tip ${tip:0:8}"
bash "$SC/negctl.sh" "$S" "$D" "$OL" | san > "$LG/negative-controls.log"
[ "$(grep -c -- "— PASS" "$LG/negative-controls.log")" = 9 ]
! grep -q -- "— FAIL" "$LG/negative-controls.log"; echo "negative controls: 9 PASS"
bash "$SC/screens.sh" "$D" > /dev/null
{ echo "## Delta (screendelta.py, pairdiff.py, copied verbatim from <S>/tools; screen v3)"
  python3 -I "$SC/screendelta.py" "$LG/screen-before.txt" "$LG/screen-after.txt"
  python3 -I "$SC/pairdiff.py" "$LG/screen-after.txt" "$LG/screen-before.txt"; } > "$LG/screen-delta.log"
grep -q "new 0 (cross-file 0)" "$LG/screen-delta.log"; echo "screen v3: no new pair"; cat "$LG/screen-delta.log"
