#!/bin/bash
# Run a copy of the repository's campaign_style_lint.py from this review's scripts/ dir, over a
# lint root holding copies of the Diagonalization subtree and facade from tree $1, with the owned
# file replaced by $2 (optional).  usage: lint_run.sh <tree root> [<owned file copy>] > out
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/eq-cont1-fill
T=$1; O=$2; L=$R/scripts/lintroot
rm -rf "$L"; mkdir -p "$L/scripts" "$L/TCSlib/Complexity"
cp "$T/scripts/campaign_style_lint.py" "$L/scripts/"
cp -R "$T/TCSlib/Complexity/Diagonalization" "$L/TCSlib/Complexity/"
cp "$T/TCSlib/Complexity/Diagonalization.lean" "$L/TCSlib/Complexity/"
[ -n "$O" ] && cp "$O" "$L/TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean"
echo "lint copy: $(shasum -a 256 "$L/scripts/campaign_style_lint.py" | cut -c1-16); tree $T; owned file $(shasum -a 256 "$L/TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean" | cut -c1-16)"
cd "$L" && python3 -I "$L/scripts/campaign_style_lint.py" TCSlib/Complexity/Diagonalization
