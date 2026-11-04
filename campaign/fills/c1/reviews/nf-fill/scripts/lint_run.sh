#!/bin/bash
# Run copies of the repository's campaign_style_lint.py and style_lint.py from a lint root holding
# copies of the ClassNP subtree and facade of tree $1, with the owned file replaced by $2
# (optional).  usage: lint_run.sh <tree root> [<owned file copy>] > out
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/nf-fill
T=$1; O=$2; L=$R/scripts/lintroot
rm -rf "$L"; mkdir -p "$L/scripts" "$L/TCSlib/Complexity"
cp "$T/scripts/campaign_style_lint.py" "$T/scripts/style_lint.py" "$L/scripts/"
cp -R "$T/TCSlib/Complexity/ClassNP" "$L/TCSlib/Complexity/"
cp "$T/TCSlib/Complexity/ClassNP.lean" "$L/TCSlib/Complexity/"
[ -n "$O" ] && cp "$O" "$L/TCSlib/Complexity/ClassNP/NDNormalForm.lean"
echo "lint copies: $(shasum -a 256 "$L/scripts/campaign_style_lint.py" | cut -c1-16) $(shasum -a 256 "$L/scripts/style_lint.py" | cut -c1-16); tree $T; owned file $(shasum -a 256 "$L/TCSlib/Complexity/ClassNP/NDNormalForm.lean" | cut -c1-16)"
cd "$L" || exit 1
echo "## campaign_style_lint TCSlib/Complexity/ClassNP"; python3 -I "$L/scripts/campaign_style_lint.py" TCSlib/Complexity/ClassNP; echo "exit $?"
echo "## style_lint (policy linter) on the owned file"; python3 -I "$L/scripts/style_lint.py" TCSlib/Complexity/ClassNP/NDNormalForm.lean; echo "exit $?"
