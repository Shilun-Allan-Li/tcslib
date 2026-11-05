#!/usr/bin/env bash
# Gate 89 round 5's lint: campaign_style_lint over the five touched directories, and style_lint over
# the round-5 files, at a git-archive export of 711f5444 and at the head.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R5=$S/savgen/g89r5; WT=$S/wt-ls1; H=$(git -C $WT rev-parse HEAD); B=711f5444bf3412f7c9268c7bc96667fdd5af3149
DIRS=(SpaceComplexity Randomized TuringMachine ClassP ClassPSPACE)
LB=$R5/lint-base-tree; rm -rf "$LB"; mkdir -p "$LB"
git -C $WT archive $B "${DIRS[@]/#/TCSlib/Complexity/}" scripts/campaign_style_lint.py scripts/style_lint.py | tar -x -C "$LB"
mapfile_files=$(git -C $WT diff --name-only 227d92ee4a91fa86860d1d1ddf3a98130fa674b9 $H -- 'TCSlib/*.lean')
for side in base head; do
  R=$LB; C=$B; [ $side = head ] && { R=$WT; C=$H; }
  ( cd "$R" && echo "# commit $C"
    for d in "${DIRS[@]}"; do echo "## $d"; python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/$d 2>&1; echo "# exit $?"; done ) > $R5/lint/lint-$side.txt
  ( cd "$R" && for f in $mapfile_files; do echo "## $f"; python3 -I scripts/style_lint.py $f 2>&1 | grep -v '^$'; done ) > $R5/lint/style-$side.txt
done
