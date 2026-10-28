#!/bin/bash
# Integrity checks for the E-Q cont1 delivery (reads data only; git and python3 -I from scripts/).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/eq-cont1-fill; G=/Users/seyoonr/phd_experiments/tcslib
B=43fe918f2b7612b46d6b1bd6d4201651f7243430; H=e952bc50924ae7cea3364298087148fe1540a534
F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
X=$R/delivery/fill-eq-query-cont1
echo "## zip"; shasum -a 256 /Users/seyoonr/phd_experiments/tcslib/exchange/inbox/fill-eq-query-cont1.zip
echo "## sums"; cat $R/out/01a-sums.txt
echo "## bundle"; git -C $G bundle verify $X/fill-eq-query-cont1.bundle 2>&1; git -C $G bundle list-heads $X/fill-eq-query-cont1.bundle
echo "refs/deliv/eq-query-cont1 = $(git -C $G rev-parse refs/deliv/eq-query-cont1)"
echo "## worker's bundle-verify.txt"; cat $X/checks/bundle-verify.txt
echo "## commits base..head (parents)"; git -C $G rev-list --parents $B..$H
git -C $G log --format='%H %an <%ae> author %aI committer %cI | %s' $B..$H
echo "## files touched base..head"; git -C $G diff --stat $B $H | tail -3; git -C $G diff --name-only $B $H
echo "## per commit"; for c in $(git -C $G rev-list --reverse $B..$H); do echo "$c: $(git -C $G diff-tree --no-commit-id --numstat -r $c | tr '\n' ' ')"; done
echo "## blobs"; echo "base blob $(git -C $G rev-parse $B:$F) (brief: f965eac02e06549e8239c7476b31c0ced4f3d11b)"; echo "head blob $(git -C $G rev-parse $H:$F)"
echo "zip source blob $(git -C $G hash-object $X/source/$F)"
echo "## patches vs commits (patch-id --stable)"; for p in $X/patches/*.patch; do echo "$(basename $p): $(git -C $G patch-id --stable < $p | cut -c1-40)"; done
for c in $(git -C $G rev-list --reverse $B..$H); do echo "commit $c: $(git -C $G show $c | git -C $G patch-id --stable | cut -c1-40)"; done
echo "## patches byte-equal to git format-patch of the range"; T=$R/out/aux-fp; rm -rf $T; mkdir -p $T; git -C $G format-patch -q -o $T $B..$H; for p in $X/patches/*.patch; do cmp -s $p $T/$(basename $p) && echo "equal $(basename $p)" || echo "DIFFER $(basename $p)"; done; ls $T | wc -l
echo "## base is ancestor of head; base vs tip"; git -C $G merge-base --is-ancestor $B $H && echo "base ancestor of head"
T2=$(git -C $S/wt-hk rev-parse HEAD); echo "records tip $T2"; git -C $G merge-base --is-ancestor $B $T2 && echo "base ancestor of the tip"
echo "owned file at tip: $(git -C $G rev-parse $T2:$F)"
echo "lean files changed base..tip:"; git -C $G diff --name-only $B $T2 -- '*.lean'
echo "## base Lean vs 940671e0 (oleans-lhh's tree)"; P=$(git -C $G rev-parse 940671e0); echo "940671e0 = $P"; echo "lean files differing 940671e0..base: $(git -C $G diff --name-only $P $B -- '*.lean' | wc -l)"
