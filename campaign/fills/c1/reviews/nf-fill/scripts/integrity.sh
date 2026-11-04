#!/bin/bash
# Integrity checks for the NF partial delivery (reads data only; git and python3 -I from scripts/).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/nf-fill; G=/Users/seyoonr/phd_experiments/tcslib
B=951251f641f9e2436429c282e4e199a9c9b79420; H=4af97d4679f8024ea5bcbf11c04d1e4e5e0373cb
F=TCSlib/Complexity/ClassNP/NDNormalForm.lean
X=$S/intake/c1-nf/x; Z=$G/exchange/inbox/fill-c1-nf.zip
echo "## zip"; shasum -a 256 $Z
python3 -I $R/scripts/ziplist.py $Z | tail -1
echo "## sums"; python3 -I $R/scripts/sumscheck.py $X
echo "## symlinks in extraction: $(find $X -type l | wc -l)"
echo "## bundle"; git -C $G bundle verify $X/fill-c1-nf.bundle 2>&1; git -C $G bundle list-heads $X/fill-c1-nf.bundle
echo "refs/deliv/c1-nf = $(git -C $G rev-parse refs/deliv/c1-nf)"
echo "## commits base..head (parents)"; git -C $G rev-list --parents $B..$H
git -C $G log --format='%H %an <%ae> author %aI committer %cI | %s' $B..$H
echo "## files touched base..head"; git -C $G diff --stat $B $H | tail -1; git -C $G diff --name-only $B $H
echo "## per commit"; for c in $(git -C $G rev-list --reverse $B..$H); do echo "$c: $(git -C $G diff-tree --no-commit-id --numstat -r $c | tr '\n' ' ')"; done
echo "## blobs"; echo "base blob $(git -C $G rev-parse $B:$F) (brief: 5150734a89b935396dee9516911030497f2034d1)"; echo "head blob $(git -C $G rev-parse $H:$F)"
echo "zip source blob $(git -C $G hash-object $X/$F); zip source sha256 $(shasum -a 256 $X/$F | cut -c1-64)"
echo "## patches vs commits (patch-id --stable)"; for p in $X/patches/*.patch; do echo "$(basename $p): $(git -C $G patch-id --stable < $p | cut -c1-40)"; done
for c in $(git -C $G rev-list --reverse $B..$H); do echo "commit $c: $(git -C $G show $c | git -C $G patch-id --stable | cut -c1-40)"; done
echo "## patches vs git format-patch of the range (diff ignoring the version trailer)"; T=$R/out/aux-fp; rm -rf $T; mkdir -p $T; git -C $G format-patch -q -o $T $B..$H
for p in $X/patches/*.patch; do q=$T/$(basename $p); if cmp -s $p $q; then echo "byte-equal $(basename $p)"; else echo "differs $(basename $p):"; diff $p $q | head -8; fi; done
echo "## cp1 commit's file vs the overlay + cp1 additions: overlay is the first edit?"
OV=$S/wt-hk/campaign/fills/c1/inputs/c1-fill-nf/NDNormalFormOverlay.lean.txt
echo "overlay vs base: $(diff <(git -C $G show $B:$F) $OV | head -5 | tr '\n' ' ')"
echo "## brief copies"; shasum -a 256 $G/exchange/archive/fills/c1-fill-nf.md $X/inputs/c1-fill-nf.md $X/inputs/fill-environment-addendum.md $S/wt-hk/campaign/standards/fill-environment-addendum.md
echo "## base ancestor of head / of the tip"; git -C $G merge-base --is-ancestor $B $H && echo "base ancestor of head"
T2=$(git -C $S/wt-hk rev-parse HEAD); echo "records tip $T2"; git -C $G merge-base --is-ancestor $B $T2 && echo "base ancestor of the tip"
echo "owned file at tip: $(git -C $G rev-parse $T2:$F)"
echo "lean files changed base..tip:"; git -C $G diff --name-only $B $T2 -- '*.lean'
