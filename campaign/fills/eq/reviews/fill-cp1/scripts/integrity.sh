#!/bin/bash
# Integrity checks for the E-Q delivery (reads data only; runs git and python3 -I from scripts/).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/eq-fill; G=/Users/seyoonr/phd_experiments/tcslib
B=ab09aa4124da9ffce36e939f652dc4bc30e6f3c5; H=9d93626dadf1561c757494cfff992d1951a458e2; C1=fabce3bb1008815d8f592da0c628e40c1355015d
F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
X=$R/delivery/main/x; Y=$R/delivery/cp1/x
echo "## zips"; shasum -a 256 $R/delivery/main/fill-eq-query.zip $R/delivery/cp1/fill-eq-query-cp1.zip
echo "## sums"; cat $R/out/sums-main.txt $R/out/sums-cp1.txt
echo "## bundle"; cat $R/out/bundle-verify.txt; echo "deliver/fill-eq-query-in = $(git -C $G rev-parse deliver/fill-eq-query-in)"
cmp $X/fill-eq-query.bundle $Y/fill-eq-query.bundle && echo "cp1 bundle == final bundle (byte-equal)"
echo "## commits base..head"; git -C $G rev-list --parents $B..$H; git -C $G log --format='%H %an <%ae> %aI | %cI | %s' $B..$H
echo "## files touched per commit"; for c in $C1 $H; do echo "$c: $(git -C $G diff-tree --no-commit-id --name-only -r $c | tr '\n' ' ')"; git -C $G diff-tree --numstat -r $c | tail -n +1; done
echo "## blobs"; echo "base blob $(git -C $G rev-parse $B:$F) (brief: 3cdc4f33a1650df104c752f2783bf5dc734be3b3)"; echo "overlay-commit blob $(git -C $G rev-parse $C1:$F)"; echo "head blob $(git -C $G rev-parse $H:$F)"
echo "zip source blob (main) $(git -C $G hash-object $X/$F); (cp1) $(git -C $G hash-object $Y/$F)"
echo "## first commit == overlay input"; git -C $G show $B:campaign/fills/eq/inputs/eq-fill-query/NTimeDiagonalizerOverlay.lean.txt > $R/out/aux-overlay.txt; git -C $G show $C1:$F > $R/out/aux-c1.lean; cmp $R/out/aux-overlay.txt $R/out/aux-c1.lean && echo "fabce3bb file == base's NTimeDiagonalizerOverlay.lean.txt (byte-equal)"
echo "## overlay vs base diff"; git -C $G diff $B $C1 -- $F | grep '^[+-]' | grep -v '^+++\|^---'
echo "## patches"; for p in $X/patches/*.patch; do echo "$(basename $p): patch-id $(git -C $G patch-id --stable < $p)"; done
for c in $C1 $H; do echo "commit $c: patch-id $(git -C $G show $c | git -C $G patch-id --stable)"; done
cmp -s $X/patches/0001-E-Q-apply-authorized-eight-import-overlay.patch $Y/patches/0001-E-Q-apply-authorized-eight-import-overlay.patch && cmp -s $X/patches/0002-E-Q-checkpoint-1-linear-guard-and-reduction-to-the-m.patch $Y/patches/0002-E-Q-checkpoint-1-linear-guard-and-reduction-to-the-m.patch && echo "cp1 patches == final patches"
cmp -s $X/$F $Y/$F && echo "cp1 source == final source"
echo "## base Lean content vs #168 merge 13120e00"; M=13120e0067ce19ee9c09809ef6578f2b38139cf6; git -C $G cat-file -t $M; echo "lean files differing: $(git -C $G diff --name-only $M $B -- '*.lean' | wc -l)"; echo "all files differing:"; git -C $G diff --stat $M $B | tail -3
echo "## base is ancestor of the campaign tip (records worktree)"; T=$(git -C $S/wt-hk rev-parse HEAD); echo "tip $T"; git -C $G merge-base --is-ancestor $B $T && echo "base is an ancestor of the tip"
echo "owned file at tip: $(git -C $G rev-parse $T:$F) (base $(git -C $G rev-parse $B:$F))"
echo "lean files changed base..tip:"; git -C $G diff --name-only $B $T -- '*.lean'
