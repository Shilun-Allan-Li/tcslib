#!/usr/bin/env bash
# Landing rehearsal in the review's scratch clone (never the repository): git am -3 of the Lean patches,
# restricted to the owned file, onto the campaign tip; then the review's repairs on top.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/c1-core-cont2; X=$R/delivery/x/item1; F=TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean
cd $R/patchrepo || exit 1
git am --abort 2>/dev/null
git checkout -q --detach 97299639f3a7b4e51f4f94127647cbb915158393 || exit 1
P=(); for f in $X/patches/*.patch; do case "$f" in */0012-*|*/0018-*|*/0019-*) ;; *) P+=("$f");; esac; done
[ ${#P[@]} -eq 16 ] || { echo "expected 16 patches, got ${#P[@]}"; exit 1; }
echo "# landing rehearsal: git am -3 --include=$F of ${#P[@]} patches (0001-0011, 0013-0017) onto the tip 97299639"
git -c user.name=rev -c user.email=rev@local am -q -3 </dev/null --include=$F "${P[@]}" || { echo "AM FAILED"; exit 1; }
git log --reverse --format='%h %an <%ae> %aI | %s' 97299639..HEAD
echo "files touched since the tip: $(git diff --name-only 97299639 HEAD | tr '\n' ' ')"
echo "owned file blob after am: $(git rev-parse HEAD:$F) (delivered: 7d1657b3b8f97002722b2f01f8f54327309e2b10)"
cp $R/wt-repair/$F $F && echo "owned file blob with the review's repairs: $(git hash-object $F) (wt-repair: $(git -C $R/wt-repair hash-object $F))"
git checkout -q -- $F
