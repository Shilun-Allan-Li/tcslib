#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill; G=/Users/seyoonr/phd_experiments/tcslib
X=$S/intake/eq-diagonalizer/x/fill-eq-diagonalizer
Z=$G/exchange/archive/deliveries/fill-eq-diagonalizer.zip
H=$(git -C $G rev-parse refs/deliv/eq-diagonalizer); B=$(git -C $G rev-parse refs/deliv/eq-diagonalizer~11)
F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
echo "== zip sha"; shasum -a 256 $Z
echo "== zip members"; python3 -I -c "
import zipfile,sys,stat
z=zipfile.ZipFile(sys.argv[1]); n=0; bad=0; links=0
for i in z.infolist():
    n+=1
    if i.filename.startswith('/') or '..' in i.filename.split('/'): bad+=1
    if stat.S_ISLNK(i.external_attr>>16): links+=1
print('members',n,'unsafe',bad,'links',links)" $Z
echo "== SHA256SUMS"; (cd $X && shasum -a 256 -c SHA256SUMS 2>&1 | grep -vc ': OK$' ; shasum -a 256 -c SHA256SUMS 2>&1 | grep -c ': OK$')
echo "== unlisted files"; (cd $X && find . -type f ! -name SHA256SUMS | sed 's|^\./||' | sort > /tmp/.x1.$$; sed -E 's/^[0-9a-f]+ +\*?//; s|^\./||' SHA256SUMS | sort > /tmp/.x2.$$; comm -23 /tmp/.x1.$$ /tmp/.x2.$$; rm -f /tmp/.x1.$$ /tmp/.x2.$$)
echo "== bundle verify"; git -C $G bundle verify $X/fill-eq-diagonalizer.bundle 2>&1
echo "== bundle heads"; git -C $G bundle list-heads $X/fill-eq-diagonalizer.bundle
echo "== head/base"; echo "head $H"; echo "base $B"
echo "== commits"; git -C $G log --format='%H %an <%ae> %ad %s' --date=iso-strict $B..$H
echo "== linear?"; git -C $G rev-list --merges $B..$H | wc -l
echo "== files changed"; git -C $G diff --stat $B $H
echo "== numstat"; git -C $G diff --numstat $B $H
echo "== blobs"; git -C $G rev-parse $B:$F $H:$F
echo "== source = head blob"; git -C $G hash-object $X/source/$F
echo "== patch-ids (commits)"; for c in $(git -C $G rev-list --reverse $B..$H); do git -C $G show $c | git -C $G patch-id --stable; done
echo "== patch-ids (patches)"; for p in $X/patches/*.patch; do git -C $G patch-id --stable < $p; done
echo "== hunks"; git -C $G diff -U0 $B $H -- $F | grep '^@@'
