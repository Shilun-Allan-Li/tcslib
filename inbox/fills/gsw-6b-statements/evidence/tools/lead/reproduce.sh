#!/usr/bin/env bash
# reproduce.sh <payload-dir> <logfile> (gsw-6b-statements, new; check 13): in a scratch clone at the
# base, `git am` every patch of patches/o2 then patches/stmt with the committer name, email and date of
# its COMMITS.tsv row and signing off; compare each resulting hash with COMMITS.tsv, and src/, src-o2/
# with the files at the two reproduced heads, byte for byte.
set -u
D=$1; LOG=$2; B=3e51b5f28900db6190f1eb2e6d207d27ee15d541
S=$(mktemp -d /home/user/repro.XXXX); exec > >(tee $LOG) 2>&1
git clone -q --no-checkout /home/user/w6b $S/r && cd $S/r && git checkout -q --detach $B
fail=0
for s in o2 stmt; do
  i=0; tail -n +2 $D/patches/$s/COMMITS.tsv | while IFS=$'\t' read h an ae ad cn ce cd sg; do
    i=$((i+1)); p=$(ls $D/patches/$s/*.patch | sed -n ${i}p)
    GIT_COMMITTER_NAME="$cn" GIT_COMMITTER_EMAIL="$ce" GIT_COMMITTER_DATE="$cd" \
      git -c commit.gpgsign=false am -q "$p"
    got=$(git rev-parse HEAD); [ "$got" = "$h" ] && echo "OK $s $got" || { echo "MISMATCH $s expected $h got $got"; }
  done
  [ $s = o2 ] && O2H=$(git rev-parse HEAD) && { f=TCSlib/Cryptography/LWE/BitEncoding.lean; cmp -s $f $D/src-o2/$f && echo "src-o2 OK $f" || echo "src-o2 DIFF $f"; }
done
for f in $(cd $D/src && find . -type f | sed 's|^\./||'); do cmp -s $f $D/src/$f && echo "src OK $f" || echo "src DIFF $f"; done
echo "reproduced heads: o2 $O2H stmt $(git rev-parse HEAD)"
rm -rf $S
