#!/usr/bin/env bash
# series_fill.sh <repo> <base> <branch> <outdir> (gsw-6a-fills, new): patches (git format-patch <base>..<branch>),
# COMMITS.tsv (hash, author name/email/date, committer name/email/date, signing: `none` or the signature format),
# and check 12: `git am` of the patches in a scratch clone at <base> (a shared clone, sparse like the work clone:
# without briefs/ and dataset/, whose blobs the blobless work clone does not hold), with each commit's committer identity and date,
# must reproduce every hash. Writes <outdir>/patches/, <outdir>/reproduce.log.
set -eu
R=$1; B=$2; BR=$3; O=$4
rm -rf $O/patches; mkdir -p $O/patches
git -C $R format-patch -q --no-signature -o $O/patches $B..$BR
printf 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\tsubject\n' > $O/patches/COMMITS.tsv
for c in $(git -C $R rev-list --reverse $B..$BR); do
  sig=$(git -C $R cat-file -p $c | grep -q '^gpgsig' && echo gpg || echo none)
  git -C $R log -1 --format="%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09$sig%x09%s" $c >> $O/patches/COMMITS.tsv
done
S=$(mktemp -d /home/user/w6/scratch-am.XXXX)
{
  echo "# git am reproduction at $(date -u +%FT%TZ): scratch clone of $R at $B"
  git clone -q --no-checkout --shared $R $S/r && cd $S/r
  # the work clone is blobless (a partial clone of GitHub): make the scratch clone a partial clone of the same
  # remote, so that git treats the blobs it does not hold (briefs/, dataset/) as promisor objects
  git config core.repositoryformatversion 1 && git config extensions.partialClone origin
  git config remote.origin.url https://github.com/Shilun-Allan-Li/tcslib
  git config remote.origin.promisor true && git config remote.origin.partialclonefilter blob:none
  git sparse-checkout set --no-cone '/*' '!/briefs/' '!/dataset/' && git checkout -q --detach $B
  for p in $O/patches/0*.patch; do
    n=$(basename $p | cut -d- -f1); n=$((10#$n + 1))
    row=$(sed -n "$((n))p" $O/patches/COMMITS.tsv)
    want=$(echo "$row" | cut -f1)
    GIT_COMMITTER_NAME="$(echo "$row" | cut -f5)" GIT_COMMITTER_EMAIL="$(echo "$row" | cut -f6)" \
    GIT_COMMITTER_DATE="$(echo "$row" | cut -f7)" git -c commit.gpgsign=false am -q $p
    got=$(git rev-parse HEAD)
    echo "$(basename $p)	want=$want	got=$got	$([ $want = $got ] && echo REPRODUCED || echo DIFFERENT)"
  done
  echo "RESULT head=$(git rev-parse HEAD) branch_head=$(git -C $R rev-parse $BR)"
} > $O/reproduce.log 2>&1
rm -rf $S
cat $O/reproduce.log
