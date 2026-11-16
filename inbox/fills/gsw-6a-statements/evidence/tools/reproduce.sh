#!/usr/bin/env bash
# reproduce.sh <scratch-dir> <base-repo> <base> <patchdir> [<patchdir2>...]: apply each patch series
# with `git am`, setting the committer name, email and date from its COMMITS.tsv, and compare every
# resulting hash with the recorded one.
set -e
S=$1; REPO=$2; BASE=$3; shift 3
rm -rf $S; git clone -q --no-checkout $REPO $S; cd $S; git checkout -q --detach $BASE
for P in "$@"; do
  i=0
  tail -n +2 $P/COMMITS.tsv | while IFS=$'\t' read h an ae ad cn ce cd sig; do
    i=$((i+1)); f=$(ls $P/*.patch | sed -n "${i}p")
    GIT_COMMITTER_NAME="$cn" GIT_COMMITTER_EMAIL="$ce" GIT_COMMITTER_DATE="$cd" git -c commit.gpgsign=false am -q --keep-cr "$f"
    got=$(git rev-parse HEAD); [ "$got" = "$h" ] && echo "OK $h $(basename $f)" || { echo "MISMATCH want $h got $got $(basename $f)"; exit 1; }
  done
done
