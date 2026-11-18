#!/usr/bin/env bash
# c13.sh <source-repo> <base> <payload-dir> : git am the patches at base in a scratch clone with the committer data of
# COMMITS.tsv, compare every hash, and compare src/ with the final tree byte for byte.
SRC=$1; BASE=$2; P=$3; W=$(mktemp -d /home/user/c13.XXXX)
git clone -q --no-checkout "$SRC" $W/r && cd $W/r && git checkout -q --detach $BASE || exit 2
i=0; ok=0; n=0
for p in $(ls $P/patches/*.patch | sort); do
  i=$((i+1)); line=$(sed -n "$((i+1))p" $P/COMMITS.tsv)
  IFS=$'\t' read -r h an ae ad cn ce cd sg <<< "$line"
  GIT_COMMITTER_NAME="$cn" GIT_COMMITTER_EMAIL="$ce" GIT_COMMITTER_DATE="$cd" git -c commit.gpgsign=false am -q --committer-date-is-author-date "$p" 2>&1 | tail -2
  GIT_COMMITTER_NAME="$cn" GIT_COMMITTER_EMAIL="$ce" GIT_COMMITTER_DATE="$cd" git -c commit.gpgsign=false commit -q --amend --no-edit --no-verify >/dev/null 2>&1 || true
  got=$(git rev-parse HEAD); n=$((n+1)); [ "$got" = "$h" ] && ok=$((ok+1)); echo "patch $i: expected $h got $got $([ "$got" = "$h" ] && echo OK || echo MISMATCH)"
done
echo "hashes reproduced: $ok/$n"
d=0; for f in $(cd $P/src && find . -type f | sed 's|^\./||'); do cmp -s $P/src/$f $f || { echo "src DIFF $f"; d=$((d+1)); }; done
echo "src/ files: $(cd $P/src && find . -type f | wc -l), differences: $d"
cd /; rm -rf "${W:?}"
