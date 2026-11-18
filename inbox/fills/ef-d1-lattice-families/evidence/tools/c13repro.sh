#!/usr/bin/env bash
# c13repro.sh <patchdir> <commits.tsv(no header)> <expected head>: in a scratch clone at the base,
# apply each patch with `git am` under the recorded committer data and compare hashes and src.
set -eu
P=$1; C=$2; HEAD=$3; W=/home/user/work/repro/wt
git -C /home/user/work/ef-d1 worktree add -q --detach $W 5ed465f62e4ae0f93ded1a1ba49e807591b589eb
cd $W
i=0
for p in $(ls $P/*.patch | sort); do i=$((i+1))
  line=$(sed -n "${i}p" $C)
  IFS=$'\t' read -r h an ae ad cn ce cd sig <<< "$line"
  GIT_COMMITTER_NAME="$cn" GIT_COMMITTER_EMAIL="$ce" GIT_COMMITTER_DATE="$cd" git -c commit.gpgsign=false am -q "$p"
  got=$(git rev-parse HEAD); echo "patch $i: recorded $h reproduced $got $([ $got = $h ] && echo MATCH || echo MISMATCH)"
done
[ "$(git rev-parse HEAD)" = "$HEAD" ] && echo "head reproduced: $HEAD" || echo "HEAD MISMATCH"
for f in TCSlib/Cryptography/LWE/Efficient.lean TCSlib/Cryptography/SIS/Efficient.lean TCSlib/Cryptography/SIS.lean; do
  cmp -s $f /home/user/work/repro/src/$f && echo "src equal: $f" || echo "SRC DIFFERS: $f"; done
