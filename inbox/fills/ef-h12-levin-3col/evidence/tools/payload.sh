#!/usr/bin/env bash
# Build the EF-H12 delivery payload under the exchange path. Usage: payload.sh <REPORT.md source>
set -eu
BASE=cf6a2266e9556ca8ad61e56f7232266ccc6d4e62
F=/home/user/work/fill; P=/home/user/work/exch/inbox/fills/ef-h12-levin-3col; EV=/home/user/work/ev/evidence
H=$(git -C $F rev-parse HEAD)
rm -rf "${P:?}"; mkdir -p $P/patches $P/src $P/evidence
git -C $F format-patch -q $BASE..HEAD -o $P/patches
{ printf 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tgpgsig\tsubject\n'
  for c in $(git -C $F rev-list --reverse $BASE..HEAD); do
    printf '%s\t%s\t%s\n' "$(git -C $F log -1 --format='%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI' $c)" \
      "$(git -C $F cat-file -p $c | grep -c '^gpgsig' || true)" "$(git -C $F log -1 --format=%s $c)"; done; } > $P/COMMITS.tsv
for f in $(git -C $F diff --name-only $BASE HEAD); do mkdir -p $P/src/$(dirname $f); git -C $F show HEAD:$f > $P/src/$f; done
# C13: replay the patches at the base with the recorded committer data
R=/home/user/work/replay; rm -rf "${R:?}"; git clone -q --no-checkout $F $R; git -C $R checkout -q --detach $BASE
git -C $R sparse-checkout set --cone TCSlib scripts >/dev/null 2>&1 || true
ok=yes; i=0
for c in $(git -C $F rev-list --reverse $BASE..HEAD); do i=$((i+1)); pf=$(ls $P/patches | sed -n "${i}p")
  GIT_COMMITTER_NAME="$(git -C $F log -1 --format=%cn $c)" GIT_COMMITTER_EMAIL="$(git -C $F log -1 --format=%ce $c)" \
  GIT_COMMITTER_DATE="$(git -C $F log -1 --format=%cI $c)" git -C $R -c commit.gpgsign=false am -q --keep-cr $P/patches/$pf
  [ "$(git -C $R rev-parse HEAD)" = "$c" ] || ok=no; done
srcok=yes; for f in $(git -C $F diff --name-only $BASE HEAD); do cmp -s $P/src/$f <(git -C $R show HEAD:$f) || srcok=no; done
echo "C13 replay at $BASE: hashes_reproduced=$ok final=$(git -C $R rev-parse HEAD) head=$H src_equal=$srcok" | tee $EV/logs/c13-replay.txt
rm -rf "${R:?}"
cp -r $EV/. $P/evidence/
( cd $P/evidence && find . -type f ! -name SHA256SUMS | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS )
cp "$1" $P/REPORT.md
( cd $P && find . -type f ! -name SHA256SUMS | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS )
echo "payload at $P for head $H: $(find $P -type f | wc -l) files, $(du -sh $P | cut -f1)"
