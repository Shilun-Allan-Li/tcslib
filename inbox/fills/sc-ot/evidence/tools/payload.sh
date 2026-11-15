#!/usr/bin/env bash
# Refresh patches/ (format-patch series and COMMITS.tsv) and src/ of the delivery from the
# committed state of the proof branch.
set -e
D=/workspace/exchange/inbox/fills/sc-ot
B=107f1e8c218733eac12d6b9bee6fece441271317
cd /workspace/scot
rm -rf $D/patches $D/src
mkdir -p $D/patches $D/src
git format-patch -q $B..HEAD -o $D/patches
{ printf 'n\thash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsubject\n'
  i=0
  for h in $(git rev-list --reverse $B..HEAD); do
    i=$((i+1))
    git log -1 --format="$i%x09%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%s" $h
  done; } > $D/patches/COMMITS.tsv
for f in $(git diff --name-only --diff-filter=d $B..HEAD); do
  mkdir -p $D/src/$(dirname $f); git show HEAD:$f > $D/src/$f
done
ls $D/patches; (cd $D/src && find . -type f | sort)
