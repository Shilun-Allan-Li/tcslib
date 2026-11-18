#!/usr/bin/env bash
# Refresh patches/ (format-patch series and COMMITS.tsv) and src/ of the delivery from the
# committed state of the proof branch.
set -e
D=/workspace/exchange/inbox/fills/gsw-6b-u13
B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d
cd /workspace/u13
rm -rf $D/patches $D/src
mkdir -p $D/patches $D/src
git format-patch -q $B..fill/gsw-6b-u13 -o $D/patches
{ printf 'n\thash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\tsubject\n'
  i=0
  for h in $(git rev-list --reverse $B..HEAD); do
    i=$((i+1))
    sig=$(git cat-file -p $h | grep -c gpgsig || true); [ "$sig" = 0 ] && sig=unsigned || sig=SIGNED
    git log -1 --format="$i%x09%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09$sig%x09%s" $h
  done; } > $D/patches/COMMITS.tsv
for f in $(git diff --name-only --diff-filter=d $B..HEAD); do
  mkdir -p $D/src/$(dirname $f); git show HEAD:$f > $D/src/$f
done
ls $D/patches; (cd $D/src && find . -type f | sort)
