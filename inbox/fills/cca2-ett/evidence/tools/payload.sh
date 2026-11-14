#!/usr/bin/env bash
# Refresh patches/ and src/ of the delivery from the proof branch (committed state only).
set -e
D=/workspace/exchange/inbox/fills/cca2-ett
B=eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9
cd /workspace/ett
rm -rf $D/patches $D/src
mkdir -p $D/patches $D/src
git format-patch -q $B..HEAD -o $D/patches
for f in $(git diff --name-only --diff-filter=d $B..HEAD); do
  mkdir -p $D/src/$(dirname $f); git show HEAD:$f > $D/src/$f
done
ls $D/patches; (cd $D/src && find . -type f | sort)
