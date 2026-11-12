#!/usr/bin/env bash
# Refresh patches/ and src/ of the delivery from the proof branch (committed state only).
set -e
D=/workspace/exchange/inbox/fills/dl-consolidation
B=b96ab3ccc1915497ea3138df499eec00b6581db0
cd /workspace/dlc
rm -rf $D/patches $D/src
mkdir -p $D/patches $D/src
git format-patch -q $B..HEAD -o $D/patches
for f in $(git diff --name-only --diff-filter=d $B..HEAD); do
  mkdir -p $D/src/$(dirname $f); git show HEAD:$f > $D/src/$f
done
ls $D/patches; (cd $D/src && find . -type f | sort)
