#!/usr/bin/env bash
# assemble.sh : rebuild patches/, src/, evidence/tools and SHA256SUMS of the adaptive-cpa payload
set -e
P=/home/user/acpa/payload; BASE=4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27
cd /home/user/fill
rm -rf $P/patches $P/src; mkdir -p $P/patches $P/src
git format-patch -q $BASE..fill/adaptive-cpa -o $P/patches
for f in $(git diff --name-only $BASE fill/adaptive-cpa); do mkdir -p $P/src/$(dirname $f); git show fill/adaptive-cpa:$f > $P/src/$f; done
mkdir -p $P/evidence/tools; cp /home/user/tools/* $P/evidence/tools/
cd $P && rm -f SHA256SUMS && find . -type f ! -name SHA256SUMS | sort | xargs sha256sum > SHA256SUMS
echo "payload files: $(wc -l < SHA256SUMS)"
