#!/usr/bin/env bash
# Usage: deliver.sh "<commit message>"   (cleanup-part2 payload; exchange worktree only)
set -eu
MSG="$1"
F=/workspace/cp2/src
X=/workspace/tcslib
D=inbox/fills/cleanup-part2
ANC=1aa5506f58f77c215e56d24311ec33bd931cacf1
OWNED=/workspace/tcslib/outbox/fills/cleanup-part2/inputs/owned-files.txt
cd $X
if git status --porcelain | grep -v "^?? "; then echo "exchange tree/index not clean; inspect"; exit 1; fi
git checkout -q exchange/pass-shelat-ch5-8
for i in 0 1 2 3 4; do git pull -q --rebase origin exchange/pass-shelat-ch5-8 && break; sleep $((2**(i+1))); done
rm -rf $D/patches $D/src $D/evidence
mkdir -p $D/patches $D/src
while read -r p; do
  [ -z "$p" ] && continue
  mkdir -p "$D/src/$(dirname "$p")"
  git -C $F show "fill/cleanup-part2:$p" > "$D/src/$p"
done < $OWNED
git -C $F format-patch -q -o $X/$D/patches $ANC..fill/cleanup-part2 || true
mkdir -p $D/evidence
cp -r /workspace/cp2/evidence/. $D/evidence/
cp -r /workspace/cp2/tools $D/evidence/tools
# large census tables travel xz-compressed (exact bytes recoverable with `xz -d`)
find $D/evidence/census -name '*.tsv' -size +1M -exec xz -9 -T1 {} \;
find $D/evidence/logs -maxdepth 1 -name '*.json' -size +4M -exec xz -9 -T1 {} \;
cp /workspace/cp2/REPORT.md $D/REPORT.md
( cd $D && find . -type f ! -name PAYLOAD-SHA256SUMS -print0 | sort -z | xargs -0 sha256sum > /workspace/cp2/payload-sums.tmp && mv /workspace/cp2/payload-sums.tmp PAYLOAD-SHA256SUMS )
git add $D
if git status --porcelain | grep -v "^?? " | grep -v " $D/"; then echo "UNEXPECTED STAGED CHANGES OUTSIDE $D"; exit 1; fi
git commit -q -m "$MSG"
for i in 0 1 2 3 4; do
  if git push -q origin exchange/pass-shelat-ch5-8; then echo pushed; git rev-parse HEAD; exit 0; fi
  sleep $((2**(i+1))); git pull -q --rebase origin exchange/pass-shelat-ch5-8
done
echo "push failed"; exit 1
