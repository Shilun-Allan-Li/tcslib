#!/usr/bin/env bash
# Assemble the pk-cpa-cca1 payload under the exchange delivery path.
set -eu
F=/home/user/fill; D=/home/user/exch/inbox/fills/pk-cpa-cca1; BASE=8c3afbff69ad1273446750f47c05d424ab13ebe2
B=fill/pk-cpa-cca1; P=TCSlib/Cryptography/Encryption/PrivateKey
mkdir -p "$D"
rm -rf "$D/patches" "$D/src" "$D/evidence"
mkdir -p "$D/patches" "$D/src" "$D/evidence/tools"
git -C "$F" format-patch -q "$BASE..$B" -o "$D/patches"
for p in $(git -C "$F" diff --name-only "$BASE..$B"); do
  mkdir -p "$D/src/$(dirname "$p")"; git -C "$F" show "$B:$p" > "$D/src/$p"
done
cp -r "$F"/evidence/* "$D/evidence/"
cp /tmp/claude-0/pk/*.sh /tmp/claude-0/pk/*.py /tmp/claude-0/pk/tools/* "$D/evidence/tools/" 2>/dev/null || true
cp /tmp/claude-0/pk/REPORT.md "$D/REPORT.md"
cd "$D" && find . -type f ! -name PAYLOAD-SHA256SUMS | sort | xargs sha256sum > PAYLOAD-SHA256SUMS
echo "assembled: $(find "$D" -type f | wc -l) files"
