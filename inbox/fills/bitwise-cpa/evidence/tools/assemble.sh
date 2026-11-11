#!/usr/bin/env bash
# Assemble the bitwise-cpa payload under the exchange delivery path.
set -eu
F=/home/user/fill; D=/home/user/exch/inbox/fills/bitwise-cpa; BASE=4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27
B=fill/bitwise-cpa; P=TCSlib/Cryptography/Encryption/PublicKey
mkdir -p "$D"
rm -rf "$D/patches" "$D/src" "$D/evidence"
mkdir -p "$D/patches" "$D/src" "$D/evidence/tools"
git -C "$F" format-patch -q "$BASE..$B" -o "$D/patches"
for p in $P/BitwiseCPA.lean $P/BitwiseCPA/QueryHandler.lean $P/BitwiseCPA/Planted.lean \
         $P/BitwiseCPA/Eager.lean; do
  mkdir -p "$D/src/$(dirname "$p")"; git -C "$F" show "$B:$p" > "$D/src/$p"
done
cp -r "$F"/evidence/* "$D/evidence/"
cp /tmp/claude-0/bw/*.sh /tmp/claude-0/bw/*.py /tmp/claude-0/bw/tools/* "$D/evidence/tools/" 2>/dev/null || true
cp /tmp/claude-0/bw/REPORT.md "$D/REPORT.md"
cd "$D" && find . -type f ! -name PAYLOAD-SHA256SUMS | sort | xargs sha256sum > PAYLOAD-SHA256SUMS
echo "assembled: $(find "$D" -type f | wc -l) files"
