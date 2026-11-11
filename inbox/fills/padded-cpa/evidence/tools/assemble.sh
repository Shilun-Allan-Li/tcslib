#!/usr/bin/env bash
# Assemble the padded-cpa payload under the exchange delivery path.
set -eu
F=/home/user/fill; D=/home/user/exch/inbox/fills/padded-cpa; BASE=4a09f3993eb9344fc5714610e41ab141a0144db8
mkdir -p "$D"
rm -rf "$D/patches" "$D/src" "$D/evidence"
mkdir -p "$D/patches" "$D/src" "$D/evidence/logs" "$D/evidence/seal" "$D/evidence/tools"
git -C "$F" format-patch -q "$BASE..fill/padded-cpa" -o "$D/patches"
for p in TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean \
         TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean \
         TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/RecordHandler.lean; do
  mkdir -p "$D/src/$(dirname "$p")"; git -C "$F" show "fill/padded-cpa:$p" > "$D/src/$p"
done
cp "$F"/evidence/logs/* "$D/evidence/logs/"
cp "$F"/evidence/probe/*.lean "$D/evidence/seal/" 2>/dev/null || true
[ -d "$F/evidence/seal" ] && cp "$F"/evidence/seal/*.lean "$D/evidence/seal/" 2>/dev/null || true
cp /tmp/claude-0/chk.sh /tmp/claude-0/pkgcheck.py /tmp/claude-0/closure.py /tmp/claude-0/fullclosure.py \
   /tmp/claude-0/topo.py /tmp/claude-0/tools/* "$D/evidence/tools/" 2>/dev/null || true
cd "$D" && find . -type f ! -name PAYLOAD-SHA256SUMS | sort | xargs sha256sum > PAYLOAD-SHA256SUMS
echo "assembled: $(find "$D" -type f | wc -l) files"
