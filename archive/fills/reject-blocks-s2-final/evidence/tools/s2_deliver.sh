#!/usr/bin/env bash
# Usage: s2_deliver.sh "<commit message>"
set -eu
MSG="$1"
F=/workspace/tcslib-fill
X=/workspace/tcslib
D=inbox/fills/reject-blocks-s2
ANC=31348fcf7dee32f84db1fc8f929d80653137995e
cd $X
git status --porcelain | grep -v "^?? " && { echo "exchange tree/index not clean; inspect"; exit 1; } || true
git checkout -q exchange/pass-shelat-ch5-8
for i in 0 1 2 3 4; do git pull -q --rebase origin exchange/pass-shelat-ch5-8 && break; sleep $((2**(i+1))); done
rm -rf $D/patches $D/src $D/evidence
mkdir -p $D/patches $D/src/TCSlib/Cryptography/Candidates
for f in Concrete DiscreteLog ElGamal RSA Rabin; do
  git -C $F show fill/reject-blocks-s2:TCSlib/Cryptography/Candidates/$f.lean > $D/src/TCSlib/Cryptography/Candidates/$f.lean
done
git -C $F format-patch -q -o $X/$D/patches $ANC..fill/reject-blocks-s2
cp -r /workspace/s2-evidence $D/evidence
rm -f $D/evidence/logs/*.pid
cp /workspace/s2-REPORT.md $D/REPORT.md
git add $D
if git status --porcelain | grep -v "^?? " | grep -v " $D/"; then echo "UNEXPECTED STAGED CHANGES OUTSIDE $D"; exit 1; fi
git commit -q -m "$MSG"
for i in 0 1 2 3 4; do
  if git push -q origin exchange/pass-shelat-ch5-8; then echo pushed; git rev-parse HEAD; exit 0; fi
  sleep $((2**(i+1))); git pull -q --rebase origin exchange/pass-shelat-ch5-8
done
echo "push failed"; exit 1
