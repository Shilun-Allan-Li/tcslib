#!/usr/bin/env bash
# Run the whole-file seals of the changed and new files, one Lean process at a time, skipping
# files already recorded in the jsonl.  Usage: seal_all.sh <tag> <jsonl> [--eval-open]
set -u
tag="$1"; log="$2"; shift 2
FILES="TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Handler.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean"
for f in $FILES; do
  [ -f "/workspace/ett/$f" ] || continue
  if [ -f "$log" ] && grep -q "\"file\": \"$f\"" "$log"; then continue; fi
  python3 /workspace/ett-tools/seal_run.py /workspace/ett "$tag" "$log" "$@" "$f"
done
echo SEAL-ALL-DONE
