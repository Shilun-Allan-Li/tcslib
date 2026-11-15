#!/usr/bin/env bash
# Run the whole-file seals of the changed and new files, one Lean process at a time, skipping
# files already recorded in the jsonl.  Usage: seal_all.sh <tag> <jsonl> [--eval-open] [--coe-open]
set -u
tag="$1"; log="$2"; shift 2
FILES="TCSlib/Cryptography/Randomness/Learning.lean
TCSlib/Cryptography/Randomness/Learning/Sample.lean
TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean
TCSlib/Cryptography/Randomness/Learning/Law.lean
TCSlib/Cryptography/Randomness/Learning/Random.lean"
for f in $FILES; do
  [ -f "/workspace/learn/$f" ] || continue
  if [ -f "$log" ] && grep -q "\"file\": \"$f\"" "$log"; then continue; fi
  python3 -I /workspace/learn-tools/seal_run.py /workspace/learn "$tag" "$log" "$@" "$f"
done
echo SEAL-ALL-DONE
