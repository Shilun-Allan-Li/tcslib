#!/usr/bin/env bash
# Run the whole-file seals of the changed and new files, one Lean process at a time, skipping
# files already recorded in the jsonl.  Usage: seal_all.sh <tag> <jsonl> [--eval-open] [--coe-open]
set -u
tag="$1"; log="$2"; shift 2
FILES="TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean
TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean
TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Efficiency.lean
TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Simulators.lean
TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewA.lean
TCSlib/Cryptography/SecureComputation/ObliviousTransfer/ViewB.lean
TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Predictor.lean"
for f in $FILES; do
  [ -f "/workspace/scot/$f" ] || continue
  if [ -f "$log" ] && grep -q "\"file\": \"$f\"" "$log"; then continue; fi
  python3 -I /workspace/scot-tools/seal_run.py /workspace/scot "$tag" "$log" "$@" "$f"
done
echo SEAL-ALL-DONE
