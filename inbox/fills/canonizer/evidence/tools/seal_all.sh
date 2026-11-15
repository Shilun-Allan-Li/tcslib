#!/usr/bin/env bash
# Run the whole-file seals of the changed and new files, one Lean process at a time, skipping
# files already recorded in the jsonl.  Usage: seal_all.sh <tag> <jsonl> [--eval-open] [--coe-open]
set -u
tag="$1"; log="$2"; shift 2
FILES="TCSlib/Cryptography/Asymptotic/Universal.lean
TCSlib/Cryptography/Asymptotic/Universal/Canonizer.lean
TCSlib/Complexity/TuringMachine/CodeFormat.lean
TCSlib/Complexity/TuringMachine/CodeSimulator.lean"
for f in $FILES; do
  [ -f "/workspace/canon/$f" ] || continue
  if [ -f "$log" ] && grep -q "\"file\": \"$f\"" "$log"; then continue; fi
  python3 -I /workspace/canon-tools/seal_run.py /workspace/canon "$tag" "$log" "$@" "$f"
done
echo SEAL-ALL-DONE
