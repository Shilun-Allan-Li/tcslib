#!/usr/bin/env bash
# run_frozen.sh <head-file> <outdir> [<repo>]
#
# Runs the adapted frozen-header check frozen_check_bb1m.py and its controls
# frozen_controls_bb1m.py (fill bb1-machine) on <head-file> (a BonehBoyenMachine.lean) against the
# #331 base 9e7a9648 (read with `git -C <repo> show`; <repo> defaults to /home/user/fill/tcslib).
# Writes <outdir>/base-9e7a9648.lean, <outdir>/head.sha256, <outdir>/frozen-check.out,
# <outdir>/frozen-controls.out and the mutated heads under <outdir>/controls/. Exit status 0 iff
# the check PASSes and the controls give ALL_CONTROLS_OK True. Runs no Lean.
# The expected Oracles bullet/import live in frozen_check_bb1m.py (ORACLES_BULLET, ORACLES_IMPORT,
# ORACLES_AFTER_IMPORT); or set BULLET_FILE=<path> to pass --bullet-file <path> to every check run.
#
# written by tools-agent (sub-agent), fill bb1-machine
set -u
head=$1
out=$2
repo=${3:-/home/user/fill/tcslib}
here=$(cd "$(dirname "$0")" && pwd)
p=TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean
mkdir -p "$out"
git -C "$repo" show "9e7a96481785d6cac4dea3b2e990c49ac278b060:$p" > "$out/base-9e7a9648.lean"
sha256sum "$head" > "$out/head.sha256"
extra=()
if [ -n "${BULLET_FILE:-}" ]; then extra=(--bullet-file "$BULLET_FILE"); fi
python3 -I "$here/frozen_check_bb1m.py" "$out/base-9e7a9648.lean" "$head" "${extra[@]}" \
  > "$out/frozen-check.out" 2>&1
rc1=$?
python3 -I "$here/frozen_controls_bb1m.py" "$out/base-9e7a9648.lean" "$head" \
  "$here/frozen_check_bb1m.py" "$out/controls" "${extra[@]}" > "$out/frozen-controls.out" 2>&1
rc2=$?
cat "$out/frozen-check.out"
tail -n 1 "$out/frozen-controls.out"
[ $rc1 -eq 0 ] && [ $rc2 -eq 0 ]
