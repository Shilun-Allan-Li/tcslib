#!/usr/bin/env bash
# run_insertion.sh <repo-or-worktree> <outdir> [<readers.txt>]
#
# Runs insertion_check.py and insertion_controls.py (fill bb1-machine) on the head files
# <repo>/TCSlib/Cryptography/AdvancedEncryption/IdentityBased/{Defs,BonehBoyen}.lean (working
# tree) against the issue base 7c0a55e0 (read with `git -C <repo> show`). Writes
# <outdir>/base/{Defs,BonehBoyen}.lean, <outdir>/insertion-check.out,
# <outdir>/insertion-controls.out and <outdir>/controls/<control>/. Exit status 0 iff the check
# gives RESULT PASS and the controls give ALL_CONTROLS_OK True. Runs no Lean.
#
# written by tools-agent (sub-agent), fill bb1-machine
set -u
repo=$1
out=$2
src=${3:-/home/user/inhouse/r1/scope-request/BB1ReadersMin.lean.txt}
here=$(cd "$(dirname "$0")" && pwd)
d=TCSlib/Cryptography/AdvancedEncryption/IdentityBased
mkdir -p "$out/base"
for f in Defs BonehBoyen; do
  git -C "$repo" show "7c0a55e0239c14786612d0cd4462e64238543ca1:$d/$f.lean" > "$out/base/$f.lean"
done
python3 -I "$here/insertion_check.py" "$out/base/Defs.lean" "$repo/$d/Defs.lean" \
  "$out/base/BonehBoyen.lean" "$repo/$d/BonehBoyen.lean" "$src" > "$out/insertion-check.out" 2>&1
rc1=$?
python3 -I "$here/insertion_controls.py" "$out/base/Defs.lean" "$repo/$d/Defs.lean" \
  "$out/base/BonehBoyen.lean" "$repo/$d/BonehBoyen.lean" "$src" "$here/insertion_check.py" \
  "$out/controls" > "$out/insertion-controls.out" 2>&1
rc2=$?
tail -n 1 "$out/insertion-check.out"
tail -n 1 "$out/insertion-controls.out"
[ $rc1 -eq 0 ] && [ $rc2 -eq 0 ]
