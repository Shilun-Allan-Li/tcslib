#!/usr/bin/env bash
# run_frozen.sh <fill-worktree> <outdir> (bb1-sim, lead): frozen_check.py on the head files against the patch base
# 72c0498a (read with git show), then frozen_controls.py. Runs no Lean.
set -u
W=$1; O=$2; here=$(cd "$(dirname "$0")" && pwd); P=72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c
R=TCSlib/Cryptography/Games/Relational.lean; S=TCSlib/Cryptography/AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean
mkdir -p $O/base; git -C $W show $P:$R > $O/base/Relational.lean; git -C $W show $P:$S > $O/base/BonehBoyenSecurity.lean
git -C $W rev-parse HEAD > $O/HEAD.txt
python3 -I $here/frozen_check.py $O/base/Relational.lean $W/$R $O/base/BonehBoyenSecurity.lean $W/$S > $O/frozen-check.out 2>&1; r1=$?
python3 -I $here/frozen_controls.py $O/base/Relational.lean $W/$R $O/base/BonehBoyenSecurity.lean $W/$S $here/frozen_check.py $O/controls > $O/frozen-controls.out 2>&1; r2=$?
tail -n 1 $O/frozen-check.out; tail -n 1 $O/frozen-controls.out
[ $r1 -eq 0 ] && [ $r2 -eq 0 ]
