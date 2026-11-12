#!/usr/bin/env bash
# usage: runseal.sh VAR NAME...
export PATH=$HOME/.elan/bin:$PATH
cd /workspace/sim
LP=.lake/tcslib-check-oleans; for d in .lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
v=$1; shift
for n in "$@"; do s=$(date +%s); LEAN_PATH=$LP timeout 280 lean scratch/seal/Seal$v$n.lean > /workspace/simpay/evidence/logs/seal/seal$v-$n.log 2>&1; st=$?; echo "$v $n exit=$st $(( $(date +%s)-s ))s errors=$(grep -c ': error' /workspace/simpay/evidence/logs/seal/seal$v-$n.log)"; done
