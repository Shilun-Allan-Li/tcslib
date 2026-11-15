#!/usr/bin/env bash
# Development check of one module with a heartbeat limit (scratch copy; not evidence).
# usage: tst.sh Module  (relative to TCSlib/Cryptography/SecureComputation/ComposeSecurity/)
cd /workspace/scc
export PATH=$HOME/.elan/bin:$PATH
src=TCSlib/Cryptography/SecureComputation/ComposeSecurity/$1.lean
mkdir -p scratch/dev
sed 's/^set_option maxHeartbeats 0$/set_option maxHeartbeats 400000/' $src > scratch/dev/T_$1.lean
LP=$PWD/.lake/tcslib-check-oleans:$(for d in $(ls .lake/packages); do printf '%s:' $PWD/.lake/packages/$d/.lake/build/lib/lean; done)
LEAN_PATH=$LP timeout ${2:-280} lean scratch/dev/T_$1.lean 2>&1 | grep -v "^  \|^$" | head -${3:-40}
echo "EXIT ${PIPESTATUS[0]}"
