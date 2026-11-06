#!/usr/bin/env bash
# Elaborate a scratch file (no olean) against the bootstrap tree.
cd /workspace/tcslib-fill
export PATH=$HOME/.elan/bin:$PATH
OL=/workspace/tcslib-fill/.lake/tcslib-check-oleans
LP="$OL"
for d in /workspace/tcslib-fill/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"
s=$(date +%s)
lean "$1" 2>&1
echo "rc=$? secs=$(( $(date +%s) - s ))"
