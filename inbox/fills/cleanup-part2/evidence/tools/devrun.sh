#!/usr/bin/env bash
# Development pass: check the listed modules in order (phase dev); stop at the first failure.
export CHK_PHASE=${CHK_PHASE:-dev}
L=$1; START=${2:-1}
n=0
while read -r m; do n=$((n+1)); [ $n -lt $START ] && continue; echo "## $n $m"; python3 -I /workspace/cp2/tools/chk.py "$m" || { echo "STOP $n $m"; exit 1; }; done < $L
echo "ALL PASS"
