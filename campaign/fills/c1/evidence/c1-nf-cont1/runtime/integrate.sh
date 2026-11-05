#!/usr/bin/env bash
# integrate.sh part... : write the owned module = base lines 1-704 + parts + base lines 705-end
set -u
cd /home/user/tcslib
BASE=scratch/NDNormalForm.base.lean
OUT=TCSlib/Complexity/ClassNP/NDNormalForm.lean
{ head -n 704 "$BASE"; for p in "$@"; do cat "$p"; done; tail -n +705 "$BASE"; } > "$OUT"
wc -l "$OUT"
