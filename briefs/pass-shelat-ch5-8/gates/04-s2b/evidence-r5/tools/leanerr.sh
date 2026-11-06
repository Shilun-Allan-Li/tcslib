#!/usr/bin/env bash
# leanerr.sh <lean file> [lo hi]: compile against g04r6-oleans, print diagnostics (optionally for lines lo..hi)
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
export PATH="$HOME/.elan/bin:$PATH"
LP=$SP/g04r6-oleans; for d in /home/user/tcslib/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
export LEAN_PATH=$LP
cd $SP/wt-g04r4
lean "$1" > $SP/g04r6/leanerr.out 2>&1; echo "rc=$?"
python3 -I - "$SP/g04r6/leanerr.out" "${2:-0}" "${3:-999999}" <<'PY'
import re,sys
txt=open(sys.argv[1]).read(); lo,hi=int(sys.argv[2]),int(sys.argv[3])
blocks=re.split(r'(?m)^(?=\S+\.lean:\d+:\d+: )', txt)
for b in blocks:
    m=re.match(r'\S+\.lean:(\d+):\d+: (error|warning)', b)
    if m and m.group(2)=='error' and lo<=int(m.group(1))<=hi: print(b[:3000])
PY
