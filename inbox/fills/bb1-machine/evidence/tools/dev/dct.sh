#!/usr/bin/env bash
# dct.sh <seconds> <file.lean>: devcheck (no -o) on wt-fill-bb1-machine with dl-oleans; lean itself under timeout.
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
W=$SP/wt-fill-bb1-machine; T=$SP/dl-oleans
LP="$T"; for d in "$W"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
cd "$W" && PATH="$HOME/.elan/bin:$PATH" LEAN_PATH="$LP" timeout -s KILL "$1" nice -n 10 lean -DmaxErrors=0 "$2"; echo "rc=$?"
