#!/usr/bin/env bash
# run.sh <file.lean>: elaborate a probe against the e1 (head) olean tree, no olean output
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
ROOT=$SP/wt-e1; LP=$SP/e1-oleans
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP" PATH="$HOME/.elan/bin:$PATH"
F=$(readlink -f "$1"); cd "$ROOT" && lean "$F"; echo "rc=$?"
