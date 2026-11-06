#!/usr/bin/env bash
# build.sh <module>...: lean_check_tree.sh each module (no .lean) into g04r6-oleans, stop at first failure
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
export PATH="$HOME/.elan/bin:$PATH"
cd $SP/wt-g04r4
for m in "$@"; do
  out=$(TCSLIB_OLEANS=$SP/g04r6-oleans bash scripts/lean_check_tree.sh "$m" 2>&1); rc=$?
  echo "$m rc=$rc errors=$(printf '%s\n' "$out" | grep -c 'error:')"
  if [ $rc -ne 0 ]; then printf '%s\n' "$out" | grep -A12 'error:' | head -80; exit 1; fi
done
