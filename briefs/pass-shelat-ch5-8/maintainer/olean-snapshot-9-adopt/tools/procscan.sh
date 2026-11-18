#!/bin/bash
# procscan.sh <dir>...: list processes whose cwd, root, exe, open fds, maps or environment refer to any <dir>.
for pd in /proc/[0-9]*; do
  pid=${pd#/proc/}; [ "$pid" = "$$" ] && continue
  hits=""
  for d in "$@"; do
    for l in cwd root exe; do t=$(readlink $pd/$l 2>/dev/null); case "$t" in "$d"|"$d"/*) hits="$hits $l:$t";; esac; done
    for f in $pd/fd/*; do t=$(readlink $f 2>/dev/null); case "$t" in "$d"|"$d"/*) hits="$hits fd:$t";; esac; done
    grep -qF "$d" $pd/maps 2>/dev/null && hits="$hits maps"
    { tr "\0" "\n" < $pd/environ; } 2>/dev/null | grep -qF "$d" && hits="$hits environ"
  done
  [ -n "$hits" ] && echo "$pid $({ tr "\0" " " < $pd/cmdline; } 2>/dev/null | cut -c1-200) :$hits"
done
echo "scan done"
