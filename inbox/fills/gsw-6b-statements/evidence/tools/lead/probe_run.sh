#!/usr/bin/env bash
# probe_run.sh <worktree> <probe.lean> (gsw-6b-statements, new): elaborate a probe file (no -o) with
# LEAN_PATH = $TCSLIB_OLEANS plus the packages' build dirs, from inside <worktree>.
set -u
wt="$1"; f="$2"; LP="$TCSLIB_OLEANS"
for d in "$wt"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
cd "$wt" && LEAN_PATH="$LP" lean "$f"
