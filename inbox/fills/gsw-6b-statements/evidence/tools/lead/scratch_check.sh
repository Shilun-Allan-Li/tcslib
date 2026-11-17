#!/usr/bin/env bash
# scratch_check.sh <worktree> <module> <out-dir> (gsw-6b-statements, new): elaborate one module of
# <worktree> with `lean`, reading imports from the lead's olean tree $TCSLIB_OLEANS (read-only) plus
# the packages, writing its .olean only under <out-dir> (never into the lead tree). Used for
# development checks and probes; the evidence builds go through scripts/lean_check_tree.sh.
set -u
wt="$1"; rel="$2"; out="$3"
LP="$TCSLIB_OLEANS"
for d in "$wt"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
mkdir -p "$out/$(dirname "$rel")"
cd "$wt" && LEAN_PATH="$LP:$out" lean "$rel.lean" -o "$out/$rel.olean"
