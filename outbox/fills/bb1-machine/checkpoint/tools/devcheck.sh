#!/usr/bin/env bash
# devcheck.sh <worktree> <tree> <file.lean> (fill-pair-bdh; reused by fill-bb1-machine): elaborate one file for development
# with the tree's oleans on LEAN_PATH (as scripts/lean_check_tree.sh sets it), WITHOUT -o: nothing is written to the tree.
# One process; prints rc.
set -u
W=$1; T=$2; F=$3
LP="$T"; for d in "$W"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
cd "$W" && PATH="$HOME/.elan/bin:$PATH" LEAN_PATH="$LP" nice -n 10 lean -DmaxErrors=0 "$F"; echo "rc=$?"
