#!/usr/bin/env bash
# run_probe.sh <probe.lean> (gsw-6b-statements, sub-agent probe; new): elaborate one probe file
# with `lean` (no -o), LEAN_PATH = the probe olean tree /home/user/oleans/probe + every
# /home/user/sub/probe/.lake/packages/*/.lake/build/lib/lean (the construction of
# scripts/lean_check_tree.sh), from inside the worktree /home/user/sub/probe. Meant to be
# called under the shared pool: python3 -I /home/user/ev/tools/lead/pool_run.py <label> <log> --
# bash /home/user/ev/tools/probe/run_probe.sh <probe.lean>. Prints lean's output; exits with
# lean's rc.
set -u
export PATH="$HOME/.elan/bin:$PATH"
ROOT=/home/user/sub/probe
LP=/home/user/oleans/probe
for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"
cd "$ROOT"
lean "$1" 2>&1
