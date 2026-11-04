#!/usr/bin/env bash
# One dev check through scripts/lean_check_tree.sh (timed), output filtered for diagnostics.
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/tcslib
python3 -I evidence/runtime/timed_check.py /home/user/tcslib "$1" 2>&1 | grep -v "^$" | head -${2:-60}
