#!/usr/bin/env bash
# Run chk.py on one module in the background (nohup), so that a long check survives the 300 s
# tool limit; the log is written in place.  usage: bgchk.sh MODULE LOG
export PATH=$HOME/.elan/bin:$PATH
nohup setsid python3 -I /workspace/pltools/chk.py "$1" > "$2" 2>&1 &
