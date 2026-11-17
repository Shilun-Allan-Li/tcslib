#!/usr/bin/env bash
# run_capped.sh <probe.lean> <seconds> (gsw-6b-statements, sub-agent probe; new): run_probe.sh under a time cap
# that counts only the Lean run (it is called inside pool_run.py, after the slot is acquired). On the cap,
# `timeout` stops Lean (exit 124); the probe's `.progress` file keeps the part already evaluated.
timeout "$2" bash /home/user/ev/tools/probe/run_probe.sh "$1"
