#!/usr/bin/env bash
set -euo pipefail
source /Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/env.sh
export PATH="$TCSLIB_SCRATCH/replay-j4/bin:$PATH"
export TCSLIB_REPLAY_REAL_LEAN=/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/bin/lean
export TCSLIB_REPLAY_LAUNCH_LOG="$2"
exec bash "$1"
