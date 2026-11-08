#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "pid=$$ -j4 $*" >> "${TCSLIB_REPLAY_LAUNCH_LOG:?}"
exec "${TCSLIB_REPLAY_REAL_LEAN:?}" -j4 "$@"
