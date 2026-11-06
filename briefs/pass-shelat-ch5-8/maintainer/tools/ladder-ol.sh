#!/usr/bin/env bash
# ladder with a separate olean tree: ladder-ol.sh <worktree> <order> <log> <oleans-dir> [start]
export TCSLIB_OLEANS="$4"
exec bash "$(dirname "$0")/ladder.sh" "$1" "$2" "$3" "${5:-}"
