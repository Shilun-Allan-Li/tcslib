#!/usr/bin/env bash
# Run scripts/campaign_style_lint.py over the whole TCSlib tree (so the facades
# TCSlib/Quantum.lean, TCSlib/Complexity/Promise.lean and TCSlib/Complexity/Counting.lean are covered;
# round-1 audit, finding 7) and keep the lines for the 14 audited files.
set -u
cd "$(cd "$(dirname "$0")/../../../../.." && pwd)"
python3 scripts/campaign_style_lint.py TCSlib 2>&1 \
  | grep -E 'TCSlib/(Quantum|Complexity/Promise|Complexity/Counting)(/|\.lean)' | sort
