#!/usr/bin/env bash
# Copy screen (scripts/copy-text-screen-v3.py) over the four E2 files. Every pair it lists is
# classified in campaign/fills/e2/REPORT.md, § Duplication ledger.
set -u
cd "$(cd "$(dirname "$0")/../../../../.." && pwd)"
python3 -I scripts/copy-text-screen-v3.py . TCSlib/Complexity/Promise/Basic.lean \
  TCSlib/Complexity/Counting/PP.lean TCSlib/Complexity/Counting/GapP.lean \
  TCSlib/Complexity/Counting/Inclusions.lean
