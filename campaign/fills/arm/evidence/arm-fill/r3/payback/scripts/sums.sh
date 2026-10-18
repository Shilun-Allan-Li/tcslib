#!/usr/bin/env bash
# SHA256SUMS of the landing directory's deliverables. Usage: bash sums.sh <L>
set -eo pipefail
L="$1"
cd "$L"
{ find tree patches scripts logs -type f ! -path '*/__pycache__/*'; echo replay-order.txt
  for f in ledger-map.md LANDING-NOTES.md; do if [ -f "$f" ]; then echo "$f"; fi; done; } \
  | LC_ALL=C sort \
  | xargs shasum -a 256 > "$L/SHA256SUMS"
