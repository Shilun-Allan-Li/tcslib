#!/bin/bash
# The v3 copy-text screen, once, at the delivered head, under nice -n 10, holding the screen lock
# (coordinator, 2026-10-22). Waits for the lock; releases it also on failure.
LOCK=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/locks/screen.lock
POP=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/wt-rec/campaign/fills/mig12/inputs/mig12-fill-cfgrecord-cont1/screen-population.txt
OUT=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/mig12-cont1/out
W=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/mig12-cont1/wt-head
until mkdir "$LOCK" 2>/dev/null; do sleep 15; done
trap 'rmdir "$LOCK"' EXIT
echo "lock acquired $(date -u +%FT%TZ); other screens running: $(pgrep -f '[c]opy-text-screen-v3.py' | wc -l)" > "$OUT/25-screen-head.status"
cd "$W" || exit 1
start=$(date +%s)
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . $(grep -v '^#' "$POP") > "$OUT/25-screen-head.txt" 2> "$OUT/25-screen-head.err"
echo "exit=$? elapsed=$(( $(date +%s) - start ))s finished $(date -u +%FT%TZ)" >> "$OUT/25-screen-head.status"
