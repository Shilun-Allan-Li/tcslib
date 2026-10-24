#!/bin/bash
# The v3 screen of C1's 16-file population at the review worktree (= the drafting base's Lean),
# once, under the machine-wide screen lock, niced; the lock is released even on failure.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/megafill-c-c1
W=$R/wt
P=$S/wt-hk/campaign/fills/c1/drafts/c1-fill-replaycanon/preship-77f1eb4f
until mkdir $S/locks/screen.lock 2>/dev/null; do sleep 15; done
trap 'rmdir $S/locks/screen.lock' EXIT
cd $W || exit 1
echo "start $(date -u +%FT%TZ)" > $R/out/05-screen.status
nice -n 10 python3 -I scripts/copy-text-screen-v3.py $W $(grep -v '^#' $P/screen-population.txt) > $R/out/05-screen.txt 2> $R/out/05-screen.stderr
echo "exit $? end $(date -u +%FT%TZ)" >> $R/out/05-screen.status
