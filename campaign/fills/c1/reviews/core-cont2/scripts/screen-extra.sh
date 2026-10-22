#!/usr/bin/env bash
# Extra (outside the brief's population) v3 screen: the owned file at the head against the published rewind lemmas
# (Simulation), the input-rewind leaves elsewhere (SpaceComplexity/Inclusions, Build/InputWindow) and Build/Rewind.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/c1-core-cont2; SCR=$R/wt-base/scripts/copy-text-screen-v3.py
until mkdir $S/locks/screen.lock 2>/dev/null; do sleep 15; done
trap 'rmdir $S/locks/screen.lock' EXIT
echo "33-screen-extra start $(date -u +%FT%TZ)" >> $R/out/29-30-screens.log
nice -n 10 python3 -I $SCR $R/wt-head TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean TCSlib/Complexity/TuringMachine/Simulation.lean TCSlib/Complexity/SpaceComplexity/Inclusions.lean TCSlib/Complexity/TuringMachine/Build/InputWindow.lean TCSlib/Complexity/TuringMachine/Build/Rewind.lean > $R/out/33-screen-extra.txt 2> $R/out/33-screen-extra.txt.err; echo $? > $R/out/33-screen-extra.txt.status
echo "33-screen-extra end $(date -u +%FT%TZ) status $(cat $R/out/33-screen-extra.txt.status)" >> $R/out/29-30-screens.log
