#!/usr/bin/env bash
# The head screen against the campaign's screen base and the worker's final screen.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
X=$S/intake/eq-diagonalizer/x/fill-eq-diagonalizer/evidence/screens
BASE=$S/wt-hk/campaign/fills/eq/logs/eq-fill-diagonalizer-screen-base.txt
echo "== summary lines"; head -1 $BASE; head -1 $R/out/17-screen-head.txt; head -1 $X/screen-final.txt
echo "== head screen vs the worker's final screen (data): $(cmp -s $R/out/17-screen-head.txt $X/screen-final.txt && echo byte-identical || echo DIFFERENT)"
echo "== new and gone pairs against the base"; python3 -I $S/tools/pairdiff.py $R/out/17-screen-head.txt $BASE
echo "== pairs at 90% or more with an owned-file side, new at head"
python3 -I $S/tools/pairdiff.py $R/out/17-screen-head.txt $BASE | awk '/NEW/ && /NTimeDiagonalizer/' | awk '{p=$NF; sub("%","",p); if (p+0 >= 90) print}'
