#!/usr/bin/env bash
# Freeze the brief's screen population at the head (the commands run before scripts/screen.sh).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
POP=$S/wt-hk/campaign/fills/eq/inputs/eq-fill-diagonalizer/screen-population.txt
grep -v '^#' $POP | grep . > $R/out/17-population.txt
mkdir -p $R/screen-head
(cd $R/wt-head && while read f; do mkdir -p $R/screen-head/$(dirname $f); cp $f $R/screen-head/$f; done < $R/out/17-population.txt)
cp $R/wt-head/scripts/copy-text-screen-v3.py $R/scripts/copy-text-screen-v3.py
shasum -a 256 $R/scripts/copy-text-screen-v3.py > $R/out/17-screen-script.sha256
