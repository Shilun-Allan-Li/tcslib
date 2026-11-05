#!/usr/bin/env bash
# usage: elab.sh <olean dir> <abs lean file> <out tag>   (plain elaboration through the tool, timed)
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
/usr/bin/time -l bash $S/tools/leanelab.sh $R/wt-head "$1" "$2" > $R/out/$3.out 2> $R/out/$3.time
echo "exit=$?" >> $R/out/$3.time
