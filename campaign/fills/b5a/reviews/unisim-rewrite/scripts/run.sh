#!/usr/bin/env bash
# run.sh <name> : elaborate rvprobe/<name>.lean in the review worktree, raw output to out/<name>.out
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/b5a-brief; W=$R/wt; N="$1"
start=$(date +%s)
/usr/bin/time -l bash $S/tools/leanelab.sh $W $S/oleans-laplusm rvprobe/$N.lean > $R/out/$N.raw 2> $R/out/$N.time
st=$?
end=$(date +%s)
sed "s#$W/##g" $R/out/$N.raw > $R/out/$N.out
peak=$(grep "maximum resident set size" $R/out/$N.time | awk '{print $1}')
echo "# command: bash \$S/tools/leanelab.sh \$W \$S/oleans-laplusm rvprobe/$N.lean; exit $st; wall $((end-start)) s; peak $peak bytes" >> $R/out/$N.out
rm -f $R/out/$N.raw
tail -1 $R/out/$N.out
