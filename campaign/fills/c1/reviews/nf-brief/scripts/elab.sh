#!/usr/bin/env bash
# usage: elab.sh <file.lean> <outname> ; runs leanelab on the review worktree against oleans-lnfapi4
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/nf-brief
f="$1"; n="$2"
start=$(date +%s)
/usr/bin/time -l bash $S/tools/leanelab.sh $R/wt $S/oleans-lnfapi4 "$f" > $R/out/$n.raw 2> $R/out/$n.time
rc=$?
echo "exit $rc" >> $R/out/$n.time
sed -e "s#$R/wt/rvprobe/##g" -e "s#$R/wt/##g" $R/out/$n.raw > $R/out/$n.out
echo "$n: exit $rc, $(( $(date +%s) - start )) s"
