#!/usr/bin/env bash
# c1.sh <repo> <olean-tree> <outdir> <module>... : check modules in order, summary bound to git show HEAD
R=$1; OL=$2; D=$3; shift 3; mkdir -p $D/logs; cd $R; export PATH=$HOME/.elan/bin:$PATH
S=$D/summary.txt; printf "# head %s\nmodule\trc\terrors(error: / error()\tsorry_warnings\tsha256(worktree)\tsha256(git show HEAD)\tmatch\tmaxRSS_kB\n" "$(git rev-parse HEAD)" > $S
for m in "$@"; do
 L=$D/logs/$(echo $m | tr / .).log; TCSLIB_OLEANS=$OL python3 -I /home/user/scripts/timev.py bash scripts/lean_check_tree.sh $m > $L 2>&1; rc=$?
 e1=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error:' $L); e2=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error\(' $L); so=$(grep -c "declaration uses 'sorry'" $L)
 h1=$(sha256sum $m.lean | cut -c1-64); h2=$(git show HEAD:$m.lean | sha256sum | cut -c1-64); rss=$(grep -o 'Maximum resident set size (kbytes): [0-9]*' $L | awk '{print $NF}')
 printf "%s\t%s\t%s/%s\t%s\t%s\t%s\t%s\t%s\n" $m $rc $e1 $e2 $so $h1 $h2 $([ $h1 = $h2 ] && echo OK || echo DIFF) $rss >> $S; done; cat $S
