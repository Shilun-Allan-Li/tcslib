#!/bin/zsh
# Run the v3 copy-text screen (unmodified copy) over the round-3 population in one tree, niced.
# usage: zsh screen.zsh <tree-root> <population-file> <out>
set -u
root=$1; pop=$2; out=$3; scr=${0:A:h}/copy-text-screen-v3.py
start=$(date +%s)
( cd $root && nice -n 10 python3 -I $scr $root $(cat $pop) > $out 2> $out.err ); rc=$?
end=$(date +%s)
echo "rc=$rc elapsed=$((end-start))s" > $out.status
