#!/bin/bash
# usage: refgrep.sh <out>: grep every local and remote ref's TCSlib tree for the statements of the
# new privates and of the inner facts the neighbouring deciders prove; unique hits with one ref each.
G=/Users/seyoonr/phd_experiments/tcslib
PAT='(decide \(x = w\)\]|getD \[\] = \[\]|replicate x\.length true\)\]|≠ some \[\]|computesFunInTime_decideEq|computesFunInTime_allTrue|computesFunInTime_unary|qy_guard|qy_query_of_main|\bqy_|\bQy[A-Z])'
for r in $(git -C $G for-each-ref --format='%(refname)' refs/heads refs/remotes | grep -v '/HEAD$'); do
  git -C $G grep -n -P "$PAT" "$r" -- 'TCSlib/*.lean' 2>/dev/null | sed "s|^$r:||" | sed "s|^|$r\t|"
done | sort -t$'\t' -k2 -u > "$1"
echo "unique (path:line:text) hits: $(wc -l < "$1")"
