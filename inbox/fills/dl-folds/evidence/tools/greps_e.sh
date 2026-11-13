#!/usr/bin/env bash
# Grep receipts for group E, at the issue base (git grep on the base commit).
BASE=d3f2290a2c66f614e8807903b89ac595086578b3
cd /workspace/folds
run() { echo "### $1"; echo "\$ git grep -nE '$2' $BASE -- TCSlib audits"; git grep -nE "$2" $BASE -- TCSlib audits | sed "s/^$BASE://" ; echo; }
run E1-iterateEmit-uses 'polyTimeComputable_iterateEmit'
run E1-shapes 'flatMap fun i => [A-Za-z]+ \(\(?[A-Za-z]+( [A-Za-z]+)?\)\^\[i\]|\^\[i\] [A-Za-z]+\)\)?$'
run E1-orbit 'length_iterate_[A-Za-z]*_le|iterate_pairSndD_[A-Za-z]*'
run E2-guess 'guessBit|guessFun'
run E3-ctLen 'ctLen_pos|indImpl_eq_of_msgLen_eq_zero|0 < S\.ctLen\.eval'
