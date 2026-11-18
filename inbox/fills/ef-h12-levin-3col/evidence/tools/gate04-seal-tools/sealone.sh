#!/usr/bin/env bash
# sealone.sh <file.lean>...: plain seal of the given files at the worktree state, candidates cand-merge
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad; G=$SP/g04r6
printf '%s\n' "$@" > $G/one.txt
rm -rf $G/sealone
python3 -I $G/tools/seal.py plain $SP/wt-g04r4 $SP/g04r6-oleans $G/candidates $G/one.txt $G/sealone > /dev/null 2>&1
grep -E "PASS|FAIL|^   TCSlib" $G/sealone/results_plain.txt | cut -c1-230
