#!/usr/bin/env bash
# collect.sh: automatic seal candidates at the final head (candidates/) and at $BASE (candidates-base/).
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
G=$SP/g04r4; WT=$SP/wt-g04r4; T=$G/tools
BASE=$(cat $G/base.txt)
[ -z "$(git -C $WT status --porcelain -- TCSlib)" ] || { echo "worktree not clean"; exit 2; }
rm -rf $G/candidates $G/candidates-base
# two passes: the first collection gives the constant table; the source scan resolves the lemmas
# named in lemma lists (srclemmas/); the second collection adds their statements (`src:` tier)
collect2() {  # <olean-tree> <outdir> [--rev REV]
  bash $T/run_collect.sh $WT $1 $2 > $2.out1 2>&1 || exit 3
  python3 -I $T/scan.py $WT $G/changed-files.txt $2/tcslib-constants.tsv $2 /dev/null /dev/null \
    --srclemmas $2/srclemmas ${3:-} ${4:-} > /dev/null
  bash $T/run_collect.sh $WT $1 $2 > $2.out2 2>&1 || exit 3
}
collect2 $SP/g04r4-oleans $G/candidates
collect2 $SP/s2bfix-r3-oleans $G/candidates-base --rev $BASE
echo "collect.sh done at $(git -C $WT rev-parse HEAD)"
