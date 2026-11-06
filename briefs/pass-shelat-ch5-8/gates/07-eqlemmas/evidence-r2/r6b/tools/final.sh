#!/usr/bin/env bash
# final.sh: the evidence run at the final commit (gate 04 round 4). Run after the downstream replay.
#   (a) automatic candidates: tools/collect.sh (run first)        -> candidates/, candidates-base/
#   (b) seal at the final head (named unseal entries applied)    -> seal-evidence.log
#       control: the $BASE copy of each file, same entries        -> seal-control-base.log
#       plain seal (no entry at all), for the record              -> seal-plain.log
#   (c) source scan at the final head and at $BASE               -> scan.log, scan-base.log
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
G=$SP/g04r4; WT=$SP/wt-g04r4; T=$G/tools
BASE=$(cat $G/base.txt); HEAD=$(git -C $WT rev-parse HEAD)
[ -z "$(git -C $WT status --porcelain -- TCSlib)" ] || { echo "worktree not clean"; exit 2; }
[ -s $G/candidates/summary.tsv ] && [ -s $G/candidates-base/summary.tsv ] || { echo 'run collect.sh first'; exit 4; }
rm -rf $G/sealout-final $G/sealout-base
cd $G
python3 -I $T/seal.py final $WT $SP/g04r4-oleans $G/candidates $G/changed-files.txt $G/sealout-final \
  --unseal $G/unseal.json > /dev/null
{ echo "# rule-10 seal at $HEAD (final head of wip/g04r4; base $BASE): each of the 26 files compiled"
  echo "# with \`attribute [local irreducible]\` on every automatically collected candidate (candidates/),"
  echo "# the named entries of unseal.json unsealed only around their declaration (exclusions.md)"
  cat $G/sealout-final/results_final.txt; } > $G/seal-evidence.log
python3 -I $T/seal.py base $WT $SP/s2bfix-r3-oleans $G/candidates-base $G/changed-files.txt $G/sealout-base \
  --rev $BASE --unseal $G/unseal.json --lenient > /dev/null
{ echo "# control: the same seal on the \$BASE copy ($BASE) of each file, against the \$BASE olean tree,"
  echo "# with the \$BASE candidates (candidates-base/) and the same named entries"
  cat $G/sealout-base/results_base.txt; } > $G/seal-control-base.log
if [ ! -s $G/sealout-plain/results_plain.txt ]; then
python3 -I $T/seal.py plain $WT $SP/g04r4-oleans $G/candidates $G/changed-files.txt $G/sealout-plain > /dev/null
{ echo "# for the record: the same seal at $HEAD with no unseal entry at all (every failure here is"
  echo "# an entry of exclusions.md, section A or C)"
  cat $G/sealout-plain/results_plain.txt; } > $G/seal-plain.log
fi
python3 -I $T/scan.py $WT $G/changed-files.txt $G/candidates/tcslib-constants.tsv $G/candidates \
  $G/sealout-plain/results_plain.txt $G/scan.log
python3 -I $T/scan.py $WT $G/changed-files.txt $G/candidates-base/tcslib-constants.tsv $G/candidates-base \
  $G/sealout-base/results_base.txt $G/scan-base.log --rev $BASE
echo "final.sh done at $HEAD"
