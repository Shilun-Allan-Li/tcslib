#!/usr/bin/env bash
# Reproduce every commit hash of the delivered series: in a scratch clone at the base, apply each
# patch with `git am`, with the committer identity and date of COMMITS.tsv, and compare hashes.
# Usage: repro_check.sh <delivery dir> <log>
set -u
D="$1"; log="$2"; B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d; S=/tmp/u13-repro
{
echo "# reproduction check, $(date -u +%FT%TZ)"
rm -rf $S
git clone -q --shared --no-checkout /workspace/tcslib $S
git -C $S -c advice.detachedHead=false checkout -q $B
git -C $S config user.name repro; git -C $S config user.email repro@invalid
ok=0; bad=0
tail -n +2 "$D/patches/COMMITS.tsv" | while IFS=$'\t' read -r n hash an ae ad cn ce cd sig subj; do
  p=$(ls "$D"/patches/$(printf '%04d' $n)-*.patch)
  GIT_COMMITTER_NAME="$cn" GIT_COMMITTER_EMAIL="$ce" GIT_COMMITTER_DATE="$cd" git -C $S -c commit.gpgsign=false am -q "$p"
  got=$(git -C $S rev-parse HEAD)
  if [ "$got" = "$hash" ]; then echo "MATCH $n $hash"; else echo "MISMATCH $n expected $hash got $got"; fi
done
echo "base $B; scratch clone $S (git clone --shared of the local repository)"
} > "$log" 2>&1
cat "$log"
grep -q MISMATCH "$log" && echo "RESULT: MISMATCH" >> "$log" || echo "RESULT: every hash reproduced" >> "$log"
tail -1 "$log"
rm -rf $S
