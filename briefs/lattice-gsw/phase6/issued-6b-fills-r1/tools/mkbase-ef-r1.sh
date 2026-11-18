#!/usr/bin/env bash
# mkbase-ef-r1.sh <ef-r23-head> [<u18-u19-head>]  (gsw-6b-fills staging, issued-6b-fills-r1; maintainer tool)
# Builds the EF-R1 base deterministically (ruling Q-6BF-4 A): an unsigned --no-ff merge of the accepted EF-R2-R3 head
# (fill/ef-r23-regev, which sits on iO/phase-a-base 5ed465f6...) into the #377 merge bff0567b..., then, if given,
# an unsigned --no-ff merge of the accepted gsw-6b-u18-u19 head. Fixed identity, dates and messages, so every run
# gives the same commit. Run in a scratch clone that has both heads. Prints BASE <commit> tree <tree>; the
# maintainer records the output in EF-R1/base.md before the records pin is committed. Changes no ref but the
# local branch it creates.
set -euo pipefail
R23=${1:?ef-r23 head}; U1819=${2:-}
B6=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d
export GIT_AUTHOR_NAME='TCSlib ef-r1 staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid'
export GIT_COMMITTER_NAME='TCSlib ef-r1 staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid'
export GIT_AUTHOR_DATE='2026-11-18T12:00:00+00:00' GIT_COMMITTER_DATE='2026-11-18T12:00:00+00:00'
git cat-file -e "$R23^{commit}"; git cat-file -e "$B6^{commit}"
git merge-base --is-ancestor 5ed465f62e4ae0f93ded1a1ba49e807591b589eb "$R23" || { echo "E-BASE: $R23 is not on iO/phase-a-base"; exit 2; }
git checkout -q -B staging/ef-r1-base "$B6"
git -c commit.gpgsign=false -c merge.log=false merge -q --no-ff --no-edit \
  -m "ef-r1 base: merge EF-R2-R3 head ${R23:0:8} (general-modulus toolkit, on iO/phase-a-base) into #377 merge bff0567b" "$R23"
if [ -n "$U1819" ]; then
  git -c commit.gpgsign=false -c merge.log=false merge -q --no-ff --no-edit \
    -m "ef-r1 base: merge gsw-6b-u18-u19 head ${U1819:0:8} (Parameters.ofFamily_columns_le)" "$U1819"
fi
echo "BASE $(git rev-parse HEAD) tree $(git rev-parse HEAD^{tree})"
