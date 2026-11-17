#!/usr/bin/env bash
# mkbase.sh: the gsw-6a-fills base, a deterministic local merge (unsigned; no checkout needed).
# Run in a clone that has the commits of land/gsw-6a-statements (#359) and land/gsw-6a-readers
# (#360) at the pinned heads below (fetch the branches by name, or refs/pull/359/head and
# refs/pull/360/head if a branch has moved).  Equivalent to `git merge --no-ff` of R into S with
# the same identity, dates and message (brief, "Base"); both give the same commit.
set -eu
export GIT_AUTHOR_NAME='TCSlib gsw-6a-fills staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid'
export GIT_COMMITTER_NAME='TCSlib gsw-6a-fills staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid'
export GIT_AUTHOR_DATE='2026-11-17T12:00:00+00:00' GIT_COMMITTER_DATE='2026-11-17T12:00:00+00:00'
S=73aedcdaaaffef7e69ab012d9b9195f150bae68d   # #359 head: 6a statements (on #358 O1 a616adca)
R=3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032   # #360 head: Q3 owner-side readers (on records 8c5875fa)
MSG='gsw-6a fills base: merge #360 head 3ea428fd (Q3 readers) into #359 head 73aedcda (6a statements)'
TB=$(git merge-tree --write-tree "$S" "$R")
test "$TB" = 7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3
B=$(git commit-tree --no-gpg-sign -p "$S" -p "$R" -m "$MSG" "$TB")
test "$B" = 05999162b77c1f0fef64b07427e1a041a31b43d2
echo "BASE $B tree $TB"
