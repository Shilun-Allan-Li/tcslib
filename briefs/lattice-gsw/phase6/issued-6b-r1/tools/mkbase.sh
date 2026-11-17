#!/usr/bin/env bash
# mkbase.sh: the gsw-6b-statements base, a deterministic two-step local merge (unsigned; no checkout needed).
# Run in a clone that has cryptography/pass-shelat-ch2-4 at or past T, and the commits of
# land/gsw-6a-statements (#359) and land/gsw-6a-readers (#360) at the pinned heads below (fetch the branches by
# name, or refs/pull/359/head and refs/pull/360/head if a branch has moved, or the pinned commits by hash).
# Step 1 merges #360's head R into #359's head S (#359 contains #358, O1); step 2 merges step 1 into the records
# tip T, whose Lean is snapshot #6 (#357's merge 8060f6b7). Equivalent to two `git merge --no-ff` runs with the same
# identity, dates and messages (brief, "Base"); both forms give the same commits.
set -eu
export GIT_AUTHOR_NAME='TCSlib gsw-6b-statements staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid'
export GIT_COMMITTER_NAME='TCSlib gsw-6b-statements staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid'
export GIT_AUTHOR_DATE='2026-11-17T18:00:00+00:00' GIT_COMMITTER_DATE='2026-11-17T18:00:00+00:00'
S=d154c8830fc8ffc52671b41992e7dbef61e30959   # #359 head: 6a statements with LE-g45/LE-g45b (on #358 O1 a616adca)
R=cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25   # #360 head: 6a owner-side readers with the TreeDAG addendum
T=036d823933c8248bd8894c7963e15dd0f1837075   # records tip at staging (Lean = snapshot #6, 8060f6b7)
M1MSG='gsw-6b statements base, step 1: merge #360 head cc05f76c (6a readers) into #359 head d154c883 (6a statements)'
BMSG='gsw-6b statements base, step 2: merge the 6a drafts (step 1) into records tip 036d8239 (snapshot #6 Lean)'
T1=$(git merge-tree --write-tree "$S" "$R")
test "$T1" = 8eca961769fef59d5a22fd1b46dc821a614daf06
M1=$(git commit-tree --no-gpg-sign -p "$S" -p "$R" -m "$M1MSG" "$T1")
test "$M1" = 04947bcf35e08ed5f3a4902b2637a77482fd32d2
TB=$(git merge-tree --write-tree "$T" "$M1")
test "$TB" = b69a66a385ca3439d56af1d6b9791b5847984fde
B=$(git commit-tree --no-gpg-sign -p "$T" -p "$M1" -m "$BMSG" "$TB")
test "$B" = 3e51b5f28900db6190f1eb2e6d207d27ee15d541
echo "STEP1 $M1 tree $T1"
echo "BASE $B tree $TB"
