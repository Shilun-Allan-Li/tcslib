#!/usr/bin/env bash
# mkbase.sh: the bb1-sim fill's two deterministic local base commits (unsigned; no checkout needed).
# Run in a clone that has fetched cryptography/pass-shelat-ch2-4, land/pairings-bb1-machine and fill/pairings-pair-bdh.
set -eu
export GIT_AUTHOR_NAME='TCSlib bb1-sim staging' GIT_AUTHOR_EMAIL='staging@tcslib.invalid'
export GIT_COMMITTER_NAME='TCSlib bb1-sim staging' GIT_COMMITTER_EMAIL='staging@tcslib.invalid'
export GIT_AUTHOR_DATE='2026-11-17T00:00:00+00:00' GIT_COMMITTER_DATE='2026-11-17T00:00:00+00:00'
I=89a18a8225be1b76166af12a15179da291747783   # #346 head (issue base)
T=ca129d64cd54a92aabe517e5262058664b49f651   # records tip at issue (Lean = 463f2244, snapshot #4)
P=916afc25c21f5e52b4b01958186ad55d2f615fd1   # #340 head (T1)
TB=$(git merge-tree --write-tree "$I" "$T")
test "$TB" = b5a5842dd0a5af86975864b29065bec44758f561
B=$(git commit-tree --no-gpg-sign -p "$I" -p "$T" \
  -m 'bb1-sim fill patch base: merge the records tip ca129d64 into #346 head 89a18a82' "$TB")
TC=$(git merge-tree --write-tree "$B" "$P")
test "$TC" = 02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d
C=$(git commit-tree --no-gpg-sign -p "$B" -p "$P" \
  -m 'bb1-sim fill check base: merge #340 head 916afc25 (T1)' "$TC")
echo "PATCH_BASE $B tree $TB"
echo "CHECK_BASE $C tree $TC"
