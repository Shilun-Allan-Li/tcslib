#!/usr/bin/env bash
# assemble.sh <outdir> <o2-head> <stmt-head> (gsw-6b-statements, new): build the payload skeleton
# under <outdir>: patches/o2 (format-patch base..o2), patches/stmt (format-patch o2..stmt), each with
# COMMITS.tsv (hash, author name/email/date, committer name/email/date, signing); src/ = every file
# changed base..stmt at the stmt head; src-o2/ = BitEncoding.lean at the O2 head. Evidence, REPORT.md
# and SHA256SUMS are added by the caller.
set -eu
OUT=$1; O2=$2; ST=$3; B=3e51b5f28900db6190f1eb2e6d207d27ee15d541; R=/home/user/w6b
mkdir -p $OUT/patches/o2 $OUT/patches/stmt $OUT/src $OUT/src-o2
rm -f $OUT/patches/o2/*.patch $OUT/patches/stmt/*.patch
git -C $R format-patch -q --no-signature -o $OUT/patches/o2 $B..$O2
git -C $R format-patch -q --no-signature -o $OUT/patches/stmt $O2..$ST
for s in o2:$B..$O2 stmt:$O2..$ST; do
  { printf 'hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning\n'
    git -C $R log --reverse --format='%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%G?' ${s#*:} |
      awk -F'\t' 'BEGIN{OFS="\t"}{ $8 = ($8=="N" ? "none" : $8); print }'
  } > $OUT/patches/${s%%:*}/COMMITS.tsv
done
for f in $(git -C $R diff --name-only $B $ST); do mkdir -p $OUT/src/$(dirname $f); git -C $R show $ST:$f > $OUT/src/$f; done
f=TCSlib/Cryptography/LWE/BitEncoding.lean; mkdir -p $OUT/src-o2/$(dirname $f); git -C $R show $O2:$f > $OUT/src-o2/$f
echo "assembled $OUT: $(ls $OUT/patches/o2/*.patch | wc -l) + $(ls $OUT/patches/stmt/*.patch | wc -l) patches, $(find $OUT/src -type f | wc -l) src files"
