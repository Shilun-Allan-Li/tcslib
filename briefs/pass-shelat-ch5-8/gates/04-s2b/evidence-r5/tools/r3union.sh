#!/usr/bin/env bash
# r3union.sh: supplementary check. For the files whose r3 hand-picked seal row names a definition the
# automatic list does not contain (tools/r3cross.py), seal the automatic candidates PLUS those names,
# with the same named entries, at the final head. Expected: same result as seal-evidence.log.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
G=$SP/g04r6; T=$G/tools; U=$G/r3union
rm -rf $U; mkdir -p $U/cand
cp $G/candidates/*.txt $U/cand/
python3 -I $T/r3cross.py /home/user/tcslib/briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r3/seal.py.txt \
  $G/candidates > $U/r3cross.txt
grep '^  not in the automatic list:' $U/r3cross.txt | while read -r _ _ _ _ _ path name; do
  mod=$(echo "${path%.lean}" | tr / .)
  printf '%s\t(r3 hand-picked)\tr3\t-\n' "$name" >> $U/cand/$mod.txt
  echo "$path"
done | sort -u > $U/files.txt
python3 -I $T/seal.py r3union $SP/wt-g04r4 $SP/g04r6-oleans $U/cand $U/files.txt $U/sealout --unseal $G/unseal.json > /dev/null
{ echo "# supplementary: automatic candidates + the r3 hand-picked names they lack (r3cross.txt), same entries"
  cat $U/r3cross.txt; cat $U/sealout/results_r3union.txt; } > $G/seal-r3union.log
grep -c ' PASS ' $U/sealout/results_r3union.txt
