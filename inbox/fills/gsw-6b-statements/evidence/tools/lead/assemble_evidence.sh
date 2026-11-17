#!/usr/bin/env bash
# assemble_evidence.sh <payload-dir> (gsw-6b-statements, new): copy the final evidence into
# <payload>/evidence (scratch dirs and caches left out), then write evidence/SHA256SUMS and the
# top-level SHA256SUMS (every delivered file except itself; no leading ./) and verify both.
set -eu
D=$1; E=$D/evidence; S=/home/user/ev
rm -rf $E; mkdir -p $E
for d in logs build stmt admissions headers rule10 probes census clash dup citations lint sizes records subagents tools; do
  [ -e $S/$d ] && cp -a $S/$d $E/; done
cp /home/user/pool/pool.log $E/logs/pool.log
cp $S/repro-final.log $S/repro-cp1.log $E/
find $E -name '__pycache__' -prune -exec rm -rf {} + ; find $E -name '*.olean' -delete; find $E -name '*.ilean' -delete
find $E -type l -delete
(cd $E && find . -type f ! -name SHA256SUMS | sed 's|^\./||' | LC_ALL=C sort | xargs -d '\n' sha256sum > SHA256SUMS)
(cd $D && find . -type f ! -path ./SHA256SUMS | sed 's|^\./||' | LC_ALL=C sort | xargs -d '\n' sha256sum > SHA256SUMS)
(cd $E && sha256sum -c --quiet SHA256SUMS) && (cd $D && sha256sum -c --quiet SHA256SUMS)
diff <(cd $D && find . -type f ! -path ./SHA256SUMS | sed 's|^\./||' | LC_ALL=C sort) <(awk '{print substr($0, 67)}' $D/SHA256SUMS | LC_ALL=C sort)
echo "evidence $(wc -l < $E/SHA256SUMS) files; payload $(wc -l < $D/SHA256SUMS) files; $(du -sh $D | cut -f1); paths equal"
