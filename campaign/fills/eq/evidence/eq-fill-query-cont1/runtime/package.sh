#!/usr/bin/env bash
# Package a delivery zip as of HEAD: package.sh <name> <evidence-dir> <final-sweep-log>
# e.g. package.sh fill-eq-query-cont1-cp2 evidence/cp2 evidence/cp2/tail-check.log
set -eu
ROOT=/home/user/tcslib
cd $ROOT
NAME="$1"; EV="$2"; SWEEP="$3"
BASE=43fe918f2b7612b46d6b1bd6d4201651f7243430
F=TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean
git diff --quiet HEAD -- $F || { echo "owned file differs from HEAD"; exit 1; }
ST=$(mktemp -d)/$NAME
mkdir -p $ST/source/$(dirname $F) $ST/patches $ST/logs $ST/seal $ST/probe $ST/screens \
  $ST/runtime $ST/checks
cp evidence/report/REPORT.md $ST/
cp $F $ST/source/$F
git format-patch -q -o $ST/patches $BASE..HEAD
git bundle create -q $ST/fill-eq-query-cont1.bundle fill/eq-query-cont1 ^$BASE
git bundle verify $ST/fill-eq-query-cont1.bundle > $ST/checks/bundle-verify.txt 2>&1
cp evidence/logs/* $ST/logs/
cp "$SWEEP" $ST/checks/final-sweep.log
for f in tail-check.log axioms.out QyAxioms.lean walk.out lint.log probe-gen.txt \
    inspection-table.md inspection-summary.txt inspect-gen.txt inspect.out rule11-grep.txt \
    decls.md screen-diff.txt pairs.md screen-after-323e3588.txt screen-after-323e3588.start \
    screen-diff-323e3588.txt final-sweep-323e3588.log; do
  [ -f "$EV/$f" ] && cp "$EV/$f" $ST/checks/
done
cp "$EV/axioms.out" $ST/checks/axiom-log.txt
for f in QySealed.lean QySealControls.lean sealed.out controls.out sealed-names.txt; do
  cp "$EV/$f" $ST/seal/
done
cp evidence/seal/walk_tail.lean $ST/seal/
cp "$EV/QyImportProbe.lean" "$EV/probe.out" $ST/probe/
cp evidence/screens/* $ST/screens/
if [ -d evidence/dup ] && [ "${WITH_DUP:-0}" = 1 ]; then
  mkdir -p $ST/dup
  for f in names.txt name-hits-all.txt stmt-patterns.tsv stmt-hits.txt QyExactProbe.lean \
      exactq-map.tsv exactq.out exactq-results.tsv dup-table.md; do
    cp evidence/dup/$f $ST/dup/
  done
  cp evidence/logs/dup-fetch.log $ST/dup/ 2>/dev/null || true
fi
cp evidence/runtime/*.py evidence/runtime/*.sh evidence/runtime/*.txt $ST/runtime/
echo "HEAD $(git rev-parse HEAD)" > $ST/checks/head.txt
echo "base $BASE" >> $ST/checks/head.txt
(cd $ST && find . -type f ! -name SHA256SUMS | sort | xargs sha256sum > SHA256SUMS)
OUTDIR=$ROOT/evidence/deliver
mkdir -p $OUTDIR
rm -f $OUTDIR/$NAME.zip
(cd $(dirname $ST) && zip -qr $OUTDIR/$NAME.zip $NAME)
(cd $OUTDIR && sha256sum $NAME.zip > $NAME.zip.sha256)
echo "$OUTDIR/$NAME.zip: $(du -h $OUTDIR/$NAME.zip | cut -f1), $(cd $ST && find . -type f | wc -l) files"
cat $OUTDIR/$NAME.zip.sha256
