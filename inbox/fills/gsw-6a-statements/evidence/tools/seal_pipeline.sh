#!/usr/bin/env bash
# seal_pipeline.sh <worktree> <rev> <outdir> <modules-file(dotted)> <title>
# 1. collector (mkcollect.py on the GSW statement phase's collector) compiled through check.py;
# 2. seal probes A (strict), B (SEAL_EVAL=1), coe-A, coe-B by mkseals_ab.py / mkseals_coe.py;
# 3. every probe run with lean -DmaxErrors=0 (runner_lock.py, host lock, no -o);
# 4. sealsum.py per variant against touched.json (made by touched.py beforehand: <outdir>/touched.json).
set -u
WT=$1; REV=$2; OUT=$3; MODS=$4; TITLE=$5
T=/home/user/work/tools/xr
mkdir -p $OUT; cd $WT
SUB=evidence/rule10/probes-$(basename $OUT)
mkdir -p $SUB
if [ -z "${SKIP_COLLECT:-}" ]; then  # SKIP_COLLECT=1 reuses <outdir>/collect-lines.log from an earlier run
python3 -I $T/mkcollect.py $T/CollectTemplate.lean $MODS "$TITLE" $SUB/Collect.lean
cp $SUB/Collect.lean $OUT/Collect.lean
rm -f $OUT/collect.log $OUT/collect.log.summary
python3 -I /home/user/work/tools/check.py $WT $SUB/Collect $OUT/collect.log >/dev/null
grep -E '^(CAT|ROOT|CLOSURE|MODULE|CAT-COUNT)' $OUT/collect.log > $OUT/collect-lines.log
fi
for V in ${VARIANTS:-A B coeA coeB}; do
  case $V in A) S=mkseals_ab.py; E=0;; B) S=mkseals_ab.py; E=1;; coeA) S=mkseals_coe.py; E=0;; coeB) S=mkseals_coe.py; E=1;; esac
  P=Seal${V}_
  rm -rf $SUB/$V; mkdir -p $SUB/$V
  SEAL_EVAL=$E python3 -I $T/$S $T $OUT/collect-lines.log $WT $REV $OUT/seals-$V $SUB/$V $P $(cat $MODS) > $OUT/mkseals-$V.log 2>&1 || { echo "mkseals $V failed"; tail $OUT/mkseals-$V.log; }
  ls $SUB/$V/*.lean | sed 's/\.lean$//' > $OUT/order-$V.txt
  rm -rf $OUT/run-$V
  python3 -I $T/runner_lock.py $WT $OUT/order-$V.txt $WT/.lake/tcslib-check-oleans $OUT/run-$V
  python3 -I $T/sealsum.py $OUT/seals-$V $OUT/run-$V $OUT/touched.json $OUT/seal-$V.tsv
done
