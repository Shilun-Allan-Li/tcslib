#!/usr/bin/env bash
# seal_pipeline.sh <worktree> <rev> <outdir> <modules-file(dotted)> <title> <base-rev>
# [gsw-6b-statements sub-agent `seal` changes to the gsw-6a-statements seal_pipeline.sh:
#  (1) tools from /home/user/ev/tools/seal/xr (was /home/user/work/tools/xr);
#  (2) probe sources go to <worktree>/evidence-scratch/rule10/probes-<parent of outdir>-<basename outdir>/ (untracked;
#      was evidence/rule10/probes-<basename outdir>);
#  (3) the collector is elaborated by runner_pool.py (lean -DmaxErrors=0, no -o, shared pool) instead of check.py
#      (host lock, lean_check_tree.sh with -o); its log is <outdir>/collect-run/mods/*.log, copied to <outdir>/collect.log;
#      the pipeline stops if the collector's rc is non-zero or a MODULE line is missing;
#  (4) seal probes run through runner_pool.py (shared pool, $JOBS probes submitted at once, default 2) instead of
#      runner_lock.py; the olean tree is $TCSLIB_OLEANS (default /home/user/oleans/seal) instead of the worktree's;
#  (5) touched.json is made here (touched.py <worktree> <base-rev> <rev>) instead of beforehand; a 6th argument <base-rev>;
#  (6) SEAL_CHUNK is passed through to mkseals (unchanged meaning: at most that many rows per harness command).]
# 1. collector (mkcollect.py on the GSW statement phase's collector);
# 2. seal probes A (strict), B (SEAL_EVAL=1), coe-A, coe-B by mkseals_ab.py / mkseals_coe.py;
# 3. every probe run with lean -DmaxErrors=0 (runner_pool.py, shared pool, no -o);
# 4. sealsum.py per variant against touched.json.
set -u
WT=$1; REV=$2; OUT=$3; MODS=$4; TITLE=$5; BASE=$6
T=/home/user/ev/tools/seal/xr
TREE=${TCSLIB_OLEANS:-/home/user/oleans/seal}
mkdir -p $OUT; OUT=$(cd $OUT && pwd); cd $WT
SUB=evidence-scratch/rule10/probes-$(basename $(dirname $OUT))-$(basename $OUT)
mkdir -p $SUB
python3 -I $T/touched.py $WT $BASE $REV $OUT/touched.json $(sed 's#\.#/#g; s#$#.lean#' $MODS) > $OUT/touched.tsv
if [ -z "${SKIP_COLLECT:-}" ]; then  # SKIP_COLLECT=1 reuses <outdir>/collect-lines.log from an earlier run
  python3 -I $T/mkcollect.py $T/CollectTemplate.lean $MODS "$TITLE" $SUB/Collect.lean
  cp $SUB/Collect.lean $OUT/Collect.lean
  rm -rf $OUT/collect-run; echo $SUB/Collect > $OUT/order-collect.txt
  python3 -I $T/runner_pool.py $WT $OUT/order-collect.txt $TREE $OUT/collect-run 1 > $OUT/collect-run.out
  cp $OUT/collect-run/mods/*Collect.log $OUT/collect.log
  grep -E '^(CAT|ROOT|CLOSURE|MODULE|CAT-COUNT)' $OUT/collect.log > $OUT/collect-lines.log
  grep -q '"rc": 0, "errors": 0' $OUT/collect-run/results.jsonl || { echo "collector failed"; cat $OUT/collect-run.out; exit 1; }
  [ "$(grep -c '^MODULE ' $OUT/collect-lines.log)" = "$(grep -c . $MODS)" ] || { echo "collector MODULE lines missing"; exit 1; }
fi
for V in ${VARIANTS:-A B coeA coeB}; do
  case $V in A) S=mkseals_ab.py; E=0;; B) S=mkseals_ab.py; E=1;; coeA) S=mkseals_coe.py; E=0;; coeB) S=mkseals_coe.py; E=1;; esac
  P=Seal${V}_
  rm -rf $SUB/$V $OUT/seals-$V; mkdir -p $SUB/$V
  SEAL_EVAL=$E python3 -I $T/$S $T $OUT/collect-lines.log $WT $REV $OUT/seals-$V $SUB/$V $P $(cat $MODS) > $OUT/mkseals-$V.log 2>&1 || { echo "mkseals $V failed"; tail $OUT/mkseals-$V.log; exit 1; }
  ls $SUB/$V/*.lean | sed 's/\.lean$//' > $OUT/order-$V.txt
  rm -rf $OUT/run-$V
  python3 -I $T/runner_pool.py $WT $OUT/order-$V.txt $TREE $OUT/run-$V ${JOBS:-2} > $OUT/run-$V.out
  python3 -I $T/sealsum.py $OUT/seals-$V $OUT/run-$V $OUT/touched.json $OUT/seal-$V.tsv
done
