#!/usr/bin/env bash
# run_checkpoint.sh <worktree> <rev> <base-rev> <outdir> <modules-file(dotted)> <controls-spec.json|-> [<title>]
# (gsw-6b-statements sub-agent `seal`, new): every Rule 10 check (brief check 6) of one head in one command.
#   0. guard: every module's source at <rev> (git show) must be byte-identical to the worktree file, because the probes
#      elaborate against the olean tree $TCSLIB_OLEANS (default /home/user/oleans/seal), built from the worktree;
#      the per-module sha256 are written to <outdir>/source-identity.tsv;
#   1. seals A, B, coe-A, coe-B over the full TCSlib import closure (seal_pipeline.sh -> <outdir>/seal/); set
#      SEAL_CHUNK=1000 if a probe overflows; VARIANTS / JOBS / SKIP_COLLECT pass through;
#   2. per-owner seal summary (xr/summarize.py -> <outdir>/seal-summary.tsv);
#   3. notation check (xr/notation_check.py -> <outdir>/notation-check.tsv) over the brief's notation names plus $NOTATION;
#   4. explicit-unfold scan (scan_unfold.py -> <outdir>/unfold/explicit-unfold-scan.txt) and the Lean-resolved
#      supplement (scan_resolve.py -> <outdir>/unfold/scan-resolve.{tsv,log}) over the modules' files;
#   5. paired controls, strict (A) and coe (coe-A) harnesses, pretest unsealed (xr/controls_full.py -> <outdir>/controls/),
#      unless the spec is `-`.
# Every Lean process runs through runner_pool.py (shared pool, lean -DmaxErrors=0, no -o).
set -u
WT=$1; REV=$2; BASE=$3; OUT=$4; MODS=$5; SPEC=$6; TITLE=${7:-"gsw-6b Rule 10 seal $REV"}
H=/home/user/ev/tools/seal
export TCSLIB_OLEANS=${TCSLIB_OLEANS:-/home/user/oleans/seal}
mkdir -p $OUT; OUT=$(cd $OUT && pwd); MODS=$(cd $(dirname $MODS) && pwd)/$(basename $MODS)
FILES=$(sed 's#\.#/#g; s#$#.lean#' $MODS)
: > $OUT/source-identity.tsv
for f in $FILES; do
  a=$(git -C $WT show $REV:$f | sha256sum | cut -d' ' -f1); b=$(sha256sum < $WT/$f | cut -d' ' -f1)
  printf '%s\t%s\t%s\t%s\n' "$f" "$a" "$b" "$([ $a = $b ] && echo identical || echo DIFFERENT)" >> $OUT/source-identity.tsv
  [ $a = $b ] || { echo "source of $f at $REV differs from the worktree; check out $REV and rebuild the tree"; exit 1; }
done
echo "== seals"; bash $H/seal_pipeline.sh $WT $REV $OUT/seal $MODS "$TITLE" $BASE || exit 1
echo "== summary"; python3 -I $H/xr/summarize.py $OUT "rev $REV base $BASE"
G=TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
echo "== notation"; python3 -I $H/xr/notation_check.py $OUT/seal/collect-lines.log $OUT/seal $OUT/notation-check.tsv \
  $G.Parameters.columns $G.Ciphertext $G.PublicKey $G.Secret $G.Coins $G.KeySeed $G.FheView $G.Seeds \
  Complexity.PolyExpr.eval TCSlib.InformationTheory.FinDist.instCoeFunForallReal ${NOTATION:-} | tail -1
echo "== unfold scan"; mkdir -p $OUT/unfold
(cd $WT && python3 -I $H/scan_unfold.py $OUT/seal/collect-lines.log $FILES) > $OUT/unfold/explicit-unfold-scan.txt
tail -1 $OUT/unfold/explicit-unfold-scan.txt
python3 -I $H/scan_resolve.py $WT $OUT/unfold $TCSLIB_OLEANS $FILES > $OUT/unfold/scan-resolve.out 2>&1; head -1 $OUT/unfold/scan-resolve.log
if [ "$SPEC" != "-" ]; then
  echo "== controls"; mkdir -p $OUT/controls; python3 -I $H/xr/controls_full.py $OUT/seal/collect-lines.log $WT $SPEC $OUT/controls $TCSLIB_OLEANS > $OUT/controls/controls.out 2>&1; tail -1 $OUT/controls/summary.tsv
fi
