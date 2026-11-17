#!/usr/bin/env bash
# rule10_s1.sh <head|base> <olean-tree> <outdir>      (cleanup-stage1; adapted from DW-5's rule10_dw5.sh
# and rule10_b.sh, which are kept unmodified under seal/)
# Differences from DW-5: the owners are Stage 1's (head: the 17 changed owners and the 2 new modules;
# base: the 17 changed owners at the check base 2081fe57..., tree 01cc6259...); the worktree is the lead
# clone /home/user/s1/tcslib (probes under <prefix>/, untracked); the controls generator is mkctl_s1.py
# (own-and-closure seal per owner; controls-spec.json), run in strict and coe variants (head only); the
# seal-control queue runs through seal/runner_full.py (lean -DmaxErrors=0, no -o; host-wide Lean lock).
# Seal generators mkseals_ab.py / mkseals_coe.py, the collector template, sealsum.py, ctlcheck2.py,
# touched.py and the scan tools are DW-5's copies, unmodified.
# Correction (2026-11-17, after the first base run): scan1_g40.py reads the sources from its worktree,
# so in base mode the explicit-unfold scan runs in a worktree at the check base (SW=/home/user/s1/wt-base);
# the first base run had scanned the clone (head sources) and is kept as base/scan-invalid-headsources/.
set -u
MODE=$1; TREE=$2; OUT=$3
W=/home/user/s1/tcslib; TL=/home/user/s1/evidence/tools; T=$TL/seal; G=$T/review/archived-gate10-tools
ISSUE=daa6e173cdd94cad1475b9a96eca613bce53ba61; CBASE=2081fe57475138297fff6a5144d31b91d7f27706
export PATH=$HOME/.elan/bin:$PATH
OWN17="TCSlib.Complexity.Randomized.Build.IterateFindHost TCSlib.Complexity.Randomized.PPT
 TCSlib.Cryptography.Asymptotic.Adversary TCSlib.Cryptography.Asymptotic.Sampling
 TCSlib.Cryptography.Authentication.Encoding TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
 TCSlib.Cryptography.Encryption.PublicKey.Trapdoor TCSlib.Cryptography.Foundations.BitLists
 TCSlib.Cryptography.Games.Bridges.Experiments TCSlib.Cryptography.Games.Efficiency.Strings
 TCSlib.Cryptography.Games.Machines TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
 TCSlib.Cryptography.ZeroKnowledge.EncodingMachines TCSlib.Cryptography.ZeroKnowledge.Interaction
 TCSlib.InformationTheory.Entropy TCSlib.InformationTheory.FinDist TCSlib.InformationTheory.Samples"
if [ "$MODE" = head ]; then
  REV=$(git -C $W rev-parse HEAD); P=S1R10H
  OWNERS="$OWN17 TCSlib.Cryptography.Games.Tapes TCSlib.Cryptography.ZeroKnowledge.InteractionWords"
else
  REV=$CBASE; P=S1R10B; OWNERS="$OWN17"
fi
mkdir -p $OUT/order $OUT/probe-sources $OUT/statements
echo "start $(date -u +%FT%TZ) mode=$MODE rev=$REV tree=$TREE"
test -z "$(git -C $W status --porcelain --untracked-files=no)" || { echo "lead clone not clean"; exit 1; }
rm -rf $W/$P; mkdir -p $W/$P
# 1. collector
printf '%s\n' $OWNERS > $OUT/order/owners.txt
python3 -I $T/review/mkcollect.py $T/review/NmCollect.template.lean $OUT/order/owners.txt \
  "cleanup-stage1 collector ($MODE)" $W/$P/Collect.lean
cp $W/$P/Collect.lean $OUT/probe-sources/Collect.lean.txt
echo $P/Collect > $OUT/order/collect.txt
python3 -I $T/runner_full.py $W $OUT/order/collect.txt $TREE $OUT/collect-runs > $OUT/collect-runner.out 2>&1
LOG=$OUT/collect-runs/mods/${P}_Collect.log
grep -q '^CAT-COUNT' $LOG || { echo "collector failed"; tail -20 $LOG; exit 1; }
echo "collector $(date -u +%FT%TZ)"
# 2. seals: strict (A, B) and coe (A, B)
python3 -I $T/review/mkseals_ab.py $G $LOG $W $REV $OUT/seals/A $P/S SealA_ $OWNERS > $OUT/mkseals-A.log
SEAL_EVAL=1 python3 -I $T/review/mkseals_ab.py $G $LOG $W $REV $OUT/seals/B $P/S SealB_ $OWNERS > $OUT/mkseals-B.log
python3 -I $T/review/mkseals_coe.py $G $LOG $W $REV $OUT/seals-coe/A $P/C SealA_ $OWNERS > $OUT/mkseals-coe-A.log
SEAL_EVAL=1 python3 -I $T/review/mkseals_coe.py $G $LOG $W $REV $OUT/seals-coe/B $P/C SealB_ $OWNERS > $OUT/mkseals-coe-B.log
# 3. paired controls (head only)
if [ "$MODE" = head ]; then
  python3 -I $TL/mkctl_s1.py $G $LOG $TL/controls-spec.json $W $P/KS $OUT/controls-strict strict > $OUT/mkctl-strict.log
  python3 -I $TL/mkctl_s1.py $G $LOG $TL/controls-spec.json $W $P/K $OUT/controls-coe coe > $OUT/mkctl-coe.log
fi
(cd $W && ls $P/C/*.lean $P/K/*.lean $P/KS/*.lean $P/S/*.lean 2>/dev/null | sed 's/\.lean$//' | LC_ALL=C sort) \
  > $OUT/order/seal-control-queue.txt
echo "queue $(wc -l < $OUT/order/seal-control-queue.txt) probes $(date -u +%FT%TZ)"
python3 -I $T/runner_full.py $W $OUT/order/seal-control-queue.txt $TREE $OUT/seal-runs > $OUT/seal-runner.out 2>&1 || true
# 4. summaries
FILES=$(printf '%s\n' $OWNERS | sed 's|\.|/|g; s|$|.lean|')
if [ "$MODE" = head ]; then TB=$ISSUE; else TB=$REV; fi
python3 -I $T/review/touched.py $W $TB $REV $OUT/statements/touched.json $FILES > $OUT/statements/touched.tsv
TJ=$OUT/statements/touched.json
for v in A B; do
  python3 -I $T/review/sealsum.py $OUT/seals/$v $OUT/seal-runs $TJ $OUT/seals-$v.tsv
  python3 -I $T/review/sealsum.py $OUT/seals-coe/$v $OUT/seal-runs $TJ $OUT/seals-coe-$v.tsv
done
if [ "$MODE" = head ]; then
  python3 -I $T/review/ctlcheck2.py $OUT/controls-strict/controls-plan.json $OUT/seal-runs $OUT/ctlcheck-strict.json > $OUT/ctlcheck-strict.log || true
  python3 -I $T/review/ctlcheck2.py $OUT/controls-coe/controls-plan.json $OUT/seal-runs $OUT/ctlcheck-coe.json > $OUT/ctlcheck-coe.log || true
fi
# 5. explicit-unfold scan over the owners' files (sources read from SW)
SW=$W; [ "$MODE" = base ] && SW=/home/user/s1/wt-base && mkdir -p $SW/$P
mkdir -p $OUT/scan
SCAN_IMPORTS="$OWNERS" python3 -I $T/scan1_g40.py $G/scan_explicit.py $SW $TJ $OUT/scan/items.json \
  $SW/$P/ScanKinds.lean $FILES > $OUT/scan/scan1.out 2>&1
cp $SW/$P/ScanKinds.lean $OUT/probe-sources/ScanKinds.lean.txt
echo $P/ScanKinds > $OUT/order/scan.txt
python3 -I $T/runner_full.py $SW $OUT/order/scan.txt $TREE $OUT/scan/runs > $OUT/scan/scan-runner.out 2>&1
python3 -I $T/scan2.py $OUT/scan/items.json $OUT/scan/runs/mods/${P}_ScanKinds.log $OUT/scan/explicit.json \
  > $OUT/scan/scan2.log 2>&1
for f in $OUT/probe-sources; do :; done
cp -r $W/$P $OUT/probe-tree
cat $OUT/mkseals-*.log $OUT/mkctl-*.log 2>/dev/null; cat $OUT/seals-*.tsv
tail -n 1 $OUT/ctlcheck-strict.log $OUT/ctlcheck-coe.log 2>/dev/null
echo "PHASE-DONE $(date -u +%FT%TZ)"
