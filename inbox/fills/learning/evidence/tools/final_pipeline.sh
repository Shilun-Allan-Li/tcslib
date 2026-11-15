#!/usr/bin/env bash
# Final evidence runs after the final sweep, one Lean process at a time. Each step skips work
# already recorded, so the pipeline can be resumed after a host restart.
set -u
WT=/workspace/learn; T=/workspace/learn-tools; BASE=107f1e8c218733eac12d6b9bee6fece441271317
EV=/workspace/exchange/inbox/fills/learning/evidence; LG=$EV/logs; SL=$EV/seals; SC=$EV/scan
mkdir -p $SL $SC
cd $WT
step() { echo "=== $(date -u +%FT%TZ) $*" | tee -a $LG/final-pipeline.log; }
FILES="TCSlib/Cryptography/Randomness/Learning.lean TCSlib/Cryptography/Randomness/Learning/Sample.lean TCSlib/Cryptography/Randomness/Learning/Distinguisher.lean TCSlib/Cryptography/Randomness/Learning/Law.lean TCSlib/Cryptography/Randomness/Learning/Random.lean"
# 1. census, lint, width (no Lean)
step census
python3 -I $T/census.py $LG/final-sweep.log HEAD > $LG/final-census.txt
bash $T/cmpcensus.sh $LG/final-census.txt > $LG/final-census-vs-base.diff
step lint
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b > $LG/final-lint.log 2>&1
echo "lint exit=$?" >> $LG/final-lint.log
{ echo "# FAIL/WARN line sets: base-lint.log vs final-lint.log (< base only, > final only)"
  diff <(grep -E '^(FAIL|WARN)' $LG/base-lint.log | sort) <(grep -E '^(FAIL|WARN)' $LG/final-lint.log | sort)
  echo "diff exit=$?"; } > $LG/final-lint-vs-base.diff
step width
python3 -I $T/width_check.py $WT $FILES > $LG/final-width.log
# 2. axioms
if ! grep -q "^TOTAL" $LG/final-axioms.log 2>/dev/null; then
  step axioms
  mkdir -p lean_proof/learn/probes; cp /workspace/learn-work/probes/AxiomsFinal.lean lean_proof/learn/probes/
  rm -f $LG/final-axioms.log
  $T/check.sh lean_proof/learn/probes/AxiomsFinal $LG/final-axioms.log
fi
# 3. seals: final and base, A/B x strict/coe
for v in A-strict A-coe B-strict B-coe; do
  flags=""; case $v in A-*) flags="--eval-open";; esac; case $v in *-coe) flags="$flags --coe-open";; esac
  tag=$(echo "f$v" | tr -d '-')
  step seals-final-$v; $T/seal_all.sh $tag $SL/final-$v.jsonl $flags
  if ! grep -q '"file"' $SL/base-$v.jsonl 2>/dev/null; then
    step seals-base-$v
    python3 -I $T/seal_run.py $WT $(echo "b$v" | tr -d '-') $SL/base-$v.jsonl $flags \
      --as=TCSlib/Cryptography/Randomness/Learning.lean lean_proof/learn/base/LearningBase.lean
  fi
done
# 4. paired controls: unsealed, then sealed in the four variants
if ! grep -q "CtlReader" $LG/controls-plain.log 2>/dev/null; then
  step controls-plain
  for c in CtlUnfold CtlEval CtlCoe CtlReader; do $T/check.sh lean_proof/learn/ctl/$c $LG/controls-plain.log; done
fi
for v in A-strict A-coe B-strict B-coe; do
  flags=""; case $v in A-*) flags="--eval-open";; esac; case $v in *-coe) flags="$flags --coe-open";; esac
  for c in CtlUnfold CtlEval CtlCoe CtlReader; do
    grep -q "$c" $SL/controls-$v.jsonl 2>/dev/null && continue
    step controls-$v $c
    python3 -I $T/seal_run.py $WT $(echo "c$v" | tr -d '-') $SL/controls-$v.jsonl $flags lean_proof/learn/ctl/$c.lean
  done
done
# 5. explicit-unfold scan, final and base
if [ ! -s $SC/scan-final.tsv ]; then
  step scan-final
  rm -rf lean_proof/learn/scan/final; mkdir -p lean_proof/learn/scan/final
  for f in $FILES; do
    n=$(echo ${f%.lean} | sed 's|TCSlib/Cryptography/||; s|/|_|g')
    python3 -I $T/rwids.py $WT $f lean_proof/learn/scan/final/$n >> $LG/scan-final.ids.log
  done
  $T/rwids_run.sh $WT lean_proof/learn/scan/final $LG/scan-final.raw.log $SC/scan-final.tsv
fi
if [ ! -s $SC/scan-base.tsv ]; then
  step scan-base
  $T/check.sh lean_proof/learn/base/LearningBase $LG/scan-base.raw.log
  rm -rf lean_proof/learn/scan/base; mkdir -p lean_proof/learn/scan/base
  python3 -I $T/rwids.py $WT lean_proof/learn/base/LearningBase.lean lean_proof/learn/scan/base/Randomness_Learning >> $LG/scan-base.ids.log
  $T/rwids_run.sh $WT lean_proof/learn/scan/base $LG/scan-base.raw.log $SC/scan-base.tsv
fi
# 6. comparisons
step compare
{ for v in A-strict A-coe B-strict B-coe; do
    echo "## variant $v: final vs base"; python3 -I $T/cmp_scans.py seals $SL/final-$v.jsonl $SL/base-$v.jsonl; echo
  done
  for e in A B; do
    echo "## strict vs coe, variant $e, final (failing declarations that differ)"
    python3 -I $T/cmp_scans.py seals $SL/final-$e-strict.jsonl $SL/final-$e-coe.jsonl; echo
  done; } > $SL/seals-compare.log 2>&1
python3 -I $T/cmp_scans.py rwids $SC/scan-final.tsv $SC/scan-base.tsv > $SC/scan-compare.log 2>&1
step PIPELINE-DONE
