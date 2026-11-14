#!/usr/bin/env bash
# Final evidence runs after the final sweep, one Lean process at a time (each step skips work
# already recorded, so the pipeline can be resumed after a host restart).
set -u
WT=/workspace/ett; T=/workspace/ett-tools
EV=/workspace/exchange/inbox/fills/cca2-ett/evidence; LG=$EV/logs; SL=$EV/seals; SC=$EV/scan
mkdir -p $SL $SC
cd $WT
step() { echo "=== $(date -u +%FT%TZ) $*" | tee -a $LG/final-pipeline.log; }
# 1. census and lint (no Lean)
step census
python3 $T/census.py $LG/final-sweep.log > $LG/final-census.txt
( diff <(sed 's|^TCSlib/Complexity/||' $LG/final-census.txt | sort) \
       <(sed 's|^TCSlib/Complexity/||' /workspace/ett-pack/base-sorries.txt | sort); echo "diff exit=$?" ) \
  > $LG/final-census-vs-base.diff
step lint
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b \
  > $LG/final-lint.log 2>&1; echo "lint exit=$?" >> $LG/final-lint.log
# 2. axioms of the target and of every stored constant of the changed and new files
if ! grep -q "TOTAL" $LG/final-axioms.log 2>/dev/null; then
  step axioms
  mkdir -p lean_proof/ett/probes; cp /workspace/ett-work/probes/AxiomsFinal.lean lean_proof/ett/probes/
  $T/check.sh lean_proof/ett/probes/AxiomsFinal $LG/final-axioms.log
fi
# 3. whole-file seals A (PolyExpr.eval excluded) and B (sealed), final
step seals-final-A; $T/seal_all.sh finalA $SL/final-A.jsonl --eval-open
step seals-final-B; $T/seal_all.sh finalB $SL/final-B.jsonl
# 4. the same at the base (the owned file is the only changed file that exists at the base)
B=lean_proof/ett/base/EncryptThenTagBase.lean; O=TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean
grep -q '"file"' $SL/base-A.jsonl 2>/dev/null || { step seals-base-A; python3 $T/seal_run.py $WT baseA $SL/base-A.jsonl --eval-open --as=$O $B; }
grep -q '"file"' $SL/base-B.jsonl 2>/dev/null || { step seals-base-B; python3 $T/seal_run.py $WT baseB $SL/base-B.jsonl --as=$O $B; }
# 5. paired controls: unsealed checks, then sealed A and B
if ! grep -q "CtlReader" $LG/controls-plain.log 2>/dev/null; then
  step controls-plain
  for c in CtlUnfold CtlEval CtlReader; do $T/check.sh lean_proof/ett/ctl/$c $LG/controls-plain.log; done
fi
for v in A B; do
  for c in CtlUnfold CtlEval CtlReader; do
    grep -q "$c" $SL/controls-$v.jsonl 2>/dev/null && continue
    step controls-$v $c
    if [ $v = A ]; then python3 $T/seal_run.py $WT ctl$v $SL/controls-$v.jsonl --eval-open lean_proof/ett/ctl/$c.lean
    else python3 $T/seal_run.py $WT ctl$v $SL/controls-$v.jsonl lean_proof/ett/ctl/$c.lean; fi
  done
done
# 6. explicit-unfold scan, final and base
if [ ! -s $SC/scan-final.tsv ]; then
  step scan-final
  rm -rf lean_proof/ett/scan/final; mkdir -p lean_proof/ett/scan/final
  for f in $(sed -n 's/^\(TCSlib[^ ]*\)$/\1/p' <<'LIST'
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Tools.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Machines.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Games.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Handler.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Transfer.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Forgery.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Lazy.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAHandler.lean
TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/CPAReduction.lean
LIST
); do
    n=$(echo ${f%.lean} | sed 's|TCSlib/Cryptography/||; s|/|_|g')
    python3 $T/rwids.py $WT $f lean_proof/ett/scan/final/$n >> $LG/scan-final.ids.log
  done
  $T/rwids_run.sh $WT lean_proof/ett/scan/final $LG/scan-final.raw.log $SC/scan-final.tsv
fi
if [ ! -s $SC/scan-base.tsv ]; then
  step scan-base
  $T/check.sh lean_proof/ett/base/EncryptThenTagBase $LG/scan-base.raw.log
  rm -rf lean_proof/ett/scan/base; mkdir -p lean_proof/ett/scan/base
  python3 $T/rwids.py $WT $B lean_proof/ett/scan/base/Encryption_PrivateKey_EncryptThenTag >> $LG/scan-base.ids.log
  $T/rwids_run.sh $WT lean_proof/ett/scan/base $LG/scan-base.raw.log $SC/scan-base.tsv
fi
# 7. comparisons
step compare
{ echo "## seals A (PolyExpr.eval excluded)"; python3 $T/cmp_scans.py seals $SL/final-A.jsonl $SL/base-A.jsonl
  echo; echo "## seals B (PolyExpr.eval sealed)"; python3 $T/cmp_scans.py seals $SL/final-B.jsonl $SL/base-B.jsonl; } > $SL/seals-compare.log 2>&1
python3 $T/cmp_scans.py rwids $SC/scan-final.tsv $SC/scan-base.tsv > $SC/scan-compare.log 2>&1
step PIPELINE-DONE
