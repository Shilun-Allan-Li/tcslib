#!/usr/bin/env bash
# Final checks of dl-folds after the full sweep, one Lean process at a time (for nohup use).
set -u
export PATH=$HOME/.elan/bin:$PATH
F=/workspace/folds; E=/workspace/foldpay/evidence/final; T=/workspace/foldtools
LOG=$E/final-checks.log
cd $F
LP=$F/.lake/tcslib-check-oleans; for d in $F/.lake/packages/*/.lake/build/lib/lean; do LP=$LP:$d; done
mkdir -p $E/census $E/axioms $E/controls $E/rwids
echo "$(date -u +%FT%TZ) census" >> $LOG
python3 $T/gen_census.py $E/order-final.txt >> $LOG 2>&1
cp scratch/census/Census.lean /workspace/foldpay/evidence/tools/census/Census-final.lean
LEAN_PATH=$LP lean scratch/census/Census.lean > $E/census/census-final.log 2>&1; echo "census exit $?" >> $LOG
echo "$(date -u +%FT%TZ) axioms" >> $LOG
python3 $T/gen_axioms.py $E/order-final.txt /workspace/foldpay/evidence/cp3/changed-modules.txt >> $LOG 2>&1
cp scratch/census/AxFinal.lean /workspace/foldpay/evidence/tools/census/AxFinal.lean
LEAN_PATH=$LP lean scratch/census/AxFinal.lean > $E/axioms/axioms-final.log 2>&1; echo "axioms exit $?" >> $LOG
echo "$(date -u +%FT%TZ) controls" >> $LOG
python3 $T/controls.py $E/controls >> $LOG 2>&1
echo "$(date -u +%FT%TZ) rwids" >> $LOG
python3 $T/rwids_run.py $E/changed-files.txt $E/rwids >> $LOG 2>&1
echo "$(date -u +%FT%TZ) seals" >> $LOG
for i in $(seq 1 40); do
  out=$(python3 $T/seal.py final $(python3 -c "
import sys; sys.path.insert(0,'$T')
from files import SUPER
print(' '.join(SUPER + ['TCSlib/Cryptography/Games/Forwarding.lean']))") 2>&1 | tail -1)
  echo "$(date -u +%FT%TZ) seal $out" >> $LOG
  case "$out" in PAUSE*) ;; *) break ;; esac
done
echo "$(date -u +%FT%TZ) END" >> $LOG
