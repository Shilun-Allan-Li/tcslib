#!/usr/bin/env bash
# run-checks.sh (fill-bb1-machine): the evidence runs at the fill head, one Lean process at a time:
# (1) native build of the changed modules and everything downstream of them (run-dev-build.sh: runner.py through
#     scripts/lean_check_tree.sh), after backup_cum.py; (2) statements (decls2.py, touched.py); (3) rule10_bb1m.sh
#     collect, seals (strict/coe A/B + paired controls), scan; (4) the axioms probe (runner_full.py, no -o);
#     (5) the scope-request probes: PlProbe/BB1Readers and PlProbe/MachineProbe natively (devcheck, no -o) and
#     MachineProbe under the development seals A and B (devseal.py).
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
E=$SP/dl-review/fill-bb1-machine; W=$SP/wt-fill-bb1-machine; TREE=$SP/dl-oleans; T=$E/tools-used/seal
B=9e7a96481785d6cac4dea3b2e990c49ac278b060; H=$(git -C $W rev-parse HEAD)
export TMPDIR=$SP/bb1m-work/tmp
echo "start $(date -u +%FT%TZ) head $H"
cd $E
python3 -I tools-used/backup_cum.py $TREE tree/snapshot-pre.txt work/q-final.txt $SP/bb1m-work/bk tree
bash run-dev-build.sh work/q-final.txt dev-build/final3
git -C $W diff --name-only $B $H -- 'TCSlib/*.lean' > statements/pr-files.txt
(cd $W && python3 -I $T/decls2.py $W $B $(cat $E/statements/pr-files.txt) > $E/statements/decls2-vs-9e7a9648.txt 2> $E/statements/decls2.err)
python3 -I $T/review/touched.py $W $B $H $E/statements/touched-after.json $(cat $E/statements/pr-files.txt) > $E/statements/touched-after.tsv
echo "statements done $(date -u +%FT%TZ)"
bash $E/rule10_bb1m.sh collect seals scan
mkdir -p $W/Bb1mProbe $E/axioms/runs
cp $E/axioms/Axioms.lean.txt $W/Bb1mProbe/Axioms.lean
echo Bb1mProbe/Axioms > $E/axioms/order.txt
TCSLIB_OLEANS_TREE=$TREE python3 -I $T/runner_full.py $W $E/axioms/order.txt $TREE $E/axioms/runs > $E/axioms/runner.out 2>&1
echo "axioms done $(date -u +%FT%TZ)"
S=$E/scope-request; mkdir -p $S/logs
cd $W
bash $E/tools-used/devcheck.sh $W $TREE PlProbe/BB1Readers.lean > $S/logs/BB1Readers-native.log 2>&1
bash $E/tools-used/devcheck.sh $W $TREE PlProbe/MachineProbe.lean > $S/logs/MachineProbe-native.log 2>&1
for v in A B; do
  python3 -I $SP/bb1m-work/devseal.py PlProbe/MachineProbe.lean PlProbe/MachineProbeSeal$v.lean $v
  cp PlProbe/MachineProbeSeal$v.lean $S/MachineProbeSeal$v.lean.txt
  bash $E/tools-used/devcheck.sh $W $TREE PlProbe/MachineProbeSeal$v.lean > $S/logs/MachineProbe-seal$v.log 2>&1
  rm PlProbe/MachineProbeSeal$v.lean
done
echo "ALL-DONE $(date -u +%FT%TZ)"
