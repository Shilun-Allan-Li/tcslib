#!/usr/bin/env bash
# run-scope-min.sh (fill-bb1-machine): the minimal scope request. Build PlProbe/BB1ReadersMin (the seven readers, proved
# by unfolding as the owners would) on dl-oleans through scripts/lean_check_tree.sh (runner.py; its olean is removed by
# the restore with the rest of PlProbe/), then elaborate PlProbe/MachineProbeMin (the T4 proof on the seven readers and
# published readers only) natively and under the development seals A and B (devseal.py), without -o.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
E=$SP/dl-review/fill-bb1-machine; W=$SP/wt-fill-bb1-machine; TREE=$SP/dl-oleans; S=$E/scope-request
export TMPDIR=$SP/bb1m-work/tmp
mkdir -p $S/logs
echo PlProbe/BB1ReadersMin > $E/work/q-scope-min.txt
cd $E
python3 -I tools-used/backup_cum.py $TREE tree/snapshot-pre.txt work/q-scope-min.txt $SP/bb1m-work/bk tree
bash run-dev-build.sh work/q-scope-min.txt dev-build/scope-min
cd $W
bash $E/tools-used/devcheck.sh $W $TREE PlProbe/MachineProbeMin.lean > $S/logs/MachineProbeMin-native.log 2>&1
for v in A B; do
  python3 -I $SP/bb1m-work/devseal.py PlProbe/MachineProbeMin.lean PlProbe/MachineProbeMinSeal$v.lean $v
  cp PlProbe/MachineProbeMinSeal$v.lean $S/MachineProbeMinSeal$v.lean.txt
  bash $E/tools-used/devcheck.sh $W $TREE PlProbe/MachineProbeMinSeal$v.lean > $S/logs/MachineProbeMin-seal$v.log 2>&1
  rm PlProbe/MachineProbeMinSeal$v.lean
done
echo "SCOPE-MIN-DONE $(date -u +%FT%TZ)"
