#!/usr/bin/env bash
# After phase_final: the base tree's Foundations facade (not in order.txt), then the extended base
# declaration dump and the facade's explicit-unfold scan at the base.
set -u
L=/workspace/exchange/inbox/fills/dl-consolidation/evidence/logs
B=/workspace/dlc-base
while ! grep -q "PHASE FINAL DONE" /workspace/dlc-work/phase_final.out 2>/dev/null; do sleep 30; done
WT=$B /workspace/dlc-tools/check.sh TCSlib/Cryptography/Foundations $L/base-tree-facade.log
rm -f $L/decl-dump-base-ext.log
WT=$B /workspace/dlc-tools/check.sh lean_proof/dlc/DeclDumpBase $L/decl-dump-base-ext.log
WT=$B /workspace/dlc-tools/check.sh lean_proof/dlc/rwids/base/Foundations $L/rwids-base-facade.log
echo "PHASE POST DONE $(date -u +%FT%TZ)"
