#!/usr/bin/env bash
# Assemble the final delivery: copy the checked seal copies, scan modules, control sources, the
# base copy and the probes into evidence/; refresh patches/ and src/ (payload.sh); check the patch
# reproduction (repro_check.sh); write and verify both manifests (manifest.sh).
set -e
WT=/workspace/canon; D=/workspace/exchange/inbox/fills/canonizer; EV=$D/evidence
for t in fAstrict fAcoe fBstrict fBcoe bAstrict bAcoe bBstrict bBcoe cAstrict cAcoe cBstrict cBcoe; do
  rm -rf $EV/seals/sources/$t; mkdir -p $EV/seals/sources/$t
  cp $WT/lean_proof/dlc/seal/$t/*.lean $EV/seals/sources/$t/
done
for t in final base; do
  rm -rf $EV/scan/sources/$t; mkdir -p $EV/scan/sources/$t
  cp $WT/lean_proof/canon/scan/$t/*.lean $EV/scan/sources/$t/
done
mkdir -p $EV/controls $EV/base $EV/probes
cp $WT/lean_proof/canon/ctl/*.lean $EV/controls/
cp $WT/lean_proof/canon/base/*Base.lean $EV/base/
cp /workspace/canon-work/AxiomsFinal.lean $EV/probes/
bash /workspace/canon-tools/payload.sh > /dev/null
bash /workspace/canon-tools/repro_check.sh $D $EV/logs/final-repro.log | tail -1
bash /workspace/canon-tools/manifest.sh check.sh dev.sh mk.py sweep_chunk.sh census.py cmpcensus.sh \
  pkgcheck.py seal_gen.py seal_run.py seal_all.sh rwids.py rwids_run.sh cmp_scans.py width_check.py \
  final_pipeline.sh payload.sh repro_check.sh manifest.sh finalize.sh
