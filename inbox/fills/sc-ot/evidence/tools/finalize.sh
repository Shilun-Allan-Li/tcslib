#!/usr/bin/env bash
# Assemble the final delivery: copy the checked seal copies, scan modules, control sources, the
# base copy and the probes into evidence/; refresh patches/ and src/ (payload.sh); check the patch
# reproduction (repro_check.sh); write and verify both manifests (manifest.sh).
set -e
WT=/workspace/scot; D=/workspace/exchange/inbox/fills/sc-ot; EV=$D/evidence
for t in fAstrict fAcoe fBstrict fBcoe bAstrict bAcoe bBstrict bBcoe cAstrict cAcoe cBstrict cBcoe; do
  rm -rf $EV/seals/sources/$t; mkdir -p $EV/seals/sources/$t
  cp $WT/lean_proof/dlc/seal/$t/*.lean $EV/seals/sources/$t/
done
for t in final base; do
  rm -rf $EV/scan/sources/$t; mkdir -p $EV/scan/sources/$t
  cp $WT/lean_proof/scot/scan/$t/*.lean $EV/scan/sources/$t/
done
mkdir -p $EV/controls $EV/base $EV/probes
cp $WT/lean_proof/scot/ctl/*.lean $EV/controls/
cp $WT/lean_proof/scot/base/*Base.lean $EV/base/
cp /workspace/scot-work/AxiomsFinal.lean $EV/probes/
bash /workspace/scot-tools/payload.sh > /dev/null
bash /workspace/scot-tools/repro_check.sh $D $EV/logs/final-repro.log | tail -1
bash /workspace/scot-tools/manifest.sh check.sh dev.sh devall.sh sweep_chunk.sh census.py cmpcensus.sh \
  pkgcheck.py seal_gen.py seal_run.py seal_all.sh seal_cp1.sh seal_cp1b.sh cp2_checks.sh rwids.py \
  rwids_run.sh cmp_scans.py width_check.py run_final.sh final_pipeline.sh payload.sh repro_check.sh \
  manifest.sh finalize.sh
