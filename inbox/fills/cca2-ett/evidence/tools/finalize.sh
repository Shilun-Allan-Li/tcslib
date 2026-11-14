#!/usr/bin/env bash
# Assemble the final delivery: copy the generated seal copies, scan modules, control sources,
# the base copy, the probe and the tools into evidence/, refresh patches/ and src/ (payload.sh),
# and write evidence/SHA256SUMS over exactly the delivered evidence files.
set -e
WT=/workspace/ett; D=/workspace/exchange/inbox/fills/cca2-ett; EV=$D/evidence
for t in finalA finalB baseA baseB ctlA ctlB; do
  rm -rf $EV/seals/sources/$t; mkdir -p $EV/seals/sources/$t
  cp $WT/lean_proof/dlc/seal/$t/*.lean $EV/seals/sources/$t/
done
for t in final base; do
  rm -rf $EV/scan/sources/$t; mkdir -p $EV/scan/sources/$t
  cp $WT/lean_proof/ett/scan/$t/*.lean $EV/scan/sources/$t/
done
mkdir -p $EV/controls $EV/base $EV/probes $EV/tools
cp $WT/lean_proof/ett/ctl/*.lean $EV/controls/
cp $WT/lean_proof/ett/base/EncryptThenTagBase.lean $EV/base/
cp /workspace/ett-work/probes/AxiomsFinal.lean $EV/probes/
for f in check.sh dev.sh mk.py sweep_chunk.sh census.py cmpcensus.sh pkgcheck.py payload.sh \
         seal_gen.py seal_run.py seal_all.sh rwids.py rwids_run.sh cmp_scans.py final_pipeline.sh finalize.sh; do
  cp /workspace/ett-tools/$f $EV/tools/
done
bash /workspace/ett-tools/payload.sh > /dev/null
cd $EV && find . -type f ! -name SHA256SUMS | sort | xargs sha256sum > SHA256SUMS
echo "evidence files: $(grep -c '' SHA256SUMS)"
