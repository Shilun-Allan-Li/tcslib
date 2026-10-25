#!/usr/bin/env bash
# Re-run the drafter's probe records, one at a time, in this order.
for p in a1/A1ApiProbe eq/EQSealControl scp/SCPSealControl scp/SCPImportProbe scp/SCPRouteProbe scp/SCPDupProbe scp/SavitchOverlay eq/EQImportProbe eq/EQRouteProbe eq/EQDupProbe eq/NTimeDiagonalizerOverlay ed/EDImportProbe; do
  echo "$p: $(bash /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/megafill-d/scripts/runprobe.sh /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/wt-hk/campaign/fills/megafill/drafts/megafill-D-triage-fe666d60/$p.lean.txt)"
done
