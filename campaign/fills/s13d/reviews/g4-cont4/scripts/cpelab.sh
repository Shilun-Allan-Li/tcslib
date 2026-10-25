#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/g4-cont4
for c in b5247d00 478124e9 7fbf3c2e 604d9404 f771d4ff 06872fff; do
  bash $R/scripts/elab.sh $R/wt-work $S/oleans-lphl2 G4C4RevCp_$c.lean $R/out/30-cp-$c-elab.out
done
