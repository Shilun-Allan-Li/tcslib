#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/g4-cont4
bash $R/scripts/elab.sh $R/wt-tip2 $S/oleans-lu2api TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean $R/out/37-elab-newtip-lu2api.out
bash $R/scripts/elab.sh $R/wt-tip2 $S/oleans-lu2api G4C4RevLand_ZoneRebalance.lean $R/out/37b-elab-land-newtip-lu2api.out
