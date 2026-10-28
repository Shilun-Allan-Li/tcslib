#!/bin/bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/eq-cont1-fill; W=$R/wt-head; OL=$S/oleans-lhh
bash $R/scripts/elab.sh $W $OL $R/probe/land/NTimeDiagonalizer.lean $R/out/26-land-lhh
bash $R/scripts/elab.sh $W $OL $R/probe/land/AuditLand.lean $R/out/28-land-audit
bash $R/scripts/elab.sh $W $OL $R/probe/land/Seal3_sealed.lean $R/out/27-land-seal-sealed
bash $R/scripts/elab.sh $W $OL $R/probe/land/Seal3_unsealed.lean $R/out/27-land-seal-unsealed
