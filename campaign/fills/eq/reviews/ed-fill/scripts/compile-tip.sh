#!/usr/bin/env bash
# Pre-check of the landing replay: the landed file and its downstream compiled against a clone of
# oleans-lsm5 (the Lean of the campaign tip after #181, d1ddea26 = 98912ab2 in .lean files).
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
cd $R
for m in Diagonalization/NTimeDiagonalizer Diagonalization/NTimeHierarchy Diagonalization; do
  f=TCSlib/Complexity/$m.lean; tag=$(echo $m | tr '/' '_')
  /usr/bin/time -l bash $S/tools/leanelab-o.sh $R/wt-land $R/oleans-tipclone $f $R/oleans-tipclone > out/40-tip-compile-$tag.out 2> out/40-tip-compile-$tag.time
  echo "exit=$?" >> out/40-tip-compile-$tag.time
done
/usr/bin/time -l bash $S/tools/leanelab.sh $R/wt-land $R/oleans-tipclone $R/probe/DzHierAx.lean > out/40-tip-hier-ax.out 2> out/40-tip-hier-ax.time; echo "exit=$?" >> out/40-tip-hier-ax.time
