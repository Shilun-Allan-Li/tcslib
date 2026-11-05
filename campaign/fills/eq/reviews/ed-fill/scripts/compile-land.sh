#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
cd $R
for m in "$@"; do
  f=TCSlib/Complexity/$m.lean; tag=$(echo $m | tr '/' '_')
  /usr/bin/time -l bash $S/tools/leanelab-o.sh $R/wt-land $R/oleans-land $f $R/oleans-land > out/32-land-compile-$tag.out 2> out/32-land-compile-$tag.time
  echo "exit=$?" >> out/32-land-compile-$tag.time
done
/usr/bin/time -l bash $S/tools/leanelab.sh $R/wt-land $R/oleans-land $R/probe/DzAuditR2.lean > out/33-land-audit.out 2> out/33-land-audit.time; echo "exit=$?" >> out/33-land-audit.time
/usr/bin/time -l bash $S/tools/leanelab.sh $R/wt-land $R/oleans-land $R/probe/DzHierAx.lean > out/33-land-hier-ax.out 2> out/33-land-hier-ax.time; echo "exit=$?" >> out/33-land-hier-ax.time
/usr/bin/time -l bash $S/tools/leanelab.sh $R/wt-head $R/oleans-clone $R/probe/seal-land/NTimeDiagonalizer_sealed.lean > out/34-land-seal-sealed.out 2> out/34-land-seal-sealed.time; echo "exit=$?" >> out/34-land-seal-sealed.time
