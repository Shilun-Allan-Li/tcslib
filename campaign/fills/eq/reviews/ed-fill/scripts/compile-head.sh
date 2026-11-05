#!/usr/bin/env bash
# Compile the head's owned file into the clone, then its downstream modules, timing each.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad; R=$S/review/ed-fill
cd $R
for m in "$@"; do
  f=TCSlib/Complexity/$m.lean; tag=$(echo $m | tr '/' '_')
  /usr/bin/time -l bash $S/tools/leanelab-o.sh $R/wt-head $R/oleans-clone $f $R/oleans-clone > out/10-compile-$tag.out 2> out/10-compile-$tag.time
  echo "exit=$?" >> out/10-compile-$tag.time
done
