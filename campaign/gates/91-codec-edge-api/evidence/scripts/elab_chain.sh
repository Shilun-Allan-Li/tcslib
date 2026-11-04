#!/usr/bin/env bash
# The edge-mode PR's elaboration chain: every Configuration-codec module, in dependency order,
# compiled with -o into a copy-on-write clone of #182's head snapshot (tools/leanelab-o.sh).
# Usage: bash elab_chain.sh <worktree> <olean clone> <out dir>
WT=$1; O=$2; E=$3
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
echo "# worktree $WT at $(git -C $WT rev-parse HEAD); clone $O; $(date)" > $E/chain.log
for m in Word Scan Valid Step Langs Checks Bridge Engine Regs Machine Run Parse Layout Deciders Layout2 StepDecider; do
  f=TCSlib/Complexity/SpaceComplexity/Codec/$m.lean
  ( cd $WT && /usr/bin/time -p bash $S/tools/leanelab-o.sh $WT $O $f $O ) > $E/$m.out 2> $E/$m.time
  echo "$m exit=$? lines=$(wc -l < $E/$m.out | tr -d ' ') $(grep real $E/$m.time)" >> $E/chain.log
done
echo "# done $(date)" >> $E/chain.log
