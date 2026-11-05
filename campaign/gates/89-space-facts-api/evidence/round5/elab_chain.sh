#!/usr/bin/env bash
# Gate 89 round 5's elaboration chain: the changed files in dependency order (and the moved lemma's
# unchanged users), compiled with -o into a copy-on-write clone of oleans-lsm4.
# Usage: bash elab_chain.sh <worktree> <clone> <out dir>
WT=$1; O=$2; E=$3
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
echo "# worktree $WT at $(git -C $WT rev-parse HEAD) (+ working tree); clone $O; $(date)" > $E/chain.log
for f in SpaceComplexity/Machines/Bin SpaceComplexity/Codec/Word SpaceComplexity/Codec/Parse SpaceComplexity/Codec/Layout \
  SpaceComplexity/Codec/Layout2 SpaceComplexity/Codec/Deciders SpaceComplexity/Codec/StepDecider \
  SpaceComplexity/Logspace/PathHard SpaceComplexity/Logspace/ISCountGenCorrect SpaceComplexity/WindowClock \
  Randomized/SpaceAmplifyPoly Randomized/BPLInP Randomized/RandomWalkPad ClassP/BinaryArith/PrimeFind \
  ClassPSPACE/TQBFHardParams TuringMachine/CodeSimulator TuringMachine/Build/RecordTable; do
  m=$(echo $f | tr / _)
  ( cd $WT && /usr/bin/time -p bash $S/tools/leanelab-o.sh $WT $O TCSlib/Complexity/$f.lean $O ) > $E/$m.out 2> $E/$m.time
  echo "$f exit=$? lines=$(wc -l < $E/$m.out | tr -d ' ') $(grep real $E/$m.time)" >> $E/chain.log
done
echo "# done $(date)" >> $E/chain.log
