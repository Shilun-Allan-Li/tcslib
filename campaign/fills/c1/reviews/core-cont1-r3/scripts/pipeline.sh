#!/usr/bin/env bash
# Rebuild the verified overlay from the repaired copy, then elaborate it, its axiom probe, and the
# three seal variants, one elaboration at a time. usage: pipeline.sh <tag>
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/c1-core-cont1-r3; I=$S/wt-hk/campaign/fills/c1/inputs/c1-fill-core-cont1
F=TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean; T=$1
cd $R/scripts || exit 1
python3 -I mkoverlay.py $I/NDCodeSimulatorOverlay.lean.txt $R/wt-repair/$F $R/out/overlay-verified.lean.txt
cp $R/out/overlay-verified.lean.txt $R/wt-ovl/$F
bash elab.sh $R/wt-ovl $S/oleans-lseam2 $F $R/out/$T-elab-overlay-verified-lseam2.out
names=$(sed 's/^/Turing./' privnames.txt | paste -sd, -)
python3 -I mkax.py $R/wt-ovl/$F $R/probe/AxOverlayVerified.lean "$names" "Turing.exists_ndInterpreterCore,Turing.exists_replayCanonizer,Turing.CodeNDTM.serialize_eq_tableBitsK,$names" >/dev/null
cp $R/probe/AxOverlayVerified.lean $R/wt-ovl/ReviewProbe/
bash elab.sh $R/wt-ovl $S/oleans-lseam2 ReviewProbe/AxOverlayVerified.lean $R/out/$T-ax-overlay-verified.out
for v in "Seal 1 1 0" "SealControl 1 1 1" "ControlUnsealed 0 0 1"; do
  set -- $v
  python3 -I mkseal2.py $R/wt-ovl/$F $R/probe/IC$1.lean $2 $3 $4 $R/out/11-seal-set.txt $R/out/11-simp-seal-set.txt
  cp $R/probe/IC$1.lean $R/wt-ovl/ReviewProbe/
  bash elab.sh $R/wt-ovl $S/oleans-lseam2 ReviewProbe/IC$1.lean $R/out/$T-seal-IC$1.out
done
for f in $R/out/$T-*.out; do
  echo "== $(basename $f): $(grep -cE ':[0-9]+:[0-9]+: error' $f) errors; $(grep -cE ":[0-9]+:[0-9]+: warning: declaration uses 'sorry'" $f) sorry warnings; $(grep -cE ':[0-9]+:[0-9]+: warning' $f) warnings; $(tail -1 $f)"
done
