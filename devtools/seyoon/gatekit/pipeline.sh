#!/usr/bin/env bash
# Gate 149 post-replay pipeline: checks (metadata, seals, controls, qa), then the Lean-backed sweeps.
set -uo pipefail
source "$(dirname "$0")/lib.sh"
S=$SCRATCH; G=$GATE; O=$S/$OUTPUT_SNAPSHOT; RT=$G/replay/runtime
bash $KIT/checks.sh > $G/checks.out 2>&1; tail -4 $G/checks.out
grep -q "CHECKS DONE" $G/checks.out || { echo CHECKS-INCOMPLETE; exit 1; }
rm -rf $G/dsw $G/dsw-ov; mkdir -p $G/dsw/.lake $G/dsw/TCSlib/Scratch/DefSweep
cp -a $RT/TCSlib $RT/TCSlib.lean $RT/lean-toolchain $RT/lake-manifest.json $G/dsw/
ln -s "$(readlink -f $RT/.lake/packages)" $G/dsw/.lake/packages
cp $KIT/defsweep/Kinds.lean $G/dsw/TCSlib/Scratch/Kinds.lean
cp -al $O $G/dsw-ov
python3 -I $KIT/defsweep/extract.py $G/SOURCE.json $RT $G/dsw/TCSlib/Scratch/DefSweep
python3 -I $KIT/defsweep/cites.py $G/SOURCE.json $RT $G/base-src $G/dsw/TCSlib/Scratch/DefSweep
mkdir -p $G/defsweep; bash $KIT/defsweep/run.sh > $G/defsweep/run.out 2>&1; tail -3 $G/defsweep/run.out
P=$(bash $TOOLS/leanpool.sh); echo "pool $P"
ls $G/dsw/TCSlib/Scratch/DefSweep/Cite_*.lean | xargs -n1 basename | sed 's/\.lean$//' | S=$S G=$G TOOLS=$TOOLS xargs -P "$P" -I{} bash -c \
  'bash $TOOLS/leanelab-o.sh $G/dsw $G/dsw-ov TCSlib/Scratch/DefSweep/{}.lean $G/dsw-ov > $G/defsweep/{}.log 2>&1; echo "{} exit $?"' | sort
echo PIPELINE DONE
