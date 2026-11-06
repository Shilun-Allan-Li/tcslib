#!/usr/bin/env bash
# EXAMPLE (the queue that ran on 2026-11-06 after #214 and #223 merged). Copy to
# $TCSLIB_SCRATCH/fills/replay/, edit the snapshot names, C (the campaign merge commit), the
# expected module count and the prep lines, then run it with nohup. See START-HERE.md §5.
set -u
S=${TCSLIB_SCRATCH:?}; D=${TCSLIB_REPO:?}/devtools/seyoon; L=$S/fills/replay
export TCSLIB_SCRATCH=$S TCSLIB_REPO
bash $S/api/slotrun.sh bash $L/replay-lcamp7.sh > $L/replay-lcamp7.out 2>&1
grep -q '^# modules=120 failed=0' $L/replay-lcamp7.log || { echo lcamp7 failed; exit 1; }
C=72fcfbef3c1deb331aedc95d4a158a9ed4c56524
prep() { cd $S/$2 && git fetch -q origin && git reset -q --hard origin/$3 && n=$(git diff --name-only $C...origin/$3 -- '*.lean' | wc -l) && cd $S && bash $D/mk-next.sh $1 $2 $3 $C oleans-lcamp7 $L/replay-lcamp7.log oleans-$1 "the campaign after #214, #223 (oleans-lcamp7)" "$4" $n > $L/prep-$1.out 2>&1; }
run() { grep -q PRECHECK-PASSED $L/prep-$1.out && bash $S/api/slotrun.sh bash $L/replay-$1.sh > $L/replay-$1.out 2>&1; }
prep lcl3 wt-cl1 lean/dedup-cl1 "#220, CL-1, on the campaign after #214/#223"
prep lhv3 wt-harvest lean/u2-harvest-api "#221, the U2 harvest, on the campaign after #214/#223"
prep lsg7 wt-sg1 lean/dedup-sg1 "#215, SG-1, on the campaign after #214/#223"
prep lnb4 wt-natbits lean/dedup-natbits "#222, NatBits, on the campaign after #214/#223"
for n in lcl3 lhv3 lsg7 lnb4; do echo "$n: $(tail -1 $L/prep-$n.out)"; done
( run lcl3; run lhv3; run lsg7 ) &
( run lnb4 ) &
wait
echo queue12 done
