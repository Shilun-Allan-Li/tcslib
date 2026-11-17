#!/usr/bin/env bash
# run_heads.sh <o2-rev> <final-rev> <outroot> (gsw-6b-statements sub-agent `seal`, new): the full Rule 10 set at one pair of
# heads, in the lead's priority order, with the worktree /home/user/sub/seal already at <final-rev> and
# /home/user/oleans/seal re-seeded from it:
#   <outroot>/o2           BitEncoding at <o2-rev> (source-identity guard: bytes must equal the worktree's)
#   <outroot>/final-bitenc BitEncoding at <final-rev>
#   <outroot>/final        the 9 other new files and the facades GSW.lean, LWE.lean at <final-rev>
# Module lists and control specs are copied from /home/user/ev/rule10/{o2,final}/ (the a855e111 runs).
set -u
O2=$1; FIN=$2; R=$3; H=/home/user/ev/tools/seal; S=/home/user/ev/rule10; WT=/home/user/sub/seal
BASE=3e51b5f28900db6190f1eb2e6d207d27ee15d541
G=TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
[ "$(git -C $WT rev-parse HEAD)" = "$(git -C $WT rev-parse $FIN)" ] || { echo "worktree not at $FIN"; exit 1; }
mkdir -p $R/o2 $R/final-bitenc $R/final
cp $S/o2/modules.txt $S/o2/controls-spec.json $R/o2/; cp $S/o2/modules.txt $S/o2/controls-spec.json $R/final-bitenc/
cp $S/final/modules.txt $S/final/controls-spec.json $R/final/
bash $H/run_checkpoint.sh $WT $O2 $BASE $R/o2 $R/o2/modules.txt $R/o2/controls-spec.json "gsw-6b seal O2 head BitEncoding"
bash $H/run_checkpoint.sh $WT $FIN $BASE $R/final-bitenc $R/final-bitenc/modules.txt $R/final-bitenc/controls-spec.json "gsw-6b seal final head BitEncoding"
NOTATION="$G.LevelCoins $G.LeveledSeeds $G.LeveledView" JOBS=3 \
  bash $H/run_checkpoint.sh $WT $FIN $BASE $R/final $R/final/modules.txt $R/final/controls-spec.json "gsw-6b seal final head"
