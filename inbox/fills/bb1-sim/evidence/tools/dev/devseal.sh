#!/usr/bin/env bash
# devseal.sh <A|B> <module> (bb1-sim, lead): development seal check (not evidence) of <module> in the
# worktree $WT (default the lead clone) against the olean tree $TREE (default tree F): writes the
# sealed variant to $WT/Bb1sSeal/<module path with / -> _>_<A|B>.lean (untracked) and checks it
# through scripts/lean_check_tree.sh under the host's one-Lean lock. Logs to $LOGDIR (default
# /home/user/fill/bb1sim/dev/seal).
set -u
V=$1; M=$2
WT=${WT:-/home/user/fill/tcslib}; TREE=${TREE:-/home/user/fill/treeF}
LOGDIR=${LOGDIR:-/home/user/fill/bb1sim/dev/seal}; mkdir -p $LOGDIR $WT/Bb1sSeal
N=$(echo $M | tr / _)_$V
python3 -I /home/user/exch/s/inbox/fills/bb1-sim/evidence/tools/dev/devseal.py $WT/$M.lean $WT/Bb1sSeal/$N.lean $V
export PATH=$HOME/.elan/bin:$PATH TCSLIB_OLEANS=$TREE
cd $WT && flock /home/user/fill/tcslib/.lean.lock bash scripts/lean_check_tree.sh Bb1sSeal/$N > $LOGDIR/$N.log 2>&1; rc=$?
echo "== devseal $V $M rc=$rc errors=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error[:(]' $LOGDIR/$N.log) $(grep -o 'DEVSEAL [AB] sealed [0-9]*' $LOGDIR/$N.log)"
grep -E '^\S+\.lean:[0-9]+:[0-9]+: error' $LOGDIR/$N.log | head -20
exit $rc
