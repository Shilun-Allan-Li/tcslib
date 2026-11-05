#!/usr/bin/env bash
# Gate 91 round 2's resolution (minor 1): the edge-mode PR's elaboration chain at #184's head, with
# provenance. A fresh copy-on-write clone of oleans-larm (replay-larm: 138/138 at #182's 8fd6f91a,
# static-equal); #182's head 94093275 differs from 8fd6f91a only in Machines/ARMProof, so ARMProof's
# dependents among the Codec modules' imports are recompiled first, then the 16 Codec modules
# (chain_order.py). Each module: its blob at HEAD, the hash of the file compiled (they must agree),
# exit status, output lines, time. Usage: bash elab_chain_r2res.sh <worktree> <clone> <out dir>
WT=$1; O=$2; E=$3
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
[ -e "$O" ] && { echo "clone $O exists; remove it first" >&2; exit 2; }
[ -z "$(git -C $WT status --porcelain -- TCSlib)" ] || { echo "TCSlib has uncommitted changes" >&2; exit 2; }
cp -cR $S/oleans-larm "$O" || exit 2
L=$E/chain.log
{ echo "# worktree $WT at $(git -C $WT rev-parse HEAD) (TCSlib clean)"
  echo "# clone $O: cp -cR of $S/oleans-larm (replay-larm at 8fd6f91a); $(date)"
  echo "# Lean diff 8fd6f91a..HEAD outside Codec: $(git -C $WT diff --name-only 8fd6f91a HEAD -- '*.lean' | grep -v /Codec/ | tr '\n' ' ')"; } > $L
python3 -I $(dirname $0)/chain_order.py $WT > $E/order.txt
while read -r m; do
  f=${m//.//}.lean; b=$(basename $f .lean)
  blob=$(git -C $WT rev-parse HEAD:$f); hob=$(git -C $WT hash-object $f)
  ( cd $WT && /usr/bin/time -p bash $S/tools/leanelab-o.sh $WT $O $f $O ) > $E/$b.out 2> $E/$b.time
  st=$?
  echo "$m exit=$st lines=$(wc -l < $E/$b.out | tr -d ' ') blob=$blob compiled=$([ $blob = $hob ] && echo same || echo DIFFERENT) $(grep real $E/$b.time)" >> $L
done < $E/order.txt
echo "# done $(date)" >> $L
