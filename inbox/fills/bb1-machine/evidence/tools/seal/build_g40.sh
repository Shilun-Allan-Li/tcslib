#!/usr/bin/env bash
# build_g40.sh <tree>: phase 1 of LE-gate40 on one olean tree: snapshot-pre, closure need list,
# ladder build (backups first) of every needed module. No root TCSlib.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
TREE=$1; E=$SP/dl-review/gate40-le; W=$SP/wt-gate40; T=$E/tools
mkdir -p $E/tree $E/build
python3 -I $T/snapshot.py $TREE $E/tree/snapshot-pre.txt | tee $E/tree/snapshot-pre.summary
sha256sum $E/tree/snapshot-pre.txt
python3 -I $T/need.py $W $TREE eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9 \
  TCSlib.Cryptography.Pairing TCSlib.Cryptography.KeyExchange TCSlib.Cryptography.AdvancedEncryption \
  > $E/build/closure-need.txt 2> $E/build/closure-need.err
awk '{print $2}' $E/build/closure-need.txt > $E/build/closure-order.txt
cat $E/build/closure-need.txt $E/build/closure-need.err
$T/ladder_g40.sh $TREE $W $E/build/closure-order.txt $E/build/closure $E/bk $E/tree/snapshot-pre.txt
