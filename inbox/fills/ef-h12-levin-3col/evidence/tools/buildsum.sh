#!/usr/bin/env bash
# Fresh check of every LevinHardness module (in dependency order) at the fill head; summary bound to git show HEAD.
cd /home/user/work/fill
H=$(git rev-parse HEAD); E=/home/user/work/ev/evidence/build; mkdir -p $E; S=$E/summary.txt
echo "head $H  date $(date -u +%FT%TZ)" > $S
for m in "$@"; do p=TCSlib/Cryptography/ZeroKnowledge/LevinHardness/$m; [ "$m" = FACADE ] && p=TCSlib/Cryptography/ZeroKnowledge/LevinHardness; [ "$m" = ZK ] && p=TCSlib/Cryptography/ZeroKnowledge
  TCSLIB_OLEANS=/home/user/work/ol-lead /home/user/work/tools/lean_slot.sh $PWD $p > $E/$(basename $p).log 2>&1; rc=$?
  e=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error[:(]' $E/$(basename $p).log); e2=$(grep -c 'error' $E/$(basename $p).log)
  so=$(grep -c "declaration uses 'sorry'" $E/$(basename $p).log); s1=$(sha256sum < $p.lean | cut -c1-64); s2=$(git show HEAD:$p.lean | sha256sum | cut -c1-64)
  echo -e "$p\trc=$rc\terrors=$e\terror_mentions=$e2\tsorry_warnings=$so\tsha256=$s1\thead_match=$([ $s1 = $s2 ] && echo yes || echo NO)" >> $S
done; cat $S
