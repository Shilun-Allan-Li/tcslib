#!/usr/bin/env bash
# abbrev_experiment.sh: decision data for exclusions.md section C (not committed; not part of the PR).
# In a shadow copy of the sources at the final commit (abbrev/src; the worktree is not touched):
# `def QueryImpl` -> `abbrev QueryImpl` (Games/Simulate.lean) and `def OracleSpec.add` ->
# `abbrev OracleSpec.add` (Games/OracleComp.lean). Replays every module downstream of the two files
# into a separate copy of the olean tree, then collects candidates and seals the 14 Games files with
# NO named entry.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
G=$SP/g04r4; WT=$SP/wt-g04r4; X=$G/abbrev; OL=$SP/g04r4-abbrev-oleans; S=$X/src
rm -rf $X $OL; mkdir -p $S/.lake
git -C $WT archive HEAD TCSlib TCSlib.lean audits scripts lean-toolchain | tar -x -C $S
ln -s /home/user/tcslib/.lake/packages $S/.lake/packages
cp -a $SP/g04r4-oleans $OL
sed -i 's/^def QueryImpl {ι ι'"'"' : Type} (spec : OracleSpec ι) (σ : Type) (spec'"'"' : OracleSpec ι'"'"') : Type :=$/abbrev QueryImpl {ι ι'"'"' : Type} (spec : OracleSpec ι) (σ : Type) (spec'"'"' : OracleSpec ι'"'"') : Type :=/' $S/TCSlib/Cryptography/Games/Simulate.lean
sed -i 's/^def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :$/abbrev OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :/' $S/TCSlib/Cryptography/Games/OracleComp.lean
for f in Simulate OracleComp; do diff <(git -C $WT show HEAD:TCSlib/Cryptography/Games/$f.lean) $S/TCSlib/Cryptography/Games/$f.lean; done > $X/abbrev.diff
[ "$(grep -c '^>' $X/abbrev.diff)" = 2 ] || { echo "edit did not apply"; exit 3; }
python3 -I $SP/tools/downstream2.py $S TCSlib.Cryptography.Games.OracleComp TCSlib.Cryptography.Games.Simulate \
  | awk '$2=="DOWN"{print $1}' > $X/order.txt
echo audits/pass-shelat/Checks >> $X/order.txt
bash $SP/tools/ladder-ol.sh $S $X/order.txt $X/replay.log $OL
rc=$?
if [ $rc = 0 ]; then
  # one-pass collection (term, instance and statement tiers) against the abbrev tree
  bash $G/tools/run_collect.sh $S $OL $X/candidates > $X/collect.out 2>&1
  grep Games/ $G/changed-files.txt > $X/games.txt
  python3 -I $G/tools/seal.py abbrev $S $OL $X/candidates $X/games.txt $X/sealout > $X/seal.log 2>&1
fi
echo "abbrev experiment: replay rc=$rc"
