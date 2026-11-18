#!/usr/bin/env bash
# finalchecks.sh: C1, C3, C5, C6 (collector, canonical seals A/B strict/coe, controls, unfold scan),
# C7, C8, C9, C10, probes, at the committed head of fill/ef-d1-lattice-families. One Lean process at a time.
set -u
R=/home/user/work/ef-d1; EV=/home/user/work/evidence; T=/home/user/work/tools; ST=/home/user/work/sealtools
BASE=5ed465f62e4ae0f93ded1a1ba49e807591b589eb
export PATH=$HOME/.elan/bin:$PATH
cd $R
[ -z "$(git status --porcelain -- TCSlib)" ] || { echo "worktree not clean"; exit 2; }
HEAD=$(git rev-parse HEAD); echo "head $HEAD"
LP=.lake/tcslib-check-oleans; for d in .lake/packages/*/.lake/build/lib/lean; do LP=$LP:$d; done
FILES="TCSlib/Cryptography/LWE/Efficient.lean TCSlib/Cryptography/SIS/Efficient.lean TCSlib/Cryptography/SIS.lean"
# C1
mkdir -p $EV/build; : > $EV/build/summary.txt
for f in $FILES; do m=${f%.lean}; log=$EV/build/$(echo $m | tr / .).log
  bash scripts/lean_check_tree.sh $m > $log 2>&1; rc=$?
  e1=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error:' $log); e2=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error\(' $log)
  s=$(grep -c "declaration uses 'sorry'" $log)
  printf '%s\trc=%s\terrors(colon)=%s\terrors(paren)=%s\tsorry_warnings=%s\tsha256(git show HEAD:%s)=%s\tworktree_equal=%s\n' \
    $m $rc $e1 $e2 $s $f $(git show HEAD:$f | sha256sum | cut -c1-64) \
    $([ "$(git show HEAD:$f | sha256sum)" = "$(sha256sum < $f)" ] && echo yes || echo no) >> $EV/build/summary.txt
done
echo "head $HEAD" >> $EV/build/summary.txt
# C3 / C5
mkdir -p $EV/checks $EV/stmt
python3 -I $T/decls2.py . $BASE $FILES > $EV/checks/C3-decls2.tsv
LEAN_PATH=$LP lean $EV/stmt/StmtDump.lean > $EV/stmt/StmtDump.out 2>&1; echo "StmtDump rc=$?" > $EV/stmt/StmtDump.rc
for p in D1P1 D1P2 D1P3; do LEAN_PATH=$LP lean $EV/probes/$p.lean > $EV/probes/$p.out 2>&1; echo "$p rc=$?" > $EV/probes/$p.rc; done
# C4: sorry/admit/native_decide/axiom/opaque tokens in the new files, and the base's sorry set
grep -nE '\b(sorry|admit|native_decide|axiom|opaque)\b' TCSlib/Cryptography/LWE/Efficient.lean TCSlib/Cryptography/SIS/Efficient.lean > $EV/checks/C4-tokens.txt; echo "token lines: $(wc -l < $EV/checks/C4-tokens.txt) (docstring mentions only, if any)" >> $EV/checks/C4-tokens.txt
# C6: collector (referenced candidates), canonical candidates, seals, controls, unfold scan
S=$EV/seal; rm -rf $S/collector $S/canon/dev-* ; mkdir -p $S/canon
MODS=$ST/mods-final.txt bash $ST/run_collect.sh $R $R/$LP $S/collector > $S/collector.out 2>&1; python3 -I $ST/unsealable.py $S/collector >> $S/collector.out
for M in TCSlib.Cryptography.LWE.Efficient TCSlib.Cryptography.SIS.Efficient; do
  sed "s|@MOD@|$M|g; s|@OUT@|$S/canon/$M.all.tsv|" $T/AllDefs.lean.tmpl > $S/canon/AllDefs-$M.lean
  LEAN_PATH=$LP lean $S/canon/AllDefs-$M.lean > $S/canon/AllDefs-$M.out 2>&1
  for V in A-strict B-strict A-coe B-coe; do mkdir -p $S/canon/cand-$V
    awk -F'\t' -v V=$V '$2!="reducible" && $2!="irreducible" && !(V ~ /^A/ && ($1=="Complexity.PolyExpr.eval" || $1=="Complexity.PolyExpr.eval.match_1")) && !(V ~ /coe/ && $1=="TCSlib.InformationTheory.FinDist.instCoeFunForallReal")' $S/canon/$M.all.tsv > $S/canon/cand-$V/$M.txt
  done
done
printf 'TCSlib/Cryptography/LWE/Efficient.lean\nTCSlib/Cryptography/SIS/Efficient.lean\n' > $S/canon/files.txt
: > $S/canon/seal-summary.txt
for V in A-coe B-coe A-strict B-strict; do rm -rf $S/canon/out-$V
  python3 -I $ST/seal_canon.py $V $R $R/$LP $S/canon/cand-$V $S/canon/files.txt $S/canon/out-$V >> $S/canon/seal-summary.txt 2>&1
  for M in TCSlib.Cryptography.LWE.Efficient TCSlib.Cryptography.SIS.Efficient; do echo "$V $M candidates(requests)=$(wc -l < $S/canon/cand-$V/$M.txt)" >> $S/canon/seal-summary.txt; done
done
C=$S/controls
LS="TCSlib.Cryptography.LWE.Parameters.encode TCSlib.Cryptography.LWE.Family.boundedModulus TCSlib.Cryptography.LWE.noiseWord TCSlib.Cryptography.LWE.seedModulusWord TCSlib.Cryptography.LWE.seedWord TCSlib.Cryptography.LWE.seedModulus TCSlib.Cryptography.LWE.onesCount TCSlib.Cryptography.LWE.signedDiff TCSlib.Cryptography.LWE.centeredCore TCSlib.Cryptography.LWE.CenteredSampleEq TCSlib.Cryptography.LWE.dyadicParameters TCSlib.Cryptography.LWE.dyadicFamily TCSlib.Cryptography.LWE.EfficientFamily.ofBitSeeds TCSlib.Cryptography.LWE.EfficientFamily.ofDyadic TCSlib.Cryptography.LWE.dyadicExample"
SS="TCSlib.Cryptography.SIS.Parameters.encode TCSlib.Cryptography.SIS.dyadicScheduleParameters TCSlib.Cryptography.SIS.dyadicScheduleFamily TCSlib.Cryptography.SIS.EfficientFamily.ofDyadic TCSlib.Cryptography.SIS.dyadicExample"
: > $C/ctlcheck.txt
for o in lwe sis; do M=$([ $o = lwe ] && echo TCSlib.Cryptography.LWE.Efficient || echo TCSlib.Cryptography.SIS.Efficient); NAMES=$([ $o = lwe ] && echo "$LS" || echo "$SS")
  { echo "import $M"; echo; cat $C/${o}_body.lean; } > $C/Ctl_${o}_unsealed.lean
  { echo "import $M"; echo "attribute [local irreducible] $NAMES"; cat $C/${o}_body.lean; } > $C/Ctl_${o}_sealed.lean
  for v in unsealed sealed; do LEAN_PATH=$LP lean -DmaxErrors=0 $C/Ctl_${o}_$v.lean > $C/Ctl_${o}_$v.out 2>&1
    python3 -I $T/ctlcheck.py $C/Ctl_${o}_$v.lean $C/Ctl_${o}_$v.out $([ $v = sealed ] && echo 1 || echo 0) >> $C/ctlcheck.txt; done
done
{ python3 -I $T/unfoldscan.py $S/canon/TCSlib.Cryptography.LWE.Efficient.all.tsv TCSlib/Cryptography/LWE/Efficient.lean
  python3 -I $T/unfoldscan.py $S/canon/TCSlib.Cryptography.SIS.Efficient.all.tsv TCSlib/Cryptography/SIS/Efficient.lean
  echo "generated-equation references (collector .eqn.txt rows): $(cat $S/collector/*.eqn.txt | grep -v '^#' | grep -c .)"; } > $S/unfold-scan.txt
# C7 C8 C9 C10
python3 -I $T/c7facade.py . $BASE HEAD > $EV/checks/C7-facade.txt; git diff --stat $BASE HEAD > $EV/checks/C7-diffstat.txt
python3 -I scripts/style_lint.py TCSlib/Cryptography/LWE/Efficient.lean TCSlib/Cryptography/SIS/Efficient.lean TCSlib/Cryptography/SIS.lean > $EV/checks/C8-style_lint.txt 2>&1
python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b > $EV/checks/C8-campaign-head.txt 2>&1
grep -E "^(FAIL|WARN)" $EV/checks/C8-campaign-head.txt | sed 's/  */ /g' | sort > $EV/checks/C8-lines-head.txt
diff $EV/checks/C8-lines-base.txt $EV/checks/C8-lines-head.txt > $EV/checks/C8-campaign-diff.txt
python3 -I -c "
import sys
for f in sys.argv[1:]:
    L=open(f,encoding='utf-8').read().split('\n'); print(f, 'lines', len(L)-1, 'max width', max(len(l) for l in L))
" $FILES > $EV/checks/C9-sizes.txt
python3 -I $T/c10clash.py . $EV/checks/C3-decls2.tsv $BASE=IO-base 7563734a8badba842223e0687c719b3b4692e9d2=PR377-head c119a3c4f1d8642b1328740f1d1d1165a92f5567=cleanup/stage2-s2a > $EV/checks/C10-clashes.txt 2>&1
echo "finalchecks done at $HEAD"
