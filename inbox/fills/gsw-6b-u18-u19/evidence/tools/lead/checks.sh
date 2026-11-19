#!/usr/bin/env bash
# gsw-6b-u18-u19: run C1-C10 at the current head of fill/gsw-6b-u18-u19 under evidence tag TAG
# (cp1 | final); the gsw-6b-u12 runner adapted to the two owned files.
# C1 sweep of the 5 UNIT-DOWN modules (pool 3), binding; C2 admissions; C3 decls2, StmtDump;
# C4 frozen check with controls; C5 axioms and trace; C6 seals (head; base once), liveness pairs,
# explicit-unfold scan; C7 lint (head; base once); C8/C9 sizes and hygiene; C10 clash.
set -eu
TAG=$1
W=/work/deliv; R=/work/tcslib; E=$W/evidence; T=$W/tools
B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d
IN=/tmp/b/briefs/lattice-gsw/phase6/issued-6b-fills-r1
G=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
F1=$G/PolyRatio.lean; F2=$G/Asymptotic.lean
export PATH=$HOME/.elan/bin:$PATH
export TCSLIB_OLEANS=/work/oleans
cd $W
HEAD=$(git -C $R rev-parse HEAD)
echo "checks $TAG at head $HEAD $(date -u +%FT%TZ)"
mkdir -p $E/build $E/stmt $E/headers $E/axioms $E/rule10 $E/lint $E/sizes $E/docs $E/clash
# C1
grep -P '^UNIT-DOWN\tgsw-6b-u18-u19\t' $IN/closures.txt | cut -f3 > $E/build/sweep-order.txt
rm -rf $E/build/sweep-$TAG
echo "$(date -u +%FT%TZ) sweep $TAG at head $HEAD: the 5 UNIT-DOWN modules, pool 3" >> $E/logs/pool.log
(cd $R && python3 -I $T/sweep.py $E/build/sweep-order.txt 3 $E/build/sweep-$TAG $R)
python3 -I - "$TAG" <<'EOP'
import hashlib, subprocess, sys
tag = sys.argv[1]
R, E = '/work/tcslib', '/work/deliv/evidence'
rows = [l.rstrip('\n').split('\t') for l in open(f'{E}/build/sweep-{tag}/sweep.tsv')]
head = subprocess.run(['git', '-C', R, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
out = [f'# sweep at head {head}: module, rc, errors (form "error:"), errors (form "error[:(]"), sorry '
       'warnings, peak RSS kB, SHA-256 of the checked source, SHA-256 of git show HEAD:<path>, bound']
bad = 0
for m, rc, st, en, sec, rss, e1, e2, sw in rows:
    hs = hashlib.sha256(open(f'{R}/{m}.lean', 'rb').read()).hexdigest()
    gh = hashlib.sha256(subprocess.run(['git', '-C', R, 'show', f'HEAD:{m}.lean'],
                                       capture_output=True).stdout).hexdigest()
    ok = rc == '0' and e1 == '0' and e2 == '0' and hs == gh
    bad += not ok
    out.append(f'{m}\t{rc}\t{e1}\t{e2}\t{sw}\t{rss}\t{hs}\t{gh}\t{"yes" if hs == gh else "NO"}')
out.append(f'RESULT modules={len(rows)} bad={bad}')
open(f'{E}/build/summary-{tag}.txt', 'w').write('\n'.join(out) + '\n')
print(out[-1])
EOP
# C2
python3 -I $T/sorrycensus.py $R $E/logs/order.txt $E/build/sweep-$TAG $E/build/bootstrap > $E/build/admissions-$TAG.txt
{ echo "# diff base-sorries.txt (records) vs the head census (< base only, > head only)"
  diff <(grep -v '^#' $IN/base-sorries.txt | grep -v TOTAL) <(grep -v TOTAL $E/build/admissions-$TAG.txt) || true
  echo "sorry tokens in the owned files: $(grep -cw sorry $R/$F1 || true) $(grep -cw sorry $R/$F2 || true)"
  echo "admit/native_decide/axiom/opaque tokens in the owned files: $(grep -cwE 'admit|native_decide|axiom|opaque' $R/$F1 $R/$F2 | tr '\n' ' ')"
  tail -1 $E/build/admissions-$TAG.txt; } > $E/build/admissions-$TAG-vs-base.txt
cat $E/build/admissions-$TAG-vs-base.txt
# C3
(cd $R && python3 -I $T/records/decls2.py . $B $F1 $F2) > $E/stmt/decls2-$TAG.txt
{ echo "# decls2.py . $B $F1 $F2 at head $HEAD"; cat $E/stmt/decls2-$TAG.txt;
  for f in $F1 $F2; do echo "RESULT $f ADDED $(grep -c "^ADDED.$f" $E/stmt/decls2-$TAG.txt || true) CHANGED $(grep -c "^CHANGED.$f" $E/stmt/decls2-$TAG.txt || true) REMOVED $(grep -c "^REMOVED.$f" $E/stmt/decls2-$TAG.txt || true)"; done; } > $E/stmt/decls2-$TAG-summary.txt
grep RESULT $E/stmt/decls2-$TAG-summary.txt
[ -f $E/stmt/StmtDump-PolyRatio-base.stripped ] || bash $T/stmtdump.sh $B base
bash $T/stmtdump.sh HEAD head-$TAG
: > $E/stmt/StmtDump-diff-$TAG.txt
for k in PolyRatio Asymptotic; do
  if diff <(grep -v "declaration uses 'sorry'" $E/stmt/StmtDump-$k-base.stripped) <(grep -v "declaration uses 'sorry'" $E/stmt/StmtDump-$k-head-$TAG.stripped) >> $E/stmt/StmtDump-diff-$TAG.txt; then echo "StmtDump $k identical" | tee -a $E/stmt/StmtDump-diff-$TAG.txt; else echo "StmtDump $k DIFFERS" | tee -a $E/stmt/StmtDump-diff-$TAG.txt; fi
done
# C4
python3 -I $T/lead/frozen_owned.py $R $B HEAD $E/headers/allow.tsv $E/headers/targets.tsv $F1 $F2 --controls > $E/headers/frozen-$TAG.txt
[ -f $E/headers/frozen-base-vs-base.txt ] || python3 -I $T/lead/frozen_owned.py $R $B $B /dev/null $E/headers/targets.tsv $F1 $F2 > $E/headers/frozen-base-vs-base.txt
tail -1 $E/headers/frozen-$TAG.txt
git -C $R diff --stat $B HEAD > $E/git-diff-stat-$TAG.txt
# C5
(cd $R && bash scripts/lean_check_tree.sh scratch/ax/AxiomProbe > $E/axioms/AxiomProbe-$TAG.log 2>&1; echo "EXIT $?" >> $E/axioms/AxiomProbe-$TAG.log)
python3 -I $T/axcheck.py $E/axioms/AxiomProbe-$TAG.log > $E/axioms/axcheck-$TAG.txt
tail -3 $E/axioms/axcheck-$TAG.txt
# C6 (seals: head, live pairs and base run in parallel, 3 processes)
rm -rf $E/rule10/$TAG $E/rule10/live-PolyRatio-$TAG $E/rule10/live-Asymptotic-$TAG $E/rule10/unfold-$TAG $R/scratch/seal/$TAG $R/scratch/seal/live-*-$TAG
echo "$(date -u +%FT%TZ) seals $TAG: head seals, two liveness runs, base seals (once): at most 3 Lean processes" >> $E/logs/pool.log
(cd $R && python3 -I $T/lead/seals.py $TAG $R $F1 $F2 > $E/rule10/seals-$TAG.out 2>&1) &
(cd $R && python3 -I $T/lead/seals.py live-PolyRatio-$TAG $R $F1 --live $E/rule10/live-src/live-PolyRatio.lean > $E/rule10/live-PolyRatio-$TAG.out 2>&1 && python3 -I $T/lead/seals.py live-Asymptotic-$TAG $R $F2 --live $E/rule10/live-src/live-Asymptotic.lean > $E/rule10/live-Asymptotic-$TAG.out 2>&1) &
if [ ! -f $E/rule10/base/results.jsonl ]; then
  rm -rf /work/basetree; mkdir -p /work/basetree; git -C $R archive $B $F1 $F2 | tar -x -C /work/basetree
  (cd $R && python3 -I $T/lead/seals.py base /work/basetree $F1 $F2 > $E/rule10/seals-base.out 2>&1) &
fi
wait
tail -n 5 $E/rule10/seals-$TAG.out $E/rule10/live-*-$TAG.out
mkdir -p $E/rule10/unfold-$TAG
printf '%s\n' $F1 $F2 > /tmp/rwf.txt
(cd $R && python3 -I $T/lead/rwids_run.py /tmp/rwf.txt $E/rule10/unfold-$TAG | tail -2)
{ echo "# explicit-unfold scan ($TAG, head $HEAD): identifiers given to rw/simp/simpa/unfold/delta, resolved"; cut -f1,2,3,4,5 $E/rule10/unfold-$TAG/rwids.tsv | sort -u;
  echo "RESULT foreign=$(grep -c FOREIGN-TCSLIB-DEF $E/rule10/unfold-$TAG/rwids.tsv || true)"; } > $E/rule10/unfold-$TAG/explicit-unfold-scan.txt
tail -1 $E/rule10/unfold-$TAG/explicit-unfold-scan.txt
# C7
(cd $R && python3 -I scripts/style_lint.py $F1 $F2 > $E/lint/style-head-$TAG.txt 2>&1; echo "rc $?" >> $E/lint/style-head-$TAG.txt)
if [ ! -f $E/lint/campaign-base.txt ]; then
  rm -rf /work/basefull; git -C $R worktree add -q --detach /work/basefull $B
  (cd /work/basefull && python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b > $E/lint/campaign-base.txt 2>&1 || true)
  (cd /work/basefull && python3 -I scripts/style_lint.py $F1 $F2 > $E/lint/style-base.txt 2>&1; echo "rc $?" >> $E/lint/style-base.txt)
  git -C $R worktree remove --force /work/basefull
fi
(cd $R && python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b > $E/lint/campaign-head-$TAG.txt 2>&1 || true)
python3 -I $T/lead/lintdiff.py $E/lint/campaign-base.txt $E/lint/campaign-head-$TAG.txt > $E/lint/campaign-diff-$TAG.txt
cat $E/lint/campaign-diff-$TAG.txt; tail -2 $E/lint/style-head-$TAG.txt
# C8, C9
rm -f $E/sizes/sizes-$TAG.txt $E/docs/hygiene-$TAG.txt
for f in $F1 $F2; do python3 -I $T/lead/sizes_hygiene.py $R $B HEAD $f $E/sizes $TAG; done
mv $E/sizes/hygiene-$TAG.txt $E/docs/
cat $E/sizes/sizes-$TAG.txt
# C10
bash $T/clash.sh $TAG > $E/clash/clash-$TAG.txt
tail -1 $E/clash/clash-$TAG.txt
echo "checks $TAG done $(date -u +%FT%TZ)"
