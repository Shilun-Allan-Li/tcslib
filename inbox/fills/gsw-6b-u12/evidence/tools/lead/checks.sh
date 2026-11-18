#!/usr/bin/env bash
# gsw-6b-u12: run C1-C11 at the current head of fill/gsw-6b-u12 under evidence tag TAG (cp1 | final).
# C1 sweep of the UNIT-DOWN modules (pool, 3), binding; C2 admissions; C3 decls2, StmtDump;
# C4 frozen check with controls; C5 axioms and trace; C6 seals (head and base), liveness pair,
# explicit-unfold scan; C7 lint (head; base once); C8/C9 sizes and hygiene; C10 clash.
set -eu
TAG=$1
W=/workspace/gsw; R=$W/repo; E=$W/evidence; T=$W/tools
B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d
F=TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean
export PATH=$HOME/.elan/bin:$PATH
cd $W
HEAD=$(git -C $R rev-parse HEAD)
echo "checks $TAG at head $HEAD $(date -u +%FT%TZ)"
# C1
rm -rf $E/build/sweep-$TAG $E/build/sweep-$TAG.tsv
echo "$(date -u +%FT%TZ) sweep $TAG at head $HEAD: the 10 UNIT-DOWN modules, pool 3" >> $E/logs/pool.log
python3 -I $T/pool.py $R $E/build/sweep-order.txt $E/build/sweep-$TAG.tsv $E/build/sweep-$TAG 3 $E/logs/pool.log
python3 -I - "$TAG" <<'EOP'
import hashlib, subprocess, sys
tag = sys.argv[1]
rows = [l.rstrip('\n').split('\t') for l in open(f'/workspace/gsw/evidence/build/sweep-{tag}.tsv')]
head = subprocess.run(['git', '-C', '/workspace/gsw/repo', 'rev-parse', 'HEAD'], capture_output=True,
                      text=True).stdout.strip()
out = [f'# sweep at head {head}: module, rc, errors (both forms), sorry warnings, SHA-256 of the '
       'checked source, SHA-256 of git show HEAD:<path>, bound']
bad = 0
for m, rc, e, s, *_ in rows:
    hs = hashlib.sha256(open(f'/workspace/gsw/repo/{m}.lean', 'rb').read()).hexdigest()
    gh = hashlib.sha256(subprocess.run(['git', '-C', '/workspace/gsw/repo', 'show', f'HEAD:{m}.lean'],
                                       capture_output=True).stdout).hexdigest()
    ok = rc == '0' and e == '0' and hs == gh
    bad += not ok
    out.append(f'{m}\t{rc}\t{e}\t{s}\t{hs}\t{gh}\t{"yes" if hs == gh else "NO"}')
out.append(f'RESULT modules={len(rows)} bad={bad}')
open(f'/workspace/gsw/evidence/build/summary-{tag}.txt', 'w').write('\n'.join(out) + '\n')
print(out[-1])
EOP
# C2
python3 -I $T/sorrycensus.py $R $E/logs/order.txt $E/build/sweep-$TAG $E/build/bootstrap > $E/build/admissions-$TAG.txt
{ diff <(grep -v TOTAL $W/inputs/briefs/lattice-gsw/phase6/issued-6b-fills-r1/base-sorries.txt) \
    <(grep -v TOTAL $E/build/admissions-$TAG.txt) || true; echo "sorry tokens in the owned file: $(grep -c '\bsorry\b' $R/$F || true)"; tail -1 $E/build/admissions-$TAG.txt; } > $E/build/admissions-$TAG-vs-base.txt
cat $E/build/admissions-$TAG-vs-base.txt
# C3
(cd $R && python3 -I $T/records/decls2.py . $B $F) > $E/stmt/decls2-$TAG.txt
{ echo "# decls2.py . $B $F at head $HEAD (empty output means no row)"; cat $E/stmt/decls2-$TAG.txt;
  echo "RESULT ADDED $(grep -c '^ADDED' $E/stmt/decls2-$TAG.txt || true) CHANGED $(grep -c '^CHANGED' $E/stmt/decls2-$TAG.txt || true) REMOVED $(grep -c '^REMOVED' $E/stmt/decls2-$TAG.txt || true)"; } > $E/stmt/decls2-$TAG-summary.txt
tail -1 $E/stmt/decls2-$TAG-summary.txt
bash $T/stmtdump.sh HEAD head-$TAG
if diff <(grep -v "declaration uses 'sorry'" $E/stmt/StmtDump-base.stripped) $E/stmt/StmtDump-head-$TAG.stripped > $E/stmt/StmtDump-diff-$TAG.txt; then echo "StmtDump identical" | tee -a $E/stmt/StmtDump-diff-$TAG.txt; else echo "StmtDump DIFFERS"; fi
# C4
python3 -I $T/lead/frozen_owned.py $R $B HEAD $E/headers/allow.tsv $E/headers/targets.tsv $F --controls > $E/headers/frozen-$TAG.txt
tail -1 $E/headers/frozen-$TAG.txt
git -C $R diff --stat $B HEAD > $E/git-diff-stat-$TAG.txt
# C5
(cd $R && bash scripts/lean_check_tree.sh scratch/ax/AxiomProbe > $E/axioms/AxiomProbe-$TAG.log 2>&1; echo "EXIT $?" >> $E/axioms/AxiomProbe-$TAG.log)
grep "TOTAL\|SORRY-REACHING\|EXIT" $E/axioms/AxiomProbe-$TAG.log
# C6
rm -rf $E/rule10/$TAG $E/rule10/live-$TAG $E/rule10/unfold-$TAG
(cd $R && python3 -I $T/lead/seals.py $TAG $R $F | tail -5)
(cd $R && python3 -I $T/lead/seals.py live-$TAG $R $F --live $E/rule10/live-src/live-Branching.lean | tail -6)
mkdir -p $E/rule10/unfold-$TAG
echo $F > /tmp/rwf.txt
(cd $R && python3 -I $T/lead/rwids_run.py /tmp/rwf.txt $E/rule10/unfold-$TAG | tail -1)
{ echo "# explicit-unfold scan ($TAG, head $HEAD): identifiers given to rw/simp/simpa/unfold/delta, resolved"; cut -f2,3,4 $E/rule10/unfold-$TAG/rwids.tsv | sort -u;
  echo "RESULT foreign=$(grep -c FOREIGN-TCSLIB-DEF $E/rule10/unfold-$TAG/rwids.tsv || true)"; } > $E/rule10/unfold-$TAG/explicit-unfold-scan.txt
tail -1 $E/rule10/unfold-$TAG/explicit-unfold-scan.txt
# C7
(cd $R && python3 -I scripts/style_lint.py $F > $E/lint/style-head-$TAG.txt 2>&1; echo "rc $?" >> $E/lint/style-head-$TAG.txt)
(cd $R && python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b > $E/lint/campaign-head-$TAG.txt 2>&1 || true)
python3 -I $T/lead/lintdiff.py $E/lint/campaign-base.txt $E/lint/campaign-head-$TAG.txt > $E/lint/campaign-diff-$TAG.txt
tail -2 $E/lint/campaign-diff-$TAG.txt; head -1 $E/lint/style-head-$TAG.txt
# C8, C9
python3 -I $T/lead/sizes_hygiene.py $R $B HEAD $F $E/sizes $TAG
mv $E/sizes/hygiene-$TAG.txt $E/docs/
echo "checks $TAG done $(date -u +%FT%TZ)"
