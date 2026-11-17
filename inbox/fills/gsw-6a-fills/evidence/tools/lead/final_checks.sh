#!/usr/bin/env bash
# final_checks.sh <tag> (gsw-6a-fills, new): run checks 1-12 at the head of fill/gsw-6a-fills in /home/user/fill6a,
# writing every output under /home/user/w6/evidence/*/<tag>*. The base seals are run separately (they do not
# depend on the head). Stops on nothing: every result is read from its file.
set -u
TAG=$1; W=/home/user/w6; E=$W/evidence; T=$W/tools; R=/home/user/fill6a; B=05999162b77c1f0fef64b07427e1a041a31b43d2
PK=/home/user/exchange/outbox/fills/gsw-6a-fills
FILES=$(cut -f1 $E/headers/targets.tsv | sort -u)
export TCSLIB_OLEANS=$R/.lake/tcslib-check-oleans
cd $R
echo "== head $(git rev-parse HEAD) $(date -u +%FT%TZ)"
# 1. sweep of the DOWN modules (rebuild in dependency order) bound to git show HEAD
python3 -I $T/pbuild.py $R $E/build/down.txt $TCSLIB_OLEANS $E/build/sweep-$TAG
python3 -I - "$E/build/sweep-$TAG" <<'PY'
import subprocess, hashlib, sys
d = sys.argv[1]
rows = [l.rstrip('\n').split('\t') for l in open(d + '/summary.tsv') if not l.startswith('#')]
head = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
out = open(d + '/summary.txt', 'w'); bad = 0
out.write(f'# sweep at head {head}: module, rc, errors (G26-N1), error lines, sorry warnings, declarations, sha256 of `git show HEAD:<file>`, sha256 of the checked source, BOUND\n')
for r in rows:
    g = hashlib.sha256(subprocess.run(['git', 'show', f'HEAD:{r[0]}.lean'], capture_output=True).stdout).hexdigest()
    ok = g == r[10] == r[11] and r[1] == 'rc=0' and r[2] == 'errors=0' and r[3] == 'error_lines=0'
    bad += not ok
    out.write('\t'.join([r[0], r[1], r[2], r[3], r[4], r[5], g, r[10], 'BOUND' if g == r[10] == r[11] else 'UNBOUND']) + '\n')
out.write(f'RESULT modules={len(rows)} bad={bad}\n'); out.close(); print(open(d + '/summary.txt').read())
PY
# 2. admissions
python3 -I $T/admissions_fill.py $PK/base-sorries.txt $PK/targets.txt $E/build/bootstrap/summary.tsv $E/build/sweep-$TAG/summary.tsv > $E/admissions/admissions-$TAG.txt; tail -1 $E/admissions/admissions-$TAG.txt
grep -c '\bsorry\b' $FILES > $E/admissions/sorry-tokens-$TAG.txt; cat $E/admissions/sorry-tokens-$TAG.txt
# 3. statements
python3 -I $E/tools/records/decls2.py . $B $FILES > $E/stmt/decls2-$TAG.txt 2>&1
echo "RESULT ADDED=$(grep -c '^ADDED' $E/stmt/decls2-$TAG.txt) CHANGED=$(grep -c '^CHANGED' $E/stmt/decls2-$TAG.txt) REMOVED=$(grep -c '^REMOVED' $E/stmt/decls2-$TAG.txt)" | tee -a $E/stmt/decls2-$TAG.txt
cp $E/stmt/StmtDump.lean probes/StmtDump.lean
python3 -I $T/pool_run.py lead:StmtDump-$TAG $E/stmt/StmtDump-head-$TAG.log -- bash scripts/lean_check_tree.sh probes/StmtDump
cmp $E/stmt/StmtDump-base.log $E/stmt/StmtDump-head-$TAG.log && echo "STMTDUMP IDENTICAL" | tee $E/stmt/StmtDump-compare-$TAG.txt
(cd $E/headers && python3 -I frozen_owned.py $R $B HEAD allow.tsv targets.tsv $FILES --controls > frozen-$TAG.txt; tail -1 frozen-$TAG.txt; grep -c UNEXPECTED frozen-$TAG.txt)
# 4. axioms
cp $E/axioms/AxiomProbe.lean probes/AxiomProbe.lean
python3 -I $T/pool_run.py lead:AxiomProbe-$TAG $E/axioms/AxiomProbe-$TAG.log -- bash scripts/lean_check_tree.sh probes/AxiomProbe
python3 -I $T/trace_check.py $E/axioms/AxiomProbe-$TAG.log $PK/base-sorries.txt > $E/axioms/trace-check-$TAG.txt; tail -4 $E/axioms/trace-check-$TAG.txt
# 6. frozen files
git diff --stat $B HEAD | tee $E/git-diff-stat-$TAG.txt
# 7. lint
python3 -I scripts/style_lint.py $FILES > $E/lint/style-head-$TAG.txt 2>&1; tail -1 $E/lint/style-head-$TAG.txt
python3 -I scripts/campaign_style_lint.py TCSlib/Complexity --check8b > $E/lint/campaign-head-$TAG.txt 2>&1; tail -1 $E/lint/campaign-head-$TAG.txt
diff <(grep -E "FAIL|WARN" $E/lint/campaign-base.txt | sort) <(grep -E "FAIL|WARN" $E/lint/campaign-head-$TAG.txt | sort) > $E/lint/campaign-diff-$TAG.txt; echo "campaign line-set diff lines: $(wc -l < $E/lint/campaign-diff-$TAG.txt)"
# 8-10
python3 -I $T/sizes_fill.py $R $B HEAD > $E/sizes/sizes-$TAG.txt; cat $E/sizes/sizes-$TAG.txt
python3 -I $T/hygiene.py --base $R $B $FILES > $E/docs/hygiene-$TAG.txt; tail -1 $E/docs/hygiene-$TAG.txt
python3 -I $T/clash_fill.py $R $B HEAD $FILES > $E/clash/clash-$TAG.txt 2>&1; tail -1 $E/clash/clash-$TAG.txt
# 12. series and reproduction
mkdir -p $W/$TAG && bash $T/series_fill.sh $R $B fill/gsw-6a-fills $W/$TAG > /dev/null 2>&1; cp $W/$TAG/reproduce.log $E/reproduce-$TAG.log; tail -1 $E/reproduce-$TAG.log; grep -c REPRODUCED $E/reproduce-$TAG.log
# merge-tree with the records tip (information)
git fetch -q origin refs/heads/cryptography/pass-shelat-ch2-4:refs/remotes/origin/cryptography/pass-shelat-ch2-4
TIP=$(git rev-parse origin/cryptography/pass-shelat-ch2-4)
{ echo "records tip fetched $(date -u +%FT%TZ): $TIP"; echo "head: $(git rev-parse HEAD)"; o=$(git merge-tree --write-tree HEAD $TIP 2>&1); echo "git merge-tree --write-tree HEAD $TIP: rc=$?"; echo "$o" | head -5; } > $E/git-merge-tree-$TAG.txt; cat $E/git-merge-tree-$TAG.txt
