#!/usr/bin/env bash
# Delta verification for the final head H on top of the complete final verification at P:
# replay of every module whose source changed P..H or that imports one (transitively), then root
# and Checks (phase final-delta); census rerun (census-final3); whole-file seals (both variants) of
# the changed files re-run at H (the other 96 files' sources and closures are byte-identical at
# P and H). Serial.
set -u
P=ea37eb57c28710271e41533d528309a6d7d00519
cd /workspace/cp2/src
H=$(git rev-parse HEAD)
EV=/workspace/cp2/evidence; L=$EV/logs
NOT=Complexity.PolyExpr.eval,Complexity.PolyExpr.eval.match_1,Complexity.PolyExpr.eval._sunfold
export CHK_PHASE=final-delta
echo "## DELTA START $(date -u +%FT%TZ) P=$P H=$H dirty=$(git status --porcelain -- TCSlib audits TCSlib.lean | wc -l)"
python3 -I /workspace/cp2/tools/order.py $L/order-final-delta.txt
python3 -I - <<PY
import subprocess
ROOT='/workspace/cp2/src'
src=open('/workspace/cp2/tools/chk.py').read()
exec(src.split('def header_imports')[1].split('imports = header_imports')[0].join(['def header_imports','']))
order=[l.strip() for l in open('$L/order-final-delta.txt') if l.strip()]
ch={p[:-5] for p in subprocess.check_output(['git','-C',ROOT,'diff','--name-only','$P','$H'],text=True).split() if p.endswith('.lean')}
aff=set(ch)
for m in order:
    imps=[x.replace('.','/') for x in header_imports(open(f'{ROOT}/{m}.lean').read()) if x.startswith('TCSlib')]
    if any(i in aff for i in imps): aff.add(m)
sel=[m for m in order if m in aff]
open('$L/affected-final-delta.txt','w').write('\n'.join(sel)+'\n')
print(len(ch),'changed P..H;',len(sel),'affected')
PY
n=0; t=$(wc -l < $L/affected-final-delta.txt)
while read -r m; do n=$((n+1)); echo "## $n/$t $m"; python3 -I /workspace/cp2/tools/chk.py "$m"; done < $L/affected-final-delta.txt
echo "## root"; python3 -I /workspace/cp2/tools/chk.py TCSlib
echo "## Checks"; python3 -I /workspace/cp2/tools/chk.py audits/pass-shelat/Checks
echo "## replay done $(date -u +%FT%TZ)"
unset CHK_PHASE
mv $EV/census/final $EV/census/final-at-ea37eb57c
mkdir -p $EV/census/final
python3 -I /workspace/cp2/tools/gen_census.py /workspace/tcslib/outbox/fills/cleanup-part2/inputs/owned-files.txt .lake/cleanup-part2-probes/census/FinalCensus3.lean $EV/census/final
CHK_PHASE=census-final3 python3 -I /workspace/cp2/tools/chk.py .lake/cleanup-part2-probes/census/FinalCensus3
for f in names.tsv axioms.tsv c3.tsv closure.tsv; do cmp -s $EV/census/final/$f $EV/census/final-at-ea37eb57c/$f && echo "IDENTICAL-TO-P $f" || echo "DIFFERS-FROM-P $f"; done
echo "## census done $(date -u +%FT%TZ)"
git diff --name-only $P $H | sed 's/\.lean$//' > $L/seal-delta-modules.txt
for ph in final final-strict; do
  cp $L/seal-$ph.json $L/seal-$ph-at-ea37eb57c.json
  python3 -I - <<PY
import json
d=json.load(open('$L/seal-$ph.json'))
for m in open('$L/seal-delta-modules.txt').read().split():
    d.pop(m, None)
json.dump(d, open('$L/seal-$ph.json','w'), indent=1)
PY
done
CP2_SEAL_NOTATION=$NOT python3 -I /workspace/cp2/tools/sealrun.py final $H $EV/census/final/closure.tsv $L/seal-delta-modules.txt
python3 -I /workspace/cp2/tools/sealrun.py final-strict $H $EV/census/final/closure.tsv $L/seal-delta-modules.txt
echo "## DELTA DONE $(date -u +%FT%TZ)"
