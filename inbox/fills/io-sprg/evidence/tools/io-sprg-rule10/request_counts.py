# io-sprg Rule10 catalog counts,2026-11-18. Adapted to the Mac managed worktree.
# Reads only the completed nm-collector JSON lines; never invokes Lean or changes sources.
import argparse,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('collector_log');ap.add_argument('outdir');a=ap.parse_args()
cat={};roots={};closures={};stored={};cat_count=None
for line in Path(a.collector_log).read_text().splitlines():
 if line.startswith('CAT '):
  r=json.loads(line[4:]);assert r['name']['display'] not in cat;cat[r['name']['display']]=r
 elif line.startswith('ROOT '):
  r=json.loads(line[5:]);roots.setdefault(r['module'],[]).append(r)
 elif line.startswith('CLOSURE '):
  r=json.loads(line[8:]);closures[r['module']]=r['closure']
 elif line.startswith('MODULE '):
  m,c=line[7:].split(': stored ');stored[m]=int(c)
 elif line.startswith('CAT-COUNT '):cat_count=int(line.split()[1])
assert cat_count==len(cat),('incomplete collector CAT',cat_count,len(cat))
assert len(closures)==len(stored)==22,('incomplete collector owners',len(closures),len(stored))
rows=[]
for owner in sorted(closures):
 assert len(roots.get(owner,[]))==stored[owner],('incomplete ROOT',owner)
 terms={r['display'] for d in roots.get(owner,[]) for r in d['type_refs']+d['value_refs']}
 for coe in [False,True]:
  for b in [False,True]:
   excluded=set() if b else {'Complexity.PolyExpr.eval'}
   if coe:excluded.add('TCSlib.InformationTheory.FinDist.instCoeFunForallReal')
   names={n for n,r in cat.items() if r['home']['display'] in closures[owner]
    and r['kind']=='def' and(r['matcher'] or r['status']!='reducible') and n not in excluded}
   assert all(t in names or t in excluded or cat[t]['status']=='reducible' for t in terms)
   rows.append(dict(owner=owner,variant=('coe' if coe else 'strict')+'-'+('B' if b else 'A'),
    requested=len(names),matchers=sum(cat[n]['matcher'] for n in names),
    instances=sum(cat[n]['instance'] for n in names),term_names=len(terms),stored=stored[owner]))
out=Path(a.outdir);out.mkdir(parents=True,exist_ok=True)
(out/'request-counts.json').write_text(json.dumps(rows,indent=1)+'\n')
with(out/'request-counts.tsv').open('w')as f:
 f.write('owner\tvariant\trequested\tmatchers\tinstances\tterm_names\tstored\n')
 for r in rows:f.write('\t'.join(str(r[k])for k in ['owner','variant','requested','matchers','instances','term_names','stored'])+'\n')
print('Exact collector-derived requests:',len(rows),'owner/variant rows')
