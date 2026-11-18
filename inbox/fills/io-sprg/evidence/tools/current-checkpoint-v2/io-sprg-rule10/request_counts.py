# io-sprg Rule10 catalog counts,2026-11-18. Adapted to the Mac managed worktree.
# Reads the collector and exact committed inventory; no Lean/cache/source mutation.
import argparse,json,hashlib,runpy
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('collector_log');ap.add_argument('outdir')
ap.add_argument('--inventory',required=True);ap.add_argument('--probe-binding',required=True);a=ap.parse_args()
iv=runpy.run_path(str(Path(__file__).resolve().parents[1]/'checkpoint_inventory.py'))
inventory=iv['load'](a.inventory);expected=set(inventory['owners'])
probe=json.loads(Path(a.probe_binding).read_text())
assert probe['status']=='CURRENT_COLLECTOR_PASS' and probe['head']==inventory['head'] and probe['inventory_sha256']==inventory['inventory_sha256']
assert probe['owners']==inventory['owners'] and Path(probe['log']).resolve()==Path(a.collector_log).resolve()
assert hashlib.sha256(Path(a.collector_log).read_bytes()).hexdigest()==probe['log_sha256']
assert hashlib.sha256((Path(inventory['root'])/(probe['probe_module']+'.lean')).read_bytes()).hexdigest()==probe['source_sha256']
cat={};roots={};closures={};stored={};cat_count=None
for line in Path(a.collector_log).read_text().splitlines():
 if line.startswith('CAT '):
  r=json.loads(line[4:]);assert r['name']['display'] not in cat;cat[r['name']['display']]=r
 elif line.startswith('ROOT '):
  r=json.loads(line[5:]);roots.setdefault(r['module'],[]).append(r)
 elif line.startswith('CLOSURE '):
  r=json.loads(line[8:]);assert r['module'] not in closures,'duplicate CLOSURE';closures[r['module']]=r['closure']
 elif line.startswith('MODULE '):
  m,c=line[7:].split(': stored ');assert m not in stored,'duplicate MODULE';stored[m]=int(c)
 elif line.startswith('CAT-COUNT '):
  assert cat_count is None,'duplicate CAT-COUNT';cat_count=int(line.split()[1])
assert cat_count==len(cat),('incomplete collector CAT',cat_count,len(cat))
assert set(closures)==set(stored)==expected,'collector owner keys differ from exact inventory'
assert set(roots)<=expected,'ROOT outside inventory'
for owner,rs in roots.items():assert len({r['name']['display'] for r in rs})==len(rs),'duplicate ROOT'
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
(out/'request-counts-binding.json').write_text(json.dumps(dict(head=inventory['head'],
 inventory_sha256=inventory['inventory_sha256'],owners=inventory['owners'],stored=stored,
 environment_sha256=probe['environment_sha256'],probe_binding_sha256=hashlib.sha256(Path(a.probe_binding).read_bytes()).hexdigest(),
 collector_log_sha256=hashlib.sha256(Path(a.collector_log).read_bytes()).hexdigest()),indent=2)+'\n')
with(out/'request-counts.tsv').open('w')as f:
 f.write('owner\tvariant\trequested\tmatchers\tinstances\tterm_names\tstored\n')
 for r in rows:f.write('\t'.join(str(r[k])for k in ['owner','variant','requested','matchers','instances','term_names','stored'])+'\n')
print('Exact collector-derived requests:',len(rows),'owner/variant rows')
