# io-sprg one-pass axiom graph verifier,2026-11-18. No Lean invocation.
# Graph cases mirror Lean4.25 Lean.Util.CollectAxioms exactly, including inductive ctors.
# Propagate actual axiom identities through reverse edges to a least fixed point;
# handles cycles without dropping a component's dependencies.
import argparse,collections,hashlib,json,re,runpy
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('log');ap.add_argument('out')
ap.add_argument('--inventory',required=True);ap.add_argument('--collector-binding',required=True)
ap.add_argument('--probe-binding',required=True);a=ap.parse_args()
iv=runpy.run_path(str(Path(__file__).with_name('checkpoint_inventory.py')))
inventory=iv['load'](a.inventory)
collector=json.loads(Path(a.collector_binding).read_text())
assert collector['head']==inventory['head'] and collector['inventory_sha256']==inventory['inventory_sha256'] and set(collector['owners'])==set(inventory['owners'])
probe=json.loads(Path(a.probe_binding).read_text())
assert probe['head']==inventory['head'] and probe['inventory_sha256']==inventory['inventory_sha256']
assert probe['status']=='CURRENT_BOUND_PROBE_PASS' and probe['owners']==inventory['owners']
assert collector['environment_sha256']==probe['environment_sha256'],'collector and graph import environments differ'
assert Path(a.log).resolve()==Path(probe['log']).resolve() and hashlib.sha256(Path(a.log).read_bytes()).hexdigest()==probe['log_sha256']
prepared_path=Path(probe['prepared_binding']);assert hashlib.sha256(prepared_path.read_bytes()).hexdigest()==probe['prepared_binding_sha256']
assert hashlib.sha256((Path(inventory['root'])/(probe['probe_module']+'.lean')).read_bytes()).hexdigest()==probe['probe_sha256'],'current archived probe source differs'
prepared=json.loads(prepared_path.read_text());assert prepared['head']==inventory['head'] and prepared['inventory_sha256']==inventory['inventory_sha256'] and prepared['probe_sha256']==probe['probe_sha256']
assert 'template_sha256' in prepared and 'public_theorems' not in prepared,'not a graph probe'
p=Path(a.log);out=Path(a.out);assert not out.exists(),'preserve historical census; choose fresh out';out.mkdir(parents=True)
graph={};roots={};statements={};summary=[]
for line in p.read_text().splitlines():
 if line.startswith('GRAPH '):
  r=json.loads(line[6:]);assert r['name'] not in graph;graph[r['name']]=r
 elif line.startswith('ROOTMETA '):
  r=json.loads(line[9:]);assert r['name'] not in roots;roots[r['name']]=r
 elif line.startswith('STMT '):
  r=json.loads(line[5:]);assert r['name'] not in statements;statements[r['name']]=r
 elif line.startswith('GRAPH-COUNT '):summary.append(line)
assert len(summary)==1, 'incomplete graph command'
assert all(n in graph for n in roots), 'missing stored root'
counts=re.fullmatch(r'GRAPH-COUNT (\d+) ROOT-COUNT (\d+)',summary[0]);assert counts
assert int(counts[1])==len(graph) and int(counts[2])==len(roots),'printed graph/root counts differ'
assert all(r['module'] in inventory['owners'] for r in roots.values()),'root outside owner inventory'
byowner=collections.Counter(r['module'] for r in roots.values())
assert {m:byowner[m] for m in inventory['owners']}==collector['stored'],'all-stored owner census differs'
assert set(statements)=={n for n,r in roots.items() if not r['private'] and not r['internal']},'public type census incomplete'
axioms=sorted(n for n,r in graph.items() if r['axiom']);bits={n:1<<i for i,n in enumerate(axioms)}
parents=collections.defaultdict(set)
for n,r in graph.items():
 for c in r['refs']:
  assert c in graph, ('unknown dependency',c)
  parents[c].add(n)
state={n:bits.get(n,0) for n in graph};q=collections.deque(axioms);queued=set(q)
while q:
 c=q.popleft();queued.remove(c)
 for n in parents[c]:
  new=state[n]|state[c]
  if new!=state[n]:
   state[n]=new
   if n not in queued:q.append(n);queued.add(n)
def deps(n):return [ax for ax in axioms if state[n]&bits[ax]]
census=[dict(r,axioms=deps(n),direct_sorryAx='sorryAx' in graph[n]['refs']) for n,r in sorted(roots.items())]
(out/'stored-census.json').write_text(json.dumps(census,indent=1)+'\n')
(out/'StmtDump.jsonl').write_text(''.join(json.dumps(statements[n],ensure_ascii=False)+'\n' for n in sorted(statements)))
standard={'propext','Classical.choice','Quot.sound'}
result={'head':inventory['head'],'inventory_sha256':inventory['inventory_sha256'],
'environment_sha256':probe['environment_sha256'],'probe_binding_sha256':hashlib.sha256(Path(a.probe_binding).read_bytes()).hexdigest(),'owners':inventory['owners'],'owner_stored_counts':dict(byowner),'graph_nodes':len(graph),'stored_constants':len(roots),'public_types':len(statements),'axiom_identities':axioms,'source_log_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'root_nonstandard':[r for r in census if set(r['axioms'])-standard-{'sorryAx'}],'direct_sorry_constants':[r['name'] for r in census if r['direct_sorryAx']],'transitive_sorry_constants':[r['name'] for r in census if 'sorryAx' in r['axioms']]}
(out/'summary.json').write_text(json.dumps(result,indent=1)+'\n')
(out/'sorryAx-trace.json').write_text(json.dumps([dict(name=r['name'],module=r['module'],kind=r['kind'],direct=r['direct_sorryAx']) for r in census if 'sorryAx' in r['axioms']],indent=1)+'\n')
print({k:v for k,v in result.items() if k not in ['root_nonstandard','direct_sorry_constants','transitive_sorry_constants']})
print('NONSTANDARD',len(result['root_nonstandard']),'DIRECT_SORRY',len(result['direct_sorry_constants']),'TRANSITIVE_SORRY',len(result['transitive_sorry_constants']))
