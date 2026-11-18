# io-sprg one-pass axiom graph verifier,2026-11-18. No Lean invocation.
# Graph cases mirror Lean4.25 Lean.Util.CollectAxioms exactly, including inductive ctors.
# Propagate actual axiom identities through reverse edges to a least fixed point;
# handles cycles without dropping a component's dependencies.
import argparse,collections,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('log');ap.add_argument('out');a=ap.parse_args()
p=Path(a.log);out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
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
result={'graph_nodes':len(graph),'stored_constants':len(roots),'public_types':len(statements),'axiom_identities':axioms,'source_log_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'root_nonstandard':[r for r in census if set(r['axioms'])-standard-{'sorryAx'}],'direct_sorry_constants':[r['name'] for r in census if r['direct_sorryAx']],'transitive_sorry_constants':[r['name'] for r in census if 'sorryAx' in r['axioms']]}
(out/'summary.json').write_text(json.dumps(result,indent=1)+'\n')
(out/'sorryAx-trace.json').write_text(json.dumps([dict(name=r['name'],module=r['module'],kind=r['kind'],direct=r['direct_sorryAx']) for r in census if 'sorryAx' in r['axioms']],indent=1)+'\n')
print({k:v for k,v in result.items() if k not in ['root_nonstandard','direct_sorry_constants','transitive_sorry_constants']})
print('NONSTANDARD',len(result['root_nonstandard']),'DIRECT_SORRY',len(result['direct_sorry_constants']),'TRANSITIVE_SORRY',len(result['transitive_sorry_constants']))
