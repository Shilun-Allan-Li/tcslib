from pathlib import Path
import json,subprocess,hashlib,re,ast
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/gates/122-first-halt-reuse/review';g=lambda *a:subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a]);H=lambda b:hashlib.sha256(b).hexdigest();base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';head='f3c8c050ef98375bc237c72bde74f83d33833374';e0b='e0b7fd50ca81d9b8f3dd486f120292da1b4fb880'
helper=R/'devtools/seyoon/declfreeze.py';tree=ast.parse(helper.read_text());allowed={'KW','DECL','ANON','STOP','SCOPE'};nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(t,ast.Name) and t.id in allowed for t in n.targets)];ns={'re':re};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns)
freeze=json.loads((P/'HEADER-FREEZE13.json').read_text());owners=sorted({r['path'] for r in freeze});assert len(owners)==8;changed=g('diff','--name-only',base,head,'--','*.lean').decode().splitlines();assert sorted(changed)==owners;checks=[];rootchecks=[]
for owner in owners:
 a=g('show',base+':'+owner).decode();b=g('show',head+':'+owner).decode();A={n:(pr,t) for n,pr,t in ns['chunks'](a)};B={n:(pr,t) for n,pr,t in ns['chunks'](b)};assert set(A)==set(B);rows=[r for r in freeze if r['path']==owner];names=[];recovered=b
 for row in rows:
  matches=[n for n in A if n==row['name'] or n.endswith('.'+row['name'])];assert len(matches)==1,(owner,row['name'],matches);n=matches[0];names.append(n);ac=A[n][1];bc=B[n][1];assert ac[:ac.index(':=')]==bc[:bc.index(':=')]==row['literal_complete_header'];assert H(ac.encode())==row['BASE_chunk_sha256'] and H(bc.encode())==row['HEAD_chunk_sha256'];assert bc== (P/'source-review13/chunks'/str(row['id'])/'HEAD.lean.txt').read_text();assert ac==(P/'source-review13/chunks'/str(row['id'])/'BASE.lean.txt').read_text();assert recovered.count(bc)==1;recovered=recovered.replace(bc,ac,1);d=O/'selected-chunks'/str(row['id']);d.mkdir(parents=True,exist_ok=True);(d/'BASE.lean.txt').write_text(ac);(d/'HEAD.lean.txt').write_text(bc);rootchecks.append({'id':row['id'],'owner':owner,'kernel_source_name':n,'BASE_line':a[:a.index(ac)].count('\n')+1,'HEAD_line':b[:b.index(bc)].count('\n')+1,'literal_header_exact':True,'BASE_sha256':H(ac.encode()),'HEAD_sha256':H(bc.encode())})
 assert sorted(n for n in A if A[n]!=B[n])==sorted(names);assert recovered==a
 for side,s in [('BASE',a),('HEAD',b)]:
  p=O/'source'/side/(owner+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 checks.append({'path':owner,'BASE_blob':g('rev-parse',base+':'+owner).decode().strip(),'HEAD_blob':g('rev-parse',head+':'+owner).decode().strip(),'BASE_sha256':H(a.encode()),'HEAD_sha256':H(b.encode()),'public':sum(not x[0] for x in A.values()),'private':sum(x[0] for x in A.values()),'exact_all_body_reversal_recovers_BASE':True,'targets':names})
assert sum(c['public'] for c in checks)==106 and sum(c['private'] for c in checks)==1288
maps=[]
for side,rev in [('BASE',base),('HEAD',head),('E0B',e0b)]:
 m={}
 for row in g('ls-tree','-r',rev).decode().splitlines():
  spec,p=row.split('\t',1)
  if p.endswith('.lean'):m[p]=spec.split()[2]
 assert len(m)==1003;assert m==json.loads((P/'inputs/current77'/f'{side}-ALL-LEAN-BLOBS.json').read_text());maps.append({'side':side,'rev':rev,'tracked_Lean_blob_count':len(m),'entire_map_matches':True})
heldorig=json.loads((P/'inputs/historical-fh10-e0b/inputs/final403/CURRENT-DISPOSITIONS17.json').read_text());held=[]
for row in heldorig:
 if row['id'] not in [50,51,52,58,82,83,84]:continue
 owner=row['path'];a=g('show',base+':'+owner);b=g('show',head+':'+owner);assert a==b;C={n:t for n,pr,t in ns['chunks'](b.decode())};matches=[n for n in C if n==row['name'] or n.endswith('.'+row['name'])];assert len(matches)==1;chunk=C[matches[0]];line=b.decode()[:b.decode().index(chunk)].count('\n')+1;d=O/'held-source'/(str(row['id'])+'-'+row['name']);d.mkdir(parents=True,exist_ok=True);(d/'CURRENT-full-chunk.lean.txt').write_text(chunk);(d/'CURRENT-owner.lean.txt').write_bytes(b);args=[]
 for i,l in enumerate(chunk.splitlines()):
  if re.search(r'\b(simp|simpa|dsimp|rw|unfold|delta)\b',l):args.append({'line':line+i,'source':l})
 held.append({'id':row['id'],'path':owner,'name':matches[0],'actual_current_chunk_sha256':H(chunk.encode()),'actual_current_line':line,'whole_owner_BASE_exact':True,'whole_owner_SHA256':H(b),'historical_proposal_guard_execution_not_current_baseline_guard':True,'historical_reason':row['reason'],'explicit_commands_in_current_BASE_exact_chunk':args,'historical_foreign_arguments':row['explicit_foreign_definition_args'],'no_acknowledgment_inferred':True})
for side,rev in [('BASE',base),('HEAD',head)]:
 pop=(P/'screen-population.txt').read_text().splitlines();assert len(pop)==len(set(pop))==44
 for owner in pop:
  b=g('show',rev+':'+owner);p=P/'source'/side/(owner+'.txt');assert b==p.read_bytes(),(side,owner)
r={'BASE':base,'HEAD':head,'E0B':e0b,'owners':checks,'roots':rootchecks,'all13_exact_headers_and_complete_body_reversal':True,'public':106,'private':1288,'all1003_source_maps':maps,'held7':held,'all44_BASE_HEAD_screen_sources_Git_exact':True,'no_source_Git_canonical_mutation':True};(O/'SOURCE-VERIFICATION.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'owners':len(checks),'roots':len(rootchecks),'public':106,'private':1288,'all_body_reversal':True,'source_maps':maps,'held7_whole_owner_BASE_exact':len(held),'full44_source_bindings':True},indent=2))
