"""Independently reconcile every native owner row and ALLAX/PUBLICAX closure."""
from pathlib import Path
import collections,datetime,gzip,hashlib,json,re
out=Path(__file__).resolve().parent;root=out.parents[4]
H=lambda b:hashlib.sha256(b).hexdigest()
def write(n,x):(out/n).write_text(json.dumps(x,indent=2)+'\n')
ctx=json.loads((out/'context.json').read_text());endpoints={}
for mode in ['base','head']:
 receipt=json.loads((out/('Inventory-'+mode+'-run.json')).read_text());log=out/('Inventory-'+mode+'.out.gz');raw=gzip.decompress(log.read_bytes())
 assert receipt['exit']==receipt['errors']==receipt['warnings']==0
 assert receipt['input_stable'] and receipt['all_five_snapshot_outputs_unchanged'] and receipt['all_five_actual_sources_stable']
 assert H(raw)==receipt['output_sha256'] and len(raw)==receipt['output_bytes']
 assert H((out/('Inventory-'+mode+'.lean.txt')).read_bytes())==receipt['input_sha256']
 tables={k:{} for k in ['CENSUS','ALLAX','PUBLICAX','TARGET','TARGETAX']};complete=[];missing=[];lines={}
 for num,line in enumerate(raw.decode().splitlines(),1):
  prefix=line.split('|',1)[0]
  if prefix in tables:
   x=json.loads(line.split('|',1)[1]);assert x['name'] not in tables[prefix];tables[prefix][x['name']]=x
   if prefix=='CENSUS':lines[x['name']]=num
  elif prefix=='COMPLETE':complete.append(int(line.split('|')[1]))
  elif prefix=='MISSING_TARGET':missing.append(line.rstrip().split('|')[1])
 assert complete==[len(tables['CENSUS'])] and set(tables['ALLAX'])==set(tables['CENSUS'])
 assert set(tables['PUBLICAX'])=={n for n,r in tables['CENSUS'].items() if not r['private']}
 assert all(r==tables['ALLAX'][n] for n,r in tables['PUBLICAX'].items())
 assert all(r==tables['CENSUS'][n] for n,r in tables['TARGET'].items())
 assert set(tables['TARGETAX'])==set(tables['TARGET'])
 assert all(r==tables['ALLAX'][n] for n,r in tables['TARGETAX'].items())
 census=tables['CENSUS'];axs=tables['ALLAX'];summary={}
 for owner in sorted({r['owner'] for r in census.values()}):
  rs=[r for r in census.values() if r['owner']==owner]
  summary[owner]={'all':len(rs),'nonprivate':sum(not r['private'] for r in rs),'nonprivate_noninternal':sum(not r['private'] and not r['internal'] for r in rs),'private':sum(r['private'] for r in rs),'kind_counts':dict(collections.Counter(r['kind'] for r in rs))}
 normalized=[]
 for n,r in sorted(census.items()):
  x=dict(r);t=x.pop('typeExpr');x.update(typeExpr_sha256=H(t.encode()),typeExpr_utf8_bytes=len(t.encode()),raw_log=log.name,raw_CENSUS_line=lines[n]);normalized.append(x)
 write('census-'+mode+'.json',{'count':len(census),'rows':normalized})
 write('allaxioms-'+mode+'.json',{'count':len(axs),'rows':[r for _,r in sorted(axs.items())]})
 write('publicaxioms-'+mode+'.json',{'count':len(tables['PUBLICAX']),'rows':[r for _,r in sorted(tables['PUBLICAX'].items())]})
 endpoints[mode]={'tables':tables,'owner_counts':summary,'receipt':receipt,'missing':missing}
a=endpoints['base']['tables']['CENSUS'];b=endpoints['head']['tables']['CENSUS'];aa=endpoints['base']['tables']['ALLAX'];ba=endpoints['head']['tables']['ALLAX']
added=sorted(b.keys()-a.keys());removed=sorted(a.keys()-b.keys());shared=sorted(a.keys()&b.keys())
source=json.loads((out/'source-reconciliation.json').read_text())
authored=set(source['authored_public_additions']);moved='Turing.FinTM.redirectTM_spaceUsedByTape'
aux=moved+'._simp_1_1';assert set(added)==authored|{aux} and not removed
classes=[]
for n in added:
 r=b[n];assert r['kind']=='theorem' and not r['private'] and not r['simp'] and not r['unfold']
 if n in authored:
  assert not r['internal'];reason='Approved authored public theorem; source declaration is new.'
 else:
  assert n==aux and r['internal'];reason='Compiler-generated proof auxiliary beneath the approved moved redirect proof; no authored source declaration or new source public helper.'
 assert set(ba[n]['axioms'])<={'propext','Classical.choice','Quot.sound'}
 classes.append({'name':n,'classification':'authored_public_addition' if n in authored else 'generated_nonprivate_internal_proof_auxiliary','owner':r['owner'],'kind':r['kind'],'private':r['private'],'internal':r['internal'],'simp':r['simp'],'unfold':r['unfold'],'axioms':ba[n]['axioms'],'reason':reason,'typeExpr_sha256':H(r['typeExpr'].encode())})
changes=[]
for n in shared:
 fields=[k for k in a[n] if a[n][k]!=b[n][k]]
 if fields:changes.append({'name':n,'fields':fields,'before':{k:a[n][k] for k in fields},'after':{k:b[n][k] for k in fields}})
assert len(changes)==1 and changes[0]['name']==moved and changes[0]['fields']==['owner']
assert a[moved]['owner']=='TCSlib.Complexity.TuringMachine.Build.Catalog' and b[moved]['owner']=='TCSlib.Complexity.TuringMachine.Build.Wrappers'
axchanges=[{'name':n,'before':aa[n]['axioms'],'after':ba[n]['axioms']} for n in shared if aa[n]['axioms']!=ba[n]['axioms']];assert not axchanges
new_sorry=[n for n in shared if 'sorryAx' not in aa[n]['axioms'] and 'sorryAx' in ba[n]['axioms']];assert not new_sorry
cleared_sorry=[n for n in shared if 'sorryAx' in aa[n]['axioms'] and 'sorryAx' not in ba[n]['axioms']];assert not cleared_sorry
allowed={'propext','Classical.choice','Quot.sound','sorryAx'}
for endpoint in endpoints.values():assert all(set(x['axioms'])<=allowed for x in endpoint['tables']['ALLAX'].values())
expected={'Turing.MultiTapeTM.exists_first_entry_of_fixed':'TCSlib.Complexity.TuringMachine.Finite','Turing.pairDiagTM_spaceUsed':'TCSlib.Complexity.TuringMachine.Encoding','Turing.FinTM.incFixedTM_spaceUsed':'TCSlib.Complexity.TuringMachine.Build.Primitives',moved:'TCSlib.Complexity.TuringMachine.Build.Wrappers'}
targets=[]
for n,home in expected.items():
 r=b[n];assert r['owner']==home and not r['private'] and not r['internal'] and not r['simp'] and not r['unfold']
 descendants=sorted(k for k in b if k.startswith(n+'.'))
 for x in [n]+descendants:assert set(ba[x]['axioms'])<={'propext','Classical.choice','Quot.sound'}
 targets.append({'root':n,'owner':home,'kind':r['kind'],'private':r['private'],'internal':r['internal'],'simp':r['simp'],'unfold':r['unfold'],'typeExpr':r['typeExpr'],'axioms':ba[n]['axioms'],'descendants':[{'name':x,'owner':b[x]['owner'],'kind':b[x]['kind'],'private':b[x]['private'],'internal':b[x]['internal'],'simp':b[x]['simp'],'unfold':b[x]['unfold'],'typeExpr':b[x]['typeExpr'],'axioms':ba[x]['axioms']} for x in descendants]})
write('targets.json',{'roots':4,'descendants':sum(len(x['descendants']) for x in targets),'targets':targets})
sorry={}
for mode,e in endpoints.items():
 c=e['tables']['CENSUS'];s=[dict(r,private=c[n]['private'],internal=c[n]['internal']) for n,r in e['tables']['ALLAX'].items() if 'sorryAx' in r['axioms']]
 sorry[mode]={'ALLAX_count':len(s),'PUBLICAX_count':sum(not x['private'] for x in s),'constants':s}
assert sorry['base']['ALLAX_count']==sorry['head']['ALLAX_count']==12
assert sorry['base']['PUBLICAX_count']==sorry['head']['PUBLICAX_count']==11
write('inherited-sorry-dependencies.json',{'endpoints':sorry,'shared_newly_sorry_dependent':new_sorry,'shared_sorry_dependencies_cleared':cleared_sorry,'note':'These are native axiom-closure counts, not a source admission census. The12 existing owner constants remain sorry-dependent; no inherited admission is cleared or accepted here.'})
write('compiled-delta.json',{'baseline_constant_count':len(a),'candidate_constant_count':len(b),'shared_count':len(shared),'added':classes,'removed':removed,'shared_metadata_changes':changes,'shared_axiom_changes':axchanges,'shared_newly_sorry_dependent':new_sorry,'shared_sorry_dependencies_cleared':cleared_sorry,'all_shared_fields_checked':list(next(iter(a.values())).keys()),'source_public_additions_count':3,'source_public_home_move_count':1,'generated_auxiliary_addition_count':1})
counts={}
for mode,e in endpoints.items():
 c=e['tables']['CENSUS'];counts[mode]={'all':len(c),'nonprivate':sum(not r['private'] for r in c.values()),'nonprivate_noninternal':sum(not r['private'] and not r['internal'] for r in c.values()),'private':sum(r['private'] for r in c.values()),'owners':e['owner_counts'],'ALLAX_count':len(e['tables']['ALLAX']),'PUBLICAX_count':len(e['tables']['PUBLICAX']),'sorry_dependent_ALLAX':sorry[mode]['ALLAX_count'],'sorry_dependent_PUBLICAX':sorry[mode]['PUBLICAX_count'],'seconds':e['receipt']['seconds'],'errors':e['receipt']['errors'],'warnings':e['receipt']['warnings']}
summary={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verdict':'PASS for this bounded native metadata comparison; no gate closure or merge clearance.','endpoints':counts,'all_owned_constants_unfiltered':True,'all_owned_constant_axioms_checked':True,'public_axioms_redundantly_reconciled_with_unfiltered_ALLAX':True,'authored_additions':3,'same_name_public_home_moves':1,'generated_nonprivate_internal_additions':1,'removed_constants':0,'shared_changed_type_kind_privacy_internal_simp_unfold_reducibility_safety_instance_protected_or_universe_parameters':0,'only_shared_owner_change':moved,'all_new_targets_and_actual_proof_descendants_standard_axioms_only':True,'formerly_proved_acquired_sorry':0,'inherited_admissions_remain':True,'no_native_failure_or_warning':True,'no_source_or_compiled_snapshot_mutation':True,'no_integrated_chain_or_replay_run_by_this_agent':True}
write('summary.json',summary);print(json.dumps(summary,indent=2))
