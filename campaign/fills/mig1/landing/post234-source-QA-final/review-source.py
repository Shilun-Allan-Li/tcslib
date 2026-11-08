from pathlib import Path
import ast,collections,datetime,hashlib,json,re,subprocess,types
OUT=Path(__file__).resolve().parent;ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');L=ROOT/'campaign/fills/mig1/landing';OLD=L/'review-final-source-final'
CAP=json.loads((OUT/'capture.json').read_text());FILES=CAP['owners'];sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
# Execute only selected inspected pure parser functions/regexes, never historical workflows.
cp=(OUT/'tools/compare-source.py.txt').read_text();env={'re':re};nodes=[n for n in ast.parse(cp).body if isinstance(n,ast.FunctionDef) and n.name in ['clean','norm','header','decls'] or isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in ['DECL','STOP'] for t in n.targets)];exec(compile(ast.Module(body=nodes,type_ignores=[]),'<isolated-source-parser>','exec'),env);P=types.SimpleNamespace(**env)
sg=(OUT/'tools/SG1-header-controls-source.py.txt').read_text();fn=next(n for n in ast.parse(sg).body if isinstance(n,ast.FunctionDef) and n.name=='split_proof');hn={'re':re,'clean':P.clean};exec(compile(ast.Module(body=[fn],type_ignores=[]),'<proof-header-delimiter>','exec'),hn)
old=(OUT/'tools/historical-source_review.py.txt').read_text();fn=next(n for n in ast.parse(old).body if isinstance(n,ast.FunctionDef) and n.name=='split_header');gn={'re':re,'P':P};exec(compile(ast.Module(body=[fn],type_ignores=[]),'<data-header-delimiter>','exec'),gn)
controls=ast.literal_eval(next(n.value for n in ast.parse(sg).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='controls' for t in n.targets)));cr=[]
for src,ending in controls:
 h,d,b=hn['split_proof'](src);assert d==':=' and ' '.join(P.clean(h).split()).endswith(' '.join(P.clean(ending).split()));cr.append(dict(source=src,complete_header=h,body=b,passed=True))
save('header-controls.json',dict(passed=True,cases=cr,method='Proof headers ignore leading absolute-value bars and balance named assignments/result-local lets, including nested by-valued let/letI. Data equations/where use the previous inspected generic delimiter; scores are unaffected.'))
def decls(text):
 out=[]
 for d in P.decls(text):
  raw=d['raw'];doc=re.search(r'(?m)^/(?:--|-!)',raw);raw=(raw[:doc.start()] if doc else raw).rstrip()+'\n';proof=d['kind'] in ['lemma','theorem'];h,delim,body=(hn['split_proof'] if proof else gn['split_header'])(raw)
  if proof:assert delim==':=',(d['name'],delim)
  out.append(dict(d,raw=raw,header_raw=h,delimiter=delim,body=body,body_code=P.norm(P.clean(body)),code=P.norm(P.clean(raw))))
 assert len({d['name'] for d in out})==len(out)
 return out
STAGES={stage:{f:(OUT/'inputs'/stage/(f+'.txt')).read_text() for f in FILES} for stage in CAP['pins']};D={s:{f:decls(t) for f,t in files.items()} for s,files in STAGES.items()}
for x in CAP['files']:assert sha((OUT/'inputs'/x['stage']/(x['path']+'.txt')).read_bytes())==x['sha256']
# Full source attribute commands, including multiline commands and nested annotation brackets.
def attributes(text):
 c=P.clean(text);commands=re.findall(r'(?m)^attribute\b[^\n]*(?:\n[ \t]+\S[^\n]*)*',c);anns=[]
 for m in re.finditer(r'@\[',c):
  i=m.end();depth=1;quoted=False
  while i<len(c) and depth:
   if c[i]=='"':quoted=not quoted
   elif not quoted:
    if c[i]=='[':depth+=1
    elif c[i]==']':depth-=1
   i+=1
  assert depth==0;anns.append(c[m.start():i])
 return [P.norm(x) for x in commands+anns]
def compare(left,right):
 report={};added=[];removed=[];headers=[];runtime=[];proofs=[]
 for f in FILES:
  al,bl=D[left][f],D[right][f];a={x['name']:x for x in al};b={x['name']:x for x in bl};common=a.keys()&b.keys();hc=[];rc=[];pc=[]
  for name in sorted(common):
   x,y=a[name],b[name]
   if (x['header_raw'],x['private'],x['kind'])!=(y['header_raw'],y['private'],y['kind']):
    r=dict(path=f,name=name,private=y['private'],kind=y['kind'],before=x['header_raw'],after=y['header_raw']);hc.append(r);headers.append(r)
   if x['body_code']!=y['body_code']:
    r=dict(path=f,name=name,private=y['private'],kind=y['kind'],line=y['start'],before_body_sha256=sha(x['body'].encode()),after_body_sha256=sha(y['body'].encode()))
    (pc if y['kind'] in ['lemma','theorem'] else rc).append(r);(proofs if y['kind'] in ['lemma','theorem'] else runtime).append(r)
  ad=[dict(path=f,name=x['name'],private=x['private'],kind=x['kind']) for x in bl if x['name'] not in a];rm=[dict(path=f,name=x['name'],private=x['private'],kind=x['kind']) for x in al if x['name'] not in b];added+=ad;removed+=rm
  im=lambda s:[x for x in P.clean(s).splitlines() if re.match(r'^import\s',x)]
  order=[x['name'] for x in al if x['name'] in common]==[x['name'] for x in bl if x['name'] in common]
  report[f]=dict(source_counts_before=dict(public=sum(not x['private'] for x in al),private=sum(x['private'] for x in al)),source_counts_after=dict(public=sum(not x['private'] for x in bl),private=sum(x['private'] for x in bl)),added=ad,removed=rm,header_changes=hc,runtime_body_changes=rc,proof_body_changes=pc,relative_order_preserved=order,imports_before=im(STAGES[left][f]),imports_after=im(STAGES[right][f]),attributes_equal=attributes(STAGES[left][f])==attributes(STAGES[right][f]))
 return dict(left=left,right=right,files=report,all_added=added,all_removed=removed,all_header_changes=headers,all_runtime_body_changes=runtime,all_proof_body_changes=proofs)
comparisons={n:compare(a,b) for n,a,b in [('BASE-to-HEAD','base','head'),('B1-to-HEAD','historical_final','head'),('API-to-BASE','historical_API','base')]}
for name,r in comparisons.items():save(name+'.json',r)
x=comparisons['BASE-to-HEAD'];b1=comparisons['B1-to-HEAD'];historical=read(OUT/'historical-freeze-summary.json')
# Derive complete current deltas first; only then test them against the authorized contracts.
public_added=[r for r in x['all_added'] if not r['private']];public_removed=[r for r in x['all_removed'] if not r['private']];pubcounts={s:sum(not d['private'] for ds in D[s].values() for d in ds) for s in D};privcounts={s:sum(d['private'] for ds in D[s].values() for d in ds) for s in D}
save('current-derived-public-private-counts.json',dict(public_counts=pubcounts,private_counts=privcounts,current_public_added=public_added,current_public_removed=public_removed,current_private_header_changes=x['all_header_changes'],scope='Actual complete current twelve-owner parse, computed before authorized-set assertions; source counts only, not compiled/generated census.'))
expected_add=set(historical['public_added_API']);expected_remove=set((ROOT/'campaign/fills/mig1/inputs/retired-public-names.txt').read_text().splitlines());assert {r['name'] for r in public_added}==expected_add;assert {r['name'] for r in public_removed}==expected_remove
assert not [r for r in x['all_header_changes'] if not r['private']]
for f,r in x['files'].items():assert r['relative_order_preserved'] and r['attributes_equal'],f
# Current HEAD runtime declarations are exactly historical final B1; baseline runtime exactly historical API.
bridges=[]
for older,newer in [('historical_API','base'),('historical_final','head')]:
 for f in FILES:
  a={d['name']:d for d in D[older][f] if d['kind'] not in ['lemma','theorem']};b={d['name']:d for d in D[newer][f] if d['kind'] not in ['lemma','theorem']};assert set(a)==set(b),(older,newer,f,'runtime membership')
  assert all((a[n]['private'],a[n]['kind'],a[n]['code'])==(b[n]['private'],b[n]['kind'],b[n]['code']) for n in a),(older,newer,f,'runtime code')
  bridges.append(dict(older=older,newer=newer,path=f,runtime_declarations=len(a),all_full_code_tokens_privacy_kind_identical=True))
# Reverify all original private moves and only the two final embedding proof-field exceptions.
prims='TCSlib/Complexity/TuringMachine/Build/Primitives.lean';cat='TCSlib/Complexity/TuringMachine/Build/Catalog.lean';basecat={d['name']:d for d in D['base'][cat]};headmaps={f:{d['name']:d for d in ds} for f,ds in D['head'].items()};oldmoves=historical['original_private_runtime_moves']
actual_private_data={(r['path'],r['name']) for r in x['all_added'] if r['private'] and r['kind'] not in ['lemma','theorem']};assert actual_private_data=={(r['target_home'],r['target']) for r in oldmoves}
def renamed(s):
 s=re.sub(r'\bf2_condHeads\b','timedHeads',s);s=re.sub(r'\ba2_MapState\b','FwdMapState',s);s=re.sub(r'\ba2_map([\w\']*)',r'fwdMap\1',s);s=re.sub(r'\bf2_', '',s);return P.norm(P.clean(s))
moves=[]
for r in oldmoves:
 a=basecat[r['source']];b=headmaps[r['target_home']][r['target']];assert renamed(a['raw'])==b['code'];moves.append(dict(r,current_code_identical_modulo_approved_rename=True))
inj=[];allowed_inj={'Turing.FinTM.emitterP2SmallIndex','Turing.FinTM.emitterP2PairIndex'};assert {r['name'] for r in x['all_runtime_body_changes']}==allowed_inj
for n in allowed_inj:
 a=next(d for d in D['base'][prims] if d['name']==n)['raw'];b=headmaps[prims][n]['raw'];needle="  inj' := by";assert a.count(needle)==b.count(needle)==1;aa=a[:a.index(needle)];bb=b[:b.index(needle)];assert aa==bb;assert not re.search(r'^  [A-Za-z_]\w*\s*:=',b[b.index(needle):].split('\n',1)[1],re.M);inj.append(dict(name=n,only_final_Prop_inj_field_masked=True,header_toFun_data_prefix_bytes_identical=True,prefix_sha256=sha(aa.encode())))
allowedimports={tuple(r) for r in historical['imports_only_two_preapproved_API_edges']};actualimports=set()
for f,r in x['files'].items():
 assert not set(r['imports_before'])-set(r['imports_after']);actualimports|={(f,z) for z in set(r['imports_after'])-set(r['imports_before'])}
 assert b1['files'][f]['imports_before']==b1['files'][f]['imports_after']
assert actualimports==allowedimports
# Bind exact approved new full private headers and their existing equality evidence as data.
approval=read(L/'post234-reader-repairs-applied/approval.json');checks=read(L/'post234-consumer-seals/FINAL-CHECKS.json');assert approval['answer']=='Approve equivalent private transports (Recommended)';equivalences=checks['original_proposed_header_equalities'];approved=[]
expected_new={('TCSlib/Complexity/TuringMachine/Composition.lean','Turing.FinTM.condTM_start'),('TCSlib/Complexity/TuringMachine/Build/Wrappers.lean','Turing.FinTM.timed_start')}
assert {(r['path'],r['name']) for r in b1['all_header_changes']}==expected_new and all(r['private'] for r in b1['all_header_changes'])
for e in equivalences:
 f=e['file'];name='Turing.FinTM.'+e['theorem'];r=next(z for z in b1['all_header_changes'] if z['path']==f and z['name']==name)
 get=lambda h:re.sub(r'^private lemma\s+'+re.escape(e['theorem'])+r'\s*','',h).strip()
 assert get(r['before'])==e['old_header'] and get(r['after'])==e['new_header'];assert sha(get(r['before']).encode())==e['old_header_sha256'] and sha(get(r['after']).encode())==e['new_header_sha256'];approved.append(dict(path=f,name=name,old_complete_header=r['before'],new_complete_header=r['after'],approval=approval['answer'],equality_preflight_report=e['identity'],source_headers_match_exact_preflight=True,execution_attribution='Existing root/other-agent kernel-rfl preflight, not rerun here.'))
expected_private={(f,n) for f,n,p in historical['private_header_changes_API']}|expected_new;assert {(r['path'],r['name']) for r in x['all_header_changes']}==expected_private
save('approved-private-header-exceptions.json',dict(current_BASE_exceptions=x['all_header_changes'],new_B1_exceptions=approved,approval_record='campaign/fills/mig1/landing/post234-reader-repairs-applied/approval.json',approval_record_sha256=sha((L/'post234-reader-repairs-applied/approval.json').read_bytes()),prior_three_private_expressions=historical['private_header_changes_API'],no_new_public_statement_or_API=True))
# Gated forwarding machine/table/headers, admission fates and documentation-only WordSize.
contract=decls((ROOT/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text());exports=[]
for d in contract:
 h=headmaps[prims][d['name']];assert P.norm(d['header_raw'])==P.norm(h['header_raw']);
 if d['kind'] not in ['lemma','theorem']:assert d['body_code']==h['body_code']
 exports.append(dict(name=d['name'],kind=d['kind'],complete_header_matches_gated=True,table_body_matches_gate=d['kind'] not in ['lemma','theorem']))
targets=read(ROOT/'campaign/fills/mig1/inputs/target-admissions.json');baseline=read(ROOT/'campaign/fills/mig1/inputs/base-admissions.json');admissions=[]
for r in baseline:
 f,n=r['path'],r['name'];a=next(d for d in D['base'][f] if d['name']==n);b=headmaps[f][n];target=any(t['name']==n for t in targets);remaining=bool(re.search(r'\b(?:sorry|admit)\b',b['body_code']));assert a['header_raw']==b['header_raw'];assert not remaining if target else remaining and a['body']==b['body'];admissions.append(dict(path=f,name=n,target=target,remaining=remaining,header_exact=True,residual_body_exact=None if target else True))
remaining=[dict(path=f,name=d['name'],line=d['start']) for f in FILES for d in D['head'][f] if re.search(r'\b(?:sorry|admit)\b',d['body_code'])];assert len(remaining)==3 and sum(x['target'] for x in admissions)==17
word='TCSlib/Complexity/RAMSimulation/WordSize.lean';assert P.norm(P.clean(STAGES['base'][word]))==P.norm(P.clean(STAGES['head'][word]))
save('runtime-import-admission-freeze.json',dict(runtime_bridges=bridges,private_runtime_moves=moves,only_runtime_differences=inj,attributes_all_identical=True,imports_only_existing_two=sorted(actualimports),forwarding_contracts=exports,targets_and_residuals=admissions,remaining_static_admissions=remaining,WordSize_all_code_tokens_identical=True,scope='Current BASE/HEAD runtime/data/table/import/source checks, with every historical runtime-fate premise revalidated. No new Lean/kernel assertion.'))
# All public names include source owner/privacy/kind/order/header; no counts from a prior generation are assumed.
public={s:{d['name']:(f,d) for f,ds in D[s].items() for d in ds if not d['private']} for s in ['base','head']}
for name in public['base'].keys()&public['head'].keys():
 f,a=public['base'][name];g,b=public['head'][name];assert f==g and (a['kind'],a['header_raw'])==(b['kind'],b['header_raw'])
roots=[]
for r in x['all_proof_body_changes']+[dict(z,change='new-proof') for z in x['all_added'] if z['kind'] in ['lemma','theorem']]:
 d=headmaps[r['path']][r['name']];roots.append(dict(r,owner=r['path'].removesuffix('.lean').replace('/','.'),line=d['start'],end=d['end'],header_sha256=sha(d['header_raw'].encode()),body_sha256=sha(d['body'].encode()),body_token_sha256=sha(d['body_code'].encode()),declaration_chunk_sha256=sha(d['raw'].encode())))
save('proof-roots-current.json',roots)
save('source-inventory-current-full.json',{s:{f:[dict(name=d['name'],private=d['private'],kind=d['kind'],line=d['start'],end=d['end'],header=d['header_raw'],delimiter=d['delimiter'],code_sha256=sha(d['code'].encode()),body_token_sha256=sha(d['body_code'].encode())) for d in ds] for f,ds in tree.items()} for s,tree in D.items()})
summary=dict(completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=CAP['pins']['base'],head=CAP['pins']['head'],result='PASS full12 source/public/header/runtime/import/admission checks',owners=len(FILES),full_sources=48,public_counts=pubcounts,private_counts=privcounts,current_public_added=public_added,current_public_removed=public_removed,all_surviving_public_headers_homes_privacy_kinds_order_frozen=True,private_header_changes_current_BASE=len(x['all_header_changes']),new_approved_private_header_transports=len(approved),new_B1_runtime_data_changes=0,proof_roots_current=len(roots),proof_roots_public=sum(not r['private'] for r in roots),proof_roots_private=sum(r['private'] for r in roots),original_private_runtime_moves=len(moves),existing_Prop_inj_exceptions=len(inj),new_consumer_reader_repair_API_or_imports=0,admissions_filled=17,unchanged_RAM_residuals=3,controls=len(cr),native_execution='None by this source task; current root native3/replay/seal evidence separate.',screen_execution='Concurrent finalHEAD screen owned separately; this QA does not assert its result.')
save('summary.json',summary);print(json.dumps(summary,indent=2))
