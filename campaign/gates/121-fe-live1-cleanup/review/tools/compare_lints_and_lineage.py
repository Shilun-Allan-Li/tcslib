from pathlib import Path
import json,re,collections,ast,hashlib,subprocess,os
B=Path(__file__).resolve().parents[1];Q=B/'qa/lints';cfg=json.loads((B/'qa/config.json').read_text())
def styleRows(phase):
 out=[]
 for line in (Q/(phase+'-style.out')).read_text().splitlines():
  if not line.strip():continue
  key=re.sub(r'(\.lean):\d+:',r'\1:',line)
  key=re.sub(r'proof is \d+ lines','proof is <count> lines',key)
  key=re.sub(r': \d+ lines \(> 1000',': <count> lines (> 1000',key)
  out.append({'raw':line,'identity_key':key})
 return out
def campaignRows(phase):
 out=[]
 for line in (Q/(phase+'-campaign-check8b.out')).read_text().splitlines():
  m=re.match(r'^(FAIL|WARN|INFO)\s+(TCSlib/\S+\.lean)\s+(.*)',line)
  if m:
   msg=re.sub(r'^\d+ lines','<count> lines',m[3]);out.append({'level':m[1],'path':m[2],'raw':line,'identity_key':m[1]+' '+m[2]+' '+msg})
 return out
sr={p:styleRows(p)for p in ['BASE','HEAD']};cr={p:campaignRows(p)for p in ['BASE','HEAD']}
bs=collections.Counter(r['identity_key']for r in sr['BASE']);hs=collections.Counter(r['identity_key']for r in sr['HEAD']);new=hs-bs;gone=bs-hs
bc=collections.Counter(r['identity_key']for r in cr['BASE']if r['level']!='INFO');hc=collections.Counter(r['identity_key']for r in cr['HEAD']if r['level']!='INFO')
runs=json.loads((Q/'RUNS.json').read_text());assert len(sr['BASE'])==65 and len(sr['HEAD'])==64;assert not new and not(hc-bc)
result={'actual_commands_and_exits':'qa/lints/RUNS.json','scope':'four current owner files, same exact helper versions','BASE_style_findings':len(sr['BASE']),'HEAD_style_findings':len(sr['HEAD']),'BASE_style_exit':next(r['exit']for r in runs if r['phase']=='BASE'and r['kind']=='style'),'HEAD_style_exit':next(r['exit']for r in runs if r['phase']=='HEAD'and r['kind']=='style'),'style_new_identity_keys':dict(new),'style_removed_identity_keys':dict(gone),'BASE_campaign_FAIL':sum(r['level']=='FAIL'for r in cr['BASE']),'HEAD_campaign_FAIL':sum(r['level']=='FAIL'for r in cr['HEAD']),'BASE_campaign_WARN':sum(r['level']=='WARN'for r in cr['BASE']),'HEAD_campaign_WARN':sum(r['level']=='WARN'for r in cr['HEAD']),'campaign_new_issue_keys':dict(hc-bc),'normalization':'Only source line locations, file line counts, and proof-length counts are removed from issue identity; every literal row remains below. Different proof-length numbers and shifted locations remain raw observations, not new identity keys.','style_rows':sr,'campaign_rows':cr,'no_new_lint_identity_observed':True,'no_inherited_style_waiver_or_global_lint_pass_claim':True}
(Q/'COMPARISON.json').write_text(json.dumps(result,indent=2)+'\n')
# Verify exact source lineage to the already executed ordinary-definition guard inputs.
F=B/'evidence/nine-boundary';freeze=json.loads((B/'source-freeze/SOURCE-FREEZE.json').read_text());helper=B/'tools/declfreeze.py';tree=ast.parse(helper.read_text());assign={'KW','DECL','ANON','STOP','SCOPE'};nodes=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))or isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in assign for t in n.targets)];ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns)
def parts(s):return {n:t for n,_,t in ns['chunks'](s)}
def sha(x):return hashlib.sha256(x.encode()).hexdigest()
def inject(s,scopes):
 for r in sorted(scopes,key=lambda x:x['start'],reverse=True):s=s[:r['end']]+'end\n\n'+s[r['end']:];s=s[:r['start']]+r['prefix']+s[r['start']:]
 return s
rows=[]
for t in freeze['targets']:
 p=t['path'];current=(Path(cfg['HEAD_export'])/p).read_text()
 if p.endswith('/InputCall.lean'):reference=(F/'hypotheses/InputCall-field-refine.lean.txt').read_text();refPath='evidence/nine-boundary/hypotheses/InputCall-field-refine.lean.txt'
 else:reference=(F/'source'/Path(p+'.txt')).read_text();refPath='evidence/nine-boundary/source/'+p+'.txt'
 assert parts(current)[t['name']]==parts(reference)[t['name']]
 rows.append({'target':t['name'],'path':p,'current_chunk_SHA256':sha(parts(current)[t['name']]),'executed_input_chunk_SHA256':sha(parts(reference)[t['name']]),'full_literal_chunk_including_sketch_exact':True,'executed_reference':refPath})
whole=[]
for stem,path in [('EXP','TCSlib/Complexity/ClassNP/EXP.lean'),('ExhaustiveReplay','TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean')]:
 current=(Path(cfg['HEAD_export'])/path).read_text();old=(F/'source'/Path(path+'.txt')).read_text();assert current==old;sc=json.loads((F/'guards'/(stem+'-scopes.json')).read_text());guard=inject(current,sc);actual=(F/'guards'/(stem+'-full-boundary.lean.txt')).read_text();assert guard==actual
 whole.append({'owner':path,'current_full_source_exact_executed_source':True,'guard_reconstructed_exact':True,'guard_SHA256':sha(actual),'successful_run': '05-EXP-full-boundary'if stem=='EXP'else'06-XR-full-boundary'})
p='TCSlib/Complexity/CookLevin/Hardness.lean';current=(Path(cfg['HEAD_export'])/p).read_text();old=(F/'source'/Path(p+'.txt')).read_text();sc=[r for r in json.loads((F/'guards/Hardness-scopes.json').read_text())if r['target']!='clA5Compare_compute'];cut=next(r['end']for r in sc if r['target']=='clFirst');assert current[:cut]==old[:cut]
g=inject(current,sc);a=g.index('private lemma clFirst ');m=re.search(r'^end\s*$',g[a:],re.M);prefix=g[:a+m.end()]+'\n\nend Complexity\n'+'\n'+''.join('#print axioms Complexity.'+n+'\n'for n in ['clBank_first','clCopy_first','clRow_first','clCmp_first','clFirst']);assert prefix==(F/'guards/Hardness-retained5-prefix.lean.txt').read_text()
whole.append({'owner':p,'scope':'Exact full preceding source prefix through complete clFirst plus original namespace closure/selectedAX; NOT whole Hardness seal','prefix_unguarded_SHA256':sha(current[:cut]),'guard_prefix_reconstructed_exact':True,'guard_SHA256':sha(prefix),'successful_run':'12-Hardness-retained5-prefix-sealed'})
p='TCSlib/Complexity/TuringMachine/Build/InputCall.lean';current=(Path(cfg['HEAD_export'])/p).read_text();assert current==(F/'hypotheses/InputCall-field-refine.lean.txt').read_text();orig=json.loads((F/'guards/InputCall-scopes.json').read_text())[0]
m=re.search(r'^private theorem inputSeekRewind_run\b',current,re.M);start=current.rfind('/--',0,m.start());after=current.find('\n',m.start())+1;top=re.search(r'^\S.*$',current[after:],re.M);end=after+top.start();spec={**orig,'start':start,'end':end};guard=inject(current,[spec]);assert guard==(F/'hypotheses/InputCall-field-refine-sealed.lean.txt').read_text()
whole.append({'owner':p,'current_full_source_SHA256':sha(current),'guard_reconstructed_exact':True,'guard_SHA256':sha(guard),'successful_runs':['10-InputCall-field-reader-native','11-InputCall-field-reader-sealed']})
defs=json.loads((F/'definition-boundaries.json').read_text())['rows'];selected={r['name']for r in freeze['targets']};chosen=[r for r in defs if any(r['root'].endswith('.'+u)for u in selected)]
foreign={d['name']:d['owner']for r in chosen for d in r['foreign_definition_mentions']if d['name']in r['ordinary_foreign_definitions']};assert len(foreign)==11
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0';oldhead=json.loads((F/'source-pins.json').read_text())['head'];files=[]
for mod in sorted(set(foreign.values())):
 p=mod.replace('.','/')+'.lean';vals=[]
 for rev in [oldhead,cfg['source_head']]:vals.append(subprocess.run(['git','rev-parse',rev+':'+p],cwd=R,env=env,check=True,stdout=subprocess.PIPE).stdout.decode().strip())
 assert vals[0]==vals[1];files.append({'path':p,'old_guard_source_head_blob':vals[0],'current_d64_blob':vals[1],'entire_owner_source_exact':True})
lineage={'old_executed_guard_source':oldhead,'current_source':cfg['source_head'],'all9_full_literal_chunks_exact':True,'targets':rows,'successful_scope_inputs':whole,'ordinary_foreign_heads':foreign,'ordinary_definition_owner_source_blobs_exact':files,'ordinary_head_union':11,'paired_direct_delta_equation_goals':22,'positive_control_run':'13-retained9-controls-base','negative_control_run':'14-retained9-controls-sealed','control_outcomes':'22 positive goals pass; same22 sealed goals fail at intended sites','no_projection_or_abbrev_guards':True,'no_imported_theorem_proof_values_traversed':'Boundary inventory follows target full type/value and local definition values, plus mentioned types; imported theorem values/foreign definition values are not followed','execution_limit':'Executed scope receipts retain their original source/snapshot pins. This is exact source/material-definition lineage to current9 plus fresh current157 replay and compact ABI/AX, not relabeling old checks as a new execution.','not_whole_Hardness_seal':True,'no_global_ordinary_definition_or_type_claim':True}
(B/'source-freeze/CODE-LINEAGE.json').write_text(json.dumps(lineage,indent=2)+'\n')
print(json.dumps({'style':str(len(sr['BASE']))+'→'+str(len(sr['HEAD'])),'new_style_keys':len(new),'removed_style_keys':dict(gone),'campaign_new_keys':len(hc-bc),'current9_literal_chunks_match_executed_inputs':True,'exact_foreign_head_union':11,'paired_controls':22,'Hardness_prefix_context_exact':True}))
