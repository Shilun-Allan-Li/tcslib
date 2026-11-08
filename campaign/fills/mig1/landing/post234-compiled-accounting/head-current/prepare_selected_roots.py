from pathlib import Path
import json,hashlib,importlib.util,sys,collections
sys.dont_write_bytecode=True
P=Path('/private/tmp/mig-post234-final-head-accounting');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');B=R/'campaign/fills/mig1/landing/post234-compiled-accounting/baseline-current';ctx=json.loads((P/'context.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
# Own previously reviewed source enumerator, copied verbatim. Source-QA files remain data.
b=(B/'source_roots.py').read_bytes();(P/'source_roots.py').write_bytes(b);spec=importlib.util.spec_from_file_location('own_current_source_roots',P/'source_roots.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
bs={};hs={}
for owner in ctx['primary_owners']+ctx['context_owners']:
 path=owner.replace('.','/')+'.lean'
 for dest,txt in [(bs,(B/'source-captures/Base'/(path+'.txt')).read_text()),(hs,(P/'source-captures/Head'/(path+'.txt')).read_text())]:
  for r in mod.declarations(txt,path):
   k=(path,r['name'],r['private'])
   # Unnamed instances are outside the proof-root list and the source public-header claim.
   if k in dest:assert r['kind']=='instance'and dest[k]['kind']=='instance',k
   dest[k]=r
key=lambda r:(r['path'],r['name'],r['private'])
changed={k for k,r in hs.items()if r['kind']in ['lemma','theorem']and(k not in bs or r['commentless_tokens_sha256']!=bs[k]['commentless_tokens_sha256'])}
qa=json.loads((P/'source-QA-data/proof-roots-current.json').read_text());qas={key(r)for r in qa};assert len(qas)==len(qa)==153 and sum(not r['private']for r in qa)==66 and sum(r['private']for r in qa)==87;assert changed==qas,{'only_own':sorted(changed-qas),'only_QA':sorted(qas-changed)}
qa_checks=[]
for r in qa:
 k=key(r);q=hs[k];assert q['kind']==r['kind']and q['line']==r['line']and r['owner']==r['path'][:-5].replace('/','.')
 qa_checks.append({'path':r['path'],'name':r['name'],'private':r['private'],'kind':r['kind'],'line':r['line'],'QA_chunk_sha256':r['declaration_chunk_sha256'],'own_complete_named_chunk_sha256':q['chunk_sha256'],'own_commentless_chunk_token_sha256':q['commentless_tokens_sha256'],'same_uniquely_identified_source_declaration':True})
selected={};rehomes=[]
def add(k,reason):
 assert k in hs,k;r=hs[k];assert r['kind']in ['lemma','theorem'],(k,r['kind'])
 row=selected.setdefault(k,{kk:r[kk]for kk in ['path','name','private','kind','line','end_line','chunk_sha256','commentless_tokens_sha256']});row['owner']=r['path'][:-5].replace('/','.');row.setdefault('reasons',[])
 if reason not in row['reasons']:row['reasons'].append(reason)
for k in sorted(changed):add(k,'actual current153 changed/added source proof population versus BASE')
old=json.loads((R/'campaign/fills/mig1/landing/compiled-comparison-final/source-proof-roots.json').read_text());assert len(old)==144
for r in old:
 k=key(r)
 if k in hs:add(k,'conservative historical144 reference retained in current exact identity')
 else:
  cs=[q for q in hs if q[1:]==k[1:]];assert len(cs)==1,(k,cs);add(cs[0],'historical reference retained in its unique current upstream-owned home');rehomes.append({'historical':list(k),'current':list(cs[0])})
targets=json.loads((R/'campaign/fills/mig1/inputs/target-admissions.json').read_text());assert len(targets)==17
for r in targets:add(key(r),'original17 targets')
repairs=json.loads((R/'campaign/fills/mig1/landing/post234-integration-preparation/API-BINDINGS.json').read_text())['consumer_mappings'];assert len(repairs)==14
for r in repairs:add((r['file'],r['name'],r['private']),'post23414 consumer repair population')
readers=json.loads((P/'source-QA-data/B1-to-HEAD.json').read_text())['all_proof_body_changes'];assert len(readers)==14
for r in readers:add(key(r),'current14 B1-to-HEAD changed proof bodies including six readers/two header transports')
exceptions=json.loads((P/'source-QA-data/approved-private-header-exceptions.json').read_text())['current_BASE_exceptions'];assert len(exceptions)==5
for r in exceptions:assert r['private'];add(key(r),'one of5 approved private-header exceptions')
roots=sorted(selected.values(),key=lambda r:(r['owner'],r['name']));save('current-selected-source-roots.json',{'source':ctx['source'],'base':ctx['base'],'actual_current_changed_roots':153,'current_changed_public':66,'current_changed_private':87,'all_current153_QA_identity_and_independent_commentaware_selection_exact':True,'selected_root_count':len(roots),'selection':'deduplicated current153 plus original17/prior144/current14consumer/currentreader/privateheader populations; retain uniquely rehomed upstream redirect reference as conservative context','historical_rehomes':rehomes,'target_count':17,'repair_count':14,'current_B1_changed_bodies_count':14,'approved_private_header_exceptions':5,'roots':roots});save('current153-source-identity-checks.json',qa_checks)
# Adapt only reviewed source-root probe population and reserved local identifier.
trusted=(B/'SourceRoots-initial-not-final.lean.txt').read_text();start=trusted.index('  let requested : List (String × String × Bool) := ');stop=trusted.index('  let kind :=',start);requested='[\n'+',\n'.join('    ('+json.dumps(r['owner'])+', '+json.dumps(r['name'])+', '+str(r['private']).lower()+')'for r in roots)+'\n  ]\n';probe=trusted[:start]+'  let requested : List (String × String × Bool) := '+requested+trusted[stop:];assert probe.count('let matches :=')==1;probe=probe.replace('let matches :=','let rootMatches :=').replace('matches.length','rootMatches.length').replace('matches.head!','rootMatches.head!');assert 'reprStr'not in probe and 'withTransparency'not in probe
(P/'CurrentSourceRoots.lean.txt').write_text(probe);project=Path(ctx['project']);(project/'Head-roots.lean').write_text(probe);save('root-job.json',[{'name':'Head-roots','side':'Head','project_file':'Head-roots.lean','evidence_file':'CurrentSourceRoots.lean.txt'}]);save('root-probe-preparation.json',{'source':ctx['source'],'root_count':len(roots),'trusted_unexecuted_initial_probe_sha256':sha((B/'SourceRoots-initial-not-final.lean.txt').read_bytes()),'new_probe_sha256':sha(probe.encode()),'changes':'exact verified current source-root population and reserved matches identifier corrected before first run','no_theorem_proof_values_rendered':True,'direct_value_constant_names_only':True,'no_imported_theorem_value_traversal':True})
print(json.dumps({'current_changed':153,'public':66,'private':87,'selected_root_union':len(roots),'rehomes':rehomes,'new_probe_sha256':sha(probe.encode())},indent=2))
