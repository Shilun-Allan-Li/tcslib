from pathlib import Path
import json,sys,importlib.util,hashlib,subprocess,datetime
sys.dont_write_bytecode=True
P=Path('/private/tmp/mig-post234-compiled-accounting');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');ctx=json.loads((P/'preparation.json').read_text());revision=sys.argv[1];mode=sys.argv[2];assert mode in ['initial-not-final','final']and len(revision)==40
assert subprocess.check_output(['git','rev-parse',revision],cwd=R).decode().strip()==revision;subprocess.run(['git','cat-file','-e',revision+'^{commit}'],cwd=R,check=True)
spec=importlib.util.spec_from_file_location('own_source_roots',P/'source_roots.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
baseline=[];head=[];sourcepins=[]
for owner in ctx['primary_owners']+ctx['context_owners']:
 path=owner.replace('.','/')+'.lean';b=(P/'source-captures/Base'/(path+'.txt')).read_text();h=subprocess.check_output(['git','show',revision+':'+path],cwd=R).decode();baseline.extend(mod.declarations(b,path));head.extend(mod.declarations(h,path));q=P/'source-captures'/('initial-head-not-final'if mode=='initial-not-final'else mode)/(path+'.txt');q.parent.mkdir(parents=True,exist_ok=True);
 if q.exists():assert q.read_text()==h
 else:q.write_text(h)
 sourcepins.append({'path':path,'owner':owner,'source':revision,'bytes':len(h.encode()),'sha256':hashlib.sha256(h.encode()).hexdigest()})
key=lambda r:(r['path'],r['name'],r['private'])
bs={key(r):r for r in baseline};hs={key(r):r for r in head};selected={};missing=[];rehomed=[]
def add(k,reason):
 assert k in hs,k
 r=hs[k];assert r['kind']in ['lemma','theorem'],(k,r['kind']);selected.setdefault(k,{'path':r['path'],'owner':r['path'][:-5].replace('/','.'),'name':r['name'],'private':r['private'],'kind':r['kind'],'line':r['line'],'end_line':r['end_line'],'chunk_sha256':r['chunk_sha256'],'commentless_tokens_sha256':r['commentless_tokens_sha256'],'reasons':[]})['reasons'].append(reason)
for k,r in hs.items():
 if r['kind']in ['lemma','theorem']and(k not in bs or r['commentless_tokens_sha256']!=bs[k]['commentless_tokens_sha256']):add(k,'current named proof is added/changed versus actual campaign BASE')
old=json.loads((R/'campaign/fills/mig1/landing/compiled-comparison-final/source-proof-roots.json').read_text())
for r in old:
 k=(r['path'],r['name'],r['private'])
 if k in hs:add(k,'historical conservative144-source-root population retained')
 else:
  candidates=[q for q in hs if q[1:]==k[1:]]
  if len(candidates)==1:
   add(candidates[0],'historical source root in its current uniquely resolved home; approved context rehome')
   rehomed.append({'historical':k,'current':candidates[0]})
  else:missing.append(k)
targets=json.loads((R/'campaign/fills/mig1/inputs/target-admissions.json').read_text());assert len(targets)==17
for r in targets:add((r['path'],r['name'],r['private']),'original17 target')
repairs=json.loads((R/'campaign/fills/mig1/landing/post234-integration-preparation/API-BINDINGS.json').read_text())['consumer_mappings'];assert len(repairs)==14
for r in repairs:add((r['file'],r['name'],r['private']),'post234 exact14-consumer repair')
out={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':revision,'stage':mode,'campaign_base':ctx['campaign_base'],'source_pins':sourcepins,'selected_root_count':len(selected),'changed_proof_root_count':sum(any('current named proof'in v for v in r['reasons'])for r in selected.values()),'historical144_roots_missing_current_source':missing,'historical_root_rehomes':rehomed,'target_count':17,'repair_count':14,'source_named_declaration_counts':{'Base':len(baseline),'Head':len(head)},'not_a_complete_anonymous_instance_or_header_freeze_claim':True,'roots':sorted(selected.values(),key=lambda r:(r['owner'],r['name']))}
(P/(mode+'-selected-source-roots.json')).write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['roots','source_pins']},indent=2))
