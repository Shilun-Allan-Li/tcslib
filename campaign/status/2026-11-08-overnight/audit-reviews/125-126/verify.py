from pathlib import Path
import json,hashlib,subprocess,re,datetime,collections
out=Path(__file__).resolve().parent
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');X=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange');intake=Path('/private/tmp/ab34-audit-intake-v2h60oly')
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
def dump(name,d):p=out/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def copy(src,name):p=out/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(src.read_bytes())
cache={}
def git(repo,*args):return subprocess.check_output(['git','-C',str(repo),*args])
def data(repo,rev,path):
 key=(str(repo),rev,path)
 if key not in cache:cache[key]=git(repo,'show',rev+':'+path)
 return cache[key]
def leanmap(rev):
 return {r.split('\t',1)[1]:r.split()[2] for r in git(R,'ls-tree','-r',rev).decode().splitlines() if r.split('\t',1)[1].endswith('.lean')}
base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';current=git(R,'rev-parse','HEAD').decode().strip();bmap=leanmap(base);cmap=leanmap(current)
assert bmap==cmap and len(bmap)==1003
for config in ['lean-toolchain','lake-manifest.json']:
 assert data(R,base,config)==data(R,current,config)
copy(intake/'INTAKE.json','inputs/INTAKE.json')
for n in ['START-HERE.md','WORKFLOW.md']:
 copy(R/'campaign/maintainer'/n,'inputs/controls/'+n)
anchors=R/'campaign/status/2026-11-08-mig1-merge'
anchor=j(anchors/'object-hashes.json');assert len(anchor)==895 and j(anchors/'Lean-tree.json')==bmap
for n in ['receipt.json','object-hashes.json','Lean-tree.json']:copy(anchors/n,'inputs/MAC8/'+n)
summary=[]
for number,slug,source,owner in [(125,'word-leaves','b8bb1f194b86c1b0c1d56e6c3f57e1defec37e80','TCSlib/Complexity/CookLevin/Hardness.lean'),(126,'restart-reader','48d715acefaa9eb1c6b1ffc8656fb79cc0ab1b10','TCSlib/Complexity/TuringMachine/UniversalK.lean')]:
 prefix='campaign/gates/'+str(number)+'-'+slug;gate=R/prefix;review=gate/'review';pub=j(gate/'publication.json');adopt=j(gate/'adoption.json');report='gate'+str(number)+'-'+slug+'-findings.md';item=next(x for x in j(intake/'INTAKE.json')['files'] if x['gate']==number)
 assert sha((intake/report).read_bytes())==item['sha256'] and len((intake/report).read_bytes())==item['bytes'];copy(intake/report,str(number)+'/findings-original.md')
 assert pub['source']==source and pub['external_dispatch_confirmed']
 for repo,rev in [(R,source),(R,base),(R,pub['records']),(X,pub['exchange'])]:
  assert git(repo,'rev-parse',rev+'^{commit}').decode().strip()==rev;git(repo,'cat-file','-e',rev+'^{commit}')
 folder=pub['folder'];bundle_name=str(number)+'-'+slug+'-bundle.md';bundle=data(X,pub['exchange'],folder+'/'+bundle_name);listing=data(X,pub['exchange'],folder+'/BUNDLE-FILES.txt').decode().splitlines();assert sha(bundle)==pub['sha256'] and len(bundle)==pub['bytes'] and len(listing)==pub['sections']
 markers=list(re.finditer(rb'(?m)^## ===== (.*?) =====\n\n',bundle));assert [m[1].decode() for m in markers]==listing
 section_rows=[]
 for index,match in enumerate(markers):
  path=listing[index];rev=source if path.endswith('.lean') else pub['records'];expected=data(R,rev,path);end=markers[index+1].start() if index+1<len(markers) else len(bundle);section=bundle[match.end():end]
  wrapper=None
  if section.startswith(b'```') and not section.startswith(expected):
   first_end=section.index(b'\n')+1;wrapper=section[:first_end].decode().rstrip();fence=section[:first_end].split()[0];last=section.rfind(fence);assert last>=first_end
   assert not section[last+len(fence):].strip(b'\n')
   section=section[first_end:last]
  assert section[:len(expected)]==expected and not section[len(expected):].strip(b'\n'),path
  section_rows.append({'path':path,'revision':rev,'bytes':len(expected),'sha256':sha(expected),'code_fence_envelope':wrapper,'exact_Git_section_payload':True})
 sums=data(X,pub['exchange'],folder+'/SHA256SUMS').decode().splitlines();assert len(sums)==2
 for line in sums:
  digest,name=line.split(maxsplit=1);assert sha(data(X,pub['exchange'],folder+'/'+name.strip()))==digest
 copy(gate/'publication.json',str(number)+'/publication.json');copy(gate/'prompt.md',str(number)+'/prompt.md');copy(gate/'pack.md',str(number)+'/pack.md');copy(gate/'BUNDLE-FILES.txt',str(number)+'/BUNDLE-FILES.txt');copy(gate/'adoption.json',str(number)+'/adoption.json');copy(review/'MANIFEST.json',str(number)+'/original-MANIFEST.json')
 assert sha((gate/'prompt.md').read_bytes())==pub['prompt_sha256']
 manifest=j(review/'MANIFEST.json');assert sha((review/'MANIFEST.json').read_bytes())==adopt['review_manifest_sha256']
 payloads=[]
 for row in manifest['files']:
  saved=(review/row['path']).read_bytes();assert len(saved)==row['bytes'] and sha(saved)==row['sha256'],row['path']
  assert data(R,pub['records'],prefix+'/review/'+row['path'])==saved,row['path']
  payloads.append({'path':row['path'],'bytes':len(saved),'sha256':sha(saved),'exact_frozen_and_published_records':True})
 smap=leanmap(source);changed=[p for p in sorted(set(smap)|set(bmap)) if smap.get(p)!=bmap.get(p)];assert changed==[owner] and len(smap)==1003
 for side,pin in [('BASE',base),('HEAD',source)]:
  source_bytes=data(R,pin,owner);assert source_bytes==(review/'source'/side/(owner+'.txt')).read_bytes();copy(review/'source'/side/(owner+'.txt'),str(number)+'/source/'+side+'/'+owner+'.txt')
 # Selected raw metadata reconstruction, exact rows and per-run hashes.
 selected={};meta_runs=[]
 for side,pin in [('BASE',base),('HEAD',source)]:
  selected[side]=j(review/'metadata'/(side+'-selected.json'));raw=(review/'metadata'/(side+'.log')).read_bytes();run=j(review/'metadata'/(side+'-run.json'));assert run['exit']==0 and run['errors']==0 and run['source_pin']==pin
  raw_rows=[json.loads(line.split('ABI|',1)[1]) for line in raw.decode().splitlines() if 'ABI|' in line];assert raw_rows==selected[side]['roots']
  for key,value in run.items():
   if 'raw' in key.lower() and 'sha' in key.lower():assert value==sha(raw)
  assert run['raw_bytes']==len(raw)
  for n in [side+'-selected.json',side+'-request.json',side+'-run.json',side+'.log']:copy(review/'metadata'/n,str(number)+'/metadata/'+n)
  meta_runs.append({'side':side,'source':pin,'raw_sha256':sha(raw),'exit':run['exit'],'errors':run['errors']})
 assert selected['BASE']==selected['HEAD']
 assert not selected['BASE']['private_type_auxiliaries']
 for rootrow in selected['BASE']['roots']:assert set(rootrow['axioms'])=={'propext','Classical.choice','Quot.sound'}
 # Replay/source/object lineage.
 result=j(review/'replay/RESULT.json');request=j(review/'replay/request.json');modules=j(review/'replay/module-results.json');compiled=j(review/'replay/compiled-source-index.json');expected_modules={125:26,126:18}[number]
 assert result['pass'] and result['head']==source and result['failed']==0 and result['modules']==result['expected_modules']==expected_modules and result['static_exit']==0 and result['source_unchanged_during_replay']
 assert j(review/'replay/input-before.json')==j(review/'replay/input-after.json')==anchor
 output=j(review/'replay/output.json');assert set(output)==set(anchor) and [p for p in anchor if anchor[p]!=output[p]]==[owner[:-5]+'.olean']
 source_map=j(review/'replay/source-before.json');assert {k:v['git_blob'] for k,v in source_map.items()}==smap
 assert len(compiled)==len(modules)==expected_modules
 for row in compiled:
  actual=data(R,source,row['path']);assert sha(actual)==row['sha256'] and smap[row['path']]==row['git_blob'] and (review/row['capture']).read_bytes()==actual
 for row in modules:
  assert row['pass'] and row['exit']==row['errors']==row['sorry']==0
  assert sha((review/'replay/logs'/(row['module']+'.log')).read_bytes())==row['log_sha256']
 for n in ['RESULT.json','request.json','module-results.json','compiled-source-index.json','static.txt','static-comparison.json','object-accounting.json']:
  if (review/'replay'/n).exists():copy(review/'replay'/n,str(number)+'/replay/'+n)
 for n in ['literal-source-and-scope-binding.json','control-evidence-binding.json','selected-ABI-comparison.json','qa/source-freeze.json','screen/pair-delta.json','screen/pair-dispositions.json']:
  copy(review/n,str(number)+'/'+n)
 # Source-only exact edit reconstruction.
 old=data(R,base,owner).decode();new=data(R,source,owner).decode()
 if number==125:
  changes=j(review/'inputs/word-full-two-scopes/selected-two-chunk-mappings.json');rebuilt=old
  for change in changes:
   assert old.count(change['old_chunk'])==1 and new.count(change['new_chunk'])==1
   rebuilt=rebuilt.replace(change['old_chunk'],change['new_chunk'],1)
  assert rebuilt==new
  copy(review/'inputs/word-full-two-scopes/selected-two-chunk-mappings.json','125/exact-chunks.json')
 else:
  before=(review/'inputs/rs1/hinit-before.lean.txt').read_text();after=(review/'inputs/rs1/hinit-after.lean.txt').read_text();assert old.count(before)==1 and new.count(after)==1 and old.replace(before,after,1)==new
  for n in ['hinit-before.lean.txt','hinit-after.lean.txt','source-header-body-map.json','HinitSealed.lean.txt','control-identities.json','ControlsSealed.lean.txt','ControlsUnsealed.lean.txt','HinitSealed-run.json','ControlsSealed-run.json','ControlsUnsealed-run.json','ControlsSealed.out','ControlsUnsealed.out','HinitSealed.out']:
   copy(review/'inputs/rs1'/n,'126/rs1/'+n)
 scope=j(review/'control-evidence-binding.json')
 summary.append({'gate':number,'source':source,'owner':owner,'publication':pub,'findings_sha256':item['sha256'],'all_bundle_sections':section_rows,'all_frozen_manifest_payloads':payloads,'all1003_source_blobs_match_HEAD':True,'only_changed_Lean_path':owner,'selected_metadata_count':len(selected['BASE']['roots']),'all_selected_raw_type_universe_kernel_owner_privacy_kind_simp_AXIOM_rows_exact':True,'selected_AX_standard_only':True,'metadata_runs':meta_runs,'replay_modules':expected_modules,'all_logs_zero_exit_error_admission_and_hash_exact':True,'whole895_inputs_exact_MAC8':True,'output_only_owner_hash_changed':True,'source_exact_scope_reconstruction':True,'scope_binding':scope})
dump('VERIFICATION.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records_observed':current,'current_records_Lean_tree_all1003_exact_MAC8_BASE':True,'toolchain_and_package_lock_exact_BASE':True,'MAC8_source_and895object_anchor_matched':True,'all_gates':summary,'new_Lean_native_control_or_screen_executions_by_reviewer':0,'scope':'Published blob/source/log/metadata/control/input validation; external claimed reexecutions are their self-report, not independently attested execution here.'})
print(json.dumps({'records':current,'source_campaign_MAC8_exact':True,'verified':[{'gate':x['gate'],'source':x['source'],'sections':len(x['all_bundle_sections']),'payloads':len(x['all_frozen_manifest_payloads']),'metadata':x['selected_metadata_count'],'replay':x['replay_modules']} for x in summary]}))
