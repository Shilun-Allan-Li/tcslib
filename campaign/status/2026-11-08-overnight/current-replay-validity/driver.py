from pathlib import Path
import subprocess,json,hashlib,datetime
r=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');out=Path('/private/tmp/ab34-current-replay-validity');out.mkdir(exist_ok=True);sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(r),*a],stderr=subprocess.STDOUT)
def rev(x):
 h=git('rev-parse',x).decode().strip();git('cat-file','-e',h+'^{commit}');return h
def blobs(h):
 rows={}
 for x in git('ls-tree','-r',h).decode().splitlines():
  meta,p=x.split('\t',1)
  if p.endswith('.lean'):rows[p]=meta.split()[2]
 return rows
current=rev('origin/complexity/arora-barak-ch3-4');base=rev('9b5dcf464');base_map=blobs(base);assert len(base_map)==1003 and blobs(current)==base_map
for p in ['lean-toolchain','lake-manifest.json']:assert git('show',current+':'+p)==git('show',base+':'+p)
manifest=json.loads(git('show',base+':lake-manifest.json'));math=next(p for p in manifest['packages'] if p['name']=='mathlib');pkg=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4/.lake/packages/mathlib');pkghead=subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD']).decode().strip();assert pkghead==math['rev'];subprocess.run(['git','-C',str(pkg),'cat-file','-e',pkghead+'^{commit}'],check=True);assert subprocess.run(['git','-C',str(pkg),'diff','--quiet']).returncode==0 and subprocess.run(['git','-C',str(pkg),'diff','--cached','--quiet']).returncode==0
anchor=json.loads((r/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text());snapshot=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8');physical={p.relative_to(snapshot).as_posix():sha(p.read_bytes()) for p in snapshot.rglob('*.olean')};assert len(anchor)==895 and physical==anchor
paths={122:'review/replay-current153',123:'review/replay',124:'review/replay',125:'review/replay',126:'review/replay',127:'review/replay',128:'review/evidence/actual-validation162/inputs/passed-Nlad2'};rows=[]
for n,rel in paths.items():
 g=next((r/'campaign/gates').glob(f'{n}-*'));pub=json.loads((g/'publication.json').read_text());source=rev(pub['source']);branch=next(x['branch'] for x in json.loads((r/'campaign/status/2026-11-08-overnight/queue.json').read_text())['gates'] if x['gate']==n);assert rev(branch)==rev('refs/remotes/origin/'+branch)==source
 source_map=blobs(source);p=g/rel;result=json.loads((p/'RESULT.json').read_text());request=json.loads((p/'request.json').read_text());assert result['head']==source and request['head']==source and result['pass'] and result['failed']==0 and result['static_exit']==0 and result['snapshot_valid'] and result['source_unchanged_during_replay']
 recorded=json.loads((p/'source-before.json').read_text());assert {k:v['git_blob'] for k,v in recorded.items()}==source_map
 for f in ['lean-toolchain','lake-manifest.json']:assert git('show',source+':'+f)==git('show',base+':'+f)
 target=git('merge-tree','--write-tree',current,source).decode().strip();assert len(target)==40;git('cat-file','-e',target+'^{tree}');assert blobs(target)==source_map
 before=json.loads((p/'input-before.json').read_text());after=json.loads((p/'input-after.json').read_text());assert before==after and len(before)==895
 if n==122:
  prev=g/'review/inputs/historical-fh10-e0b/replay';prior=json.loads((prev/'RESULT.json').read_text());assert prior['pass'] and prior['modules']==222 and json.loads((prev/'input-before.json').read_text())==json.loads((prev/'input-after.json').read_text())==anchor;assert before==json.loads((prev/'output.json').read_text());lineage='MAC8→whole passedFH10/222→whole passedFH13/153'
 else:assert before==anchor;lineage='MAC8→whole exact-head passed replay'
 modules=json.loads((p/'module-results.json').read_text());assert len(modules)==result['modules'] and all(x['pass'] and x['exit']==0 and x['errors']==0 for x in modules)
 output=json.loads((p/'output.json').read_text());assert len(output)==result['complete_output_objects']==(896 if n==128 else 895)
 row={'gate':n,'pr':pub['pr'],'source':source,'current_campaign_records':current,'current_campaign_Lean':base,'clean_current_merge_tree':target,'all_target_Lean_blobs_equal_actual_passed_replay':True,'tracked_source_files':len(source_map),'modules':result['modules'],'lineage':lineage,'input_objects':len(before),'output_objects':len(output),'complete_input_unchanged':True,'new_Lean_execution':False,'snapshot_composition':False,'basis':'All1003currentcampaignLeanblobs and package/toolchain matchactualMAC8; exactcurrentcleantargetsource matchespassedexecution, so records-only advance changes no material dependency.','result_sha256':sha((p/'RESULT.json').read_bytes()),'request_sha256':sha((p/'request.json').read_bytes()),'source_map_sha256':sha((p/'source-before.json').read_bytes()),'external_gate_closure_separate':True};rows.append(row);print('VALID',n,pub['pr'],result['modules'],len(source_map),flush=True)
(out/'RESULT.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':True,'current_campaign_records':current,'all1003currentLeanblobs_exactMAC8':True,'package_mathlib':pkghead,'whole_MAC8_895physical_object_hashes_equal_adopted_map':True,'new_Lean_runs':0,'gates':rows,'no_gate_closed_or_merge_performed_by_this_check':True},indent=2)+'\n')
(out/'driver.py').write_bytes(Path(__file__).read_bytes())
