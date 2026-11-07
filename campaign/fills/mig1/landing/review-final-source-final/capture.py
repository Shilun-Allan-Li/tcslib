"""Read-only exact Git/source capture for the final12-source QA."""
from pathlib import Path
import subprocess,json,hashlib,datetime,concurrent.futures
out=Path(__file__).resolve().parent;root=out.parents[4];wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-epad');phase2=out.parent/'review-final-source-phase2';tag=out.parent/'review-forward-tagged-invariant';adopt=json.loads((out.parent/'final-tag-adoption/receipt.json').read_text());old=json.loads((phase2/'capture.json').read_text());files=old['source_scope'];H=lambda b:hashlib.sha256(b).hexdigest();commands=[]
def git(*args):
 command=['git','-C',str(wt),*args];r=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True);commands.append(command);return r.stdout
hashes={'api':old['api_base'],'producer':old['producer'],'prior0d':old['prior_passed_source'],'prior429':adopt['prior_clean_head']}
for stage,sha in hashes.items():
 assert git('rev-parse','--verify',sha+'^{commit}').decode().strip()==sha;git('cat-file','-e',sha+'^{commit}')
head=git('rev-parse','HEAD').decode().strip();assert head==hashes['prior429']
changed={stage:git('diff','--name-only',sha,'--','*.lean').decode().splitlines() for stage,sha in hashes.items()}
assert set(changed['api'])==set(files) and set(changed['prior0d'])==set(old['changed_from_prior0d']) and changed['prior429']==[adopt['path']]
index=git('diff','--cached','--name-only').decode().splitlines();untracked=git('ls-files','--others','--exclude-standard','--','*.lean').decode().splitlines();assert not index and not untracked
status=git('status','--porcelain=v1','--untracked-files=all').decode()
def one(item):
 stage,sha,f=item;b=git('show',sha+':'+f);return stage,f,b
blobs={stage:{} for stage in [*hashes,'current']}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
 for stage,f,b in pool.map(one,[(stage,sha,f) for stage,sha in hashes.items() for f in files]):blobs[stage][f]=b
for f in files:blobs['current'][f]=(wt/f).read_bytes()
rows=[]
for f in files:
 row={'path':f,'stages':{}}
 for stage,tree in blobs.items():
  b=tree[f];p=out/'snapshots'/stage/(f+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);row['stages'][stage]={'sha256':H(b),'bytes':len(b),'lines':len(b.splitlines())}
 # Independently link committed429 to the entire immutable phase2 review.
 assert blobs['prior429'][f]==(phase2/'snapshots/current'/(f+'.txt')).read_bytes()
 # Earlier API/producer/0d capture agrees with freshly verified objects too.
 for stage in ['api','producer','prior0d']:assert blobs[stage][f]==(phase2/'snapshots'/stage/(f+'.txt')).read_bytes()
 if f==adopt['path']:
  assert H(blobs['current'][f])==adopt['after_sha256'];assert blobs['current'][f]==(tag/'candidate-Primitives.lean.txt').read_bytes()==(out.parent/'final-tag-adoption/after-Primitives.lean.txt').read_bytes()
 else:assert blobs['current'][f]==blobs['prior429'][f]
 rows.append(row)
for f in files:assert (wt/f).read_bytes()==blobs['current'][f]
# Existing phase2/prototype evidence is data; verify integrity without executing its scripts.
links=[]
for folder in [phase2,tag]:
 for line in (folder/'SHA256SUMS').read_text().splitlines():
  h,n=line.split('  ',1);assert H((folder/n).read_bytes())==h
 links.append({'folder':str(folder.relative_to(root)),'manifest_sha256':H((folder/'MANIFEST.json').read_bytes()),'checksums_verified':True})
cap={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'worktree':str(wt),'verified_commits':hashes,'actual_HEAD':head,'full_hash_object_verification':True,'source_scope':files,'source_count':len(files),'changed_Lean_paths_by_stage':changed,'index_changes':index,'untracked_Lean':untracked,'full_tracked_status':status,'exact12_changed_API':True,'only_final_private_Primitives_proof_doc_change_from429':True,'all12_sources_stable_two_pass':True,'fresh_Git_objects_match_immutable_phase2_at_all4_stages':True,'actual_final_Primitives_equals_passed_inert_prototype':True,'immutable_prior_evidence':links,'files':rows,'read_only_Git_commands':commands,'no_Git_mutations':True};(out/'capture.json').write_text(json.dumps(cap,indent=2)+'\n');print(json.dumps({k:v for k,v in cap.items() if k not in ['files','read_only_Git_commands','immutable_prior_evidence']},indent=2))
