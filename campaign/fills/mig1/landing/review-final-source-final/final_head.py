from pathlib import Path
import json,hashlib,subprocess,os,datetime
out=Path(__file__).resolve().parent;cap=json.loads((out/'capture.json').read_text());p=out.parent/'final-tag-adoption/pushed.json';push=json.loads(p.read_text());wt=Path(cap['worktree']);commands=[];env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):
 command=['git','-C',str(wt),*args];r=subprocess.run(command,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True);commands.append(command);return r.stdout
head=push['head'];assert git('rev-parse','--verify',head+'^{commit}').decode().strip()==head;git('cat-file','-e',head+'^{commit}');assert git('rev-parse','HEAD').decode().strip()==head
campaign=push['campaign_base'];assert git('rev-parse','--verify',campaign+'^{commit}').decode().strip()==campaign;git('cat-file','-e',campaign+'^{commit}')
status=git('status','--porcelain=v1','--untracked-files=all').decode();assert not status;assert not git('diff','--cached','--name-only').strip();assert not git('ls-files','--others','--exclude-standard','--','*.lean').strip()
changed=git('diff','--name-only',cap['verified_commits']['api'],head,'--','*.lean').decode().splitlines();prchanged=git('diff','--name-only',campaign+'...'+head,'--','*.lean').decode().splitlines();assert set(changed)==set(cap['source_scope'])==set(prchanged)==set(push['changed_Lean_mergebase'])
rows=[]
for r in cap['files']:
 f=r['path'];actual=(wt/f).read_bytes();committed=git('show',head+':'+f);captured=(out/'snapshots/current'/(f+'.txt')).read_bytes();assert actual==committed==captured;assert H(actual)==push['all_source_SHA256'][f]==r['stages']['current']['sha256'];rows.append({'path':f,'sha256':H(actual),'actual_equals_committed_equals_reviewed':True})
result={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'current_clean_pushed_head':head,'full_commit_object_verified':True,'campaign_base':campaign,'full_campaign_object_verified':True,'working_tree_status':status,'index_clean':True,'untracked_Lean':[],'exact12_changed_Lean_from_API':changed,'exact12_PR_mergebase_changed_Lean':prchanged,'all12_final_commit_actual_and_reviewed_bytes_equal':True,'source_blobs':rows,'pushed_receipt_sha256':H(p.read_bytes()),'read_only_Git_commands':commands,'GIT_OPTIONAL_LOCKS':'0','no_Git_mutations':True};(out/'final-head.json').write_text(json.dumps(result,indent=2)+'\n');print('Verified cleanpushed',head,';12committed/actual/captured sources byteequal;12API+PRchangedpaths.')
