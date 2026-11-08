from pathlib import Path
import base64,datetime,hashlib,io,json,os,subprocess,tarfile
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
C=json.loads((OUT/'capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest();env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
def git(*a):return subprocess.run(['git','-C',C['actual_worktree'],*a],check=True,stdout=subprocess.PIPE,env=env).stdout
assert len(C['population'])==len(set(C['population']))==25
assert C['population']==(OUT/'issued21-population.txt').read_text().splitlines()+C['added_complete_sources']
checks=[];receipts={}
for side in ['base','head']:
 pin=C[side];assert git('rev-parse',pin+'^{commit}').decode().strip()==pin;git('cat-file','-e',pin+'^{commit}')
 archive=base64.decodebytes((OUT/(side+'.tar.base64.txt')).read_bytes());assert sha(archive)==C['sides'][side]['archive_sha256'] and len(archive)==C['sides'][side]['archive_bytes']
 with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
  assert {m.name for m in tar.getmembers() if m.isfile()}==set(C['population'])
  for row in C['sides'][side]['files']:
   path=row['path'];data=(OUT/'inputs'/side/(path+'.txt')).read_bytes();assert sha(data)==row['sha256'] and len(data)==row['bytes'];assert data==(Path(C['temporary_trees'][side])/path).read_bytes()==tar.extractfile(path).read()==git('show',pin+':'+path);assert git('rev-parse',pin+':'+path).decode().strip()==row['blob'];git('cat-file','-e',row['blob']);checks.append(dict(side=side,path=path,blob=row['blob'],sha256=sha(data),all_Git_archive_inert_export_bytes_equal=True))
 receipt=json.loads((OUT/(side+'-run.json')).read_text());data=(OUT/(side+'.out')).read_bytes();assert receipt['exit']==0 and receipt['fresh_execution'] and receipt['source_commit']==pin and receipt['full_population']==25;assert (len(data),sha(data))==(receipt['bytes'],receipt['output_sha256']);assert receipt['command'][:5]==['nice','-n','10','python3','-I'] and receipt['command'][7:]==C['population'] and receipt['command'][6]==C['temporary_trees'][side];assert receipt['side_capture_sha256']==sha((OUT/(side+'-capture.json')).read_bytes());assert receipt['orchestrator_sha256']==sha((OUT/'run-side.py').read_bytes());assert receipt['script_sha256']==C['tools']['scripts/copy-text-screen-v3.py'];receipts[side]=receipt
assert sha((ROOT/'scripts/copy-text-screen-v3.py').read_bytes())==C['tools']['scripts/copy-text-screen-v3.py']
events=[json.loads(x) for x in (OUT/'lock-events.jsonl').read_text().splitlines()];release={s:next(x for x in events if x['side']==s and x['event']=='released') for s in ['base','head']};launch={s:next(x for x in events if x['side']==s and x['event']=='launched') for s in ['base','head']};assert datetime.datetime.fromisoformat(release['base']['utc'])<datetime.datetime.fromisoformat(launch['head']['utc'])
assert datetime.datetime.fromisoformat(receipts['base']['end_utc'])<datetime.datetime.fromisoformat(receipts['head']['start_utc'])
prior=json.loads((OUT.parent/'prior-evidence-before.json').read_text());preserved=[]
for old in prior:
 folder=Path(old['folder']);now=[dict(path=str(p.relative_to(folder)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(folder.rglob('*')) if p.is_file()];assert now==old['files'];preserved.append(dict(folder=str(folder),files=old['file_count'],all_paths_and_bytes_preserved=True))
assert not (OUT.parent/'base-run.json').exists() and not (OUT.parent/'base.out').exists()
actual=git('rev-parse','HEAD').decode().strip();upstream=git('rev-parse','@{upstream}').decode().strip();assert actual==upstream and not git('status','--porcelain').strip();assert not git('diff','--no-ext-diff','--no-textconv','--name-only',C['head'],actual,'--','*.lean').strip()
for row in C['sides']['head']['files']:assert (Path(C['actual_worktree'])/row['path']).read_bytes()==(OUT/'inputs/head'/(row['path']+'.txt')).read_bytes()
assert sha((Path(C['actual_worktree'])/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes())=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3'
ps=subprocess.run(['ps','-axo','pid=,command='],check=True,stdout=subprocess.PIPE,text=True).stdout;active=[]
for line in ps.splitlines():
 p=line.strip().split(None,1)
 if len(p)==2 and Path(p[1].split()[0]).name.casefold().startswith('python') and 'copy-text-screen-v3.py' in p[1]:active.append(line)
assert not any(line.strip().split()[0] in [str(receipts[s]['pid']) for s in receipts] for line in active)
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen';lockstate=dict(exists=lock.exists(),files={p.name:p.read_text() for p in lock.iterdir() if p.is_file()} if lock.exists() else {})
if lock.exists():assert (lock/'pid').read_text().strip() not in [str(receipts[s]['pid']) for s in receipts]
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=C['base'],head=C['head'],population=25,fresh_BASE_and_HEAD_exit0=True,no_old_BASE_adoption=True,all50_full_sources_Git_archive_inert_export_equal=True,immutable_side_capture_and_runner_hashes_equal=True,source_tool_unchanged=True,BASE_release_before_HEAD_launch=True,both_shared_lock_release_events=release,prior_evidence_preserved=preserved,prepared23_never_executed=True,actual_clean_pushed_worktree_head=actual,current_entire_Lean_tree_equals_screen_HEAD=True,current25_worktree_sources_equal_captures=True,owner550c59_unchanged=True,own_screen_PIDs_gone=True,current_other_active_screen_rows=active,current_screen_lock=lockstate,all_source_rows=checks)
(OUT/'final-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='all_source_rows'},indent=2))
