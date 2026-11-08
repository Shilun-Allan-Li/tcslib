"""Final source/output/receipt/lock and complete preservation verification; no Lean/screen."""
from pathlib import Path
import base64,datetime,hashlib,io,json,os,subprocess,tarfile
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OLD=ROOT/'campaign/fills/f6/landing/source-screen23';PARENT=OUT.parent
C=json.loads((OUT/'capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.run(['git','-C',C['actual_worktree'],*a],check=True,stdout=subprocess.PIPE).stdout
for pin in [C['base'],C['head']]:assert git('rev-parse',pin+'^{commit}').decode().strip()==pin;git('cat-file','-e',pin+'^{commit}')
assert git('rev-parse','HEAD').decode().strip()==C['head'] and git('rev-parse','@{upstream}').decode().strip()==C['head']
assert not git('status','--porcelain').strip()
assert len(C['population'])==len(set(C['population']))==23
assert C['population']==(OUT/'issued21-population.txt').read_text().splitlines()+C['added_complete_sources']
checked=[]
for side in ['base','head']:
 archive=base64.decodebytes((OUT/(side+'.tar.base64.txt')).read_bytes());assert sha(archive)==C['sides'][side]['archive_sha256'] and len(archive)==C['sides'][side]['archive_bytes']
 with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
  assert {x.name for x in tar.getmembers() if x.isfile()}==set(C['population'])
  for row in C['sides'][side]['files']:
   p=row['path'];b=(OUT/'inputs'/side/(p+'.txt')).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes']
   assert b==(Path(C['temporary_trees'][side])/p).read_bytes()==tar.extractfile(p).read()==git('show',C[side]+':'+p)
   assert git('rev-parse',C[side]+':'+p).decode().strip()==row['blob'];git('cat-file','-e',row['blob'])
   checked.append(dict(side=side,path=p,sha256=sha(b),all_Git_archive_inert_screen_export_bytes_equal=True))
 receipt=json.loads((OUT/(side+'-run.json')).read_text());output=(OUT/(side+'.out')).read_bytes();assert receipt['exit']==0 and sha(output)==receipt['output_sha256'] and len(output)==receipt['bytes']
 assert receipt['script_sha256']==C['tools']['scripts/copy-text-screen-v3.py'] and receipt['command'][7:]==C['population']
assert (OUT/'base.out').read_bytes()==(OLD/'base.out').read_bytes() and (OUT/'base-run.json').read_bytes()==(OLD/'base-run.json').read_bytes()
assert (OUT/'base-index.json').read_bytes()==(OLD/'base-index.json').read_bytes()
assert sha((ROOT/'scripts/copy-text-screen-v3.py').read_bytes())==C['tools']['scripts/copy-text-screen-v3.py']
assert sha((OUT/'run-head-only.py').read_bytes())==json.loads((OUT/'head-run.json').read_text())['orchestrator_sha256']
assert sha((Path(C['actual_worktree'])/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes())=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3'
oldfiles=[dict(path=str(p.relative_to(OLD)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(OLD.rglob('*')) if p.is_file()]
assert oldfiles==json.loads((PARENT/'original-folder-inventory-before.json').read_text())
assert not (OLD/'head-run.json').exists() and (OLD/'head.out').stat().st_size==0
stopped=json.loads((PARENT/'head-run.json').read_text());assert stopped['exit']==-15 and stopped['bytes']==0
assert json.loads((PARENT/'base-adoption.json').read_text())['adopted']
events=[json.loads(x) for x in (OUT/'lock-events.jsonl').read_text().splitlines()];assert events[-1]['event']=='released' and any(x['event']=='head_completed' and x['exit']==0 for x in events)
ps=subprocess.run(['ps','-axo','pid=,command='],check=True,stdout=subprocess.PIPE,text=True).stdout
active=[x for x in ps.splitlines() if 'copy-text-screen-v3.py' in x];assert not any(x.strip().split()[0]=='98269' for x in active)
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen';lockstate=dict(exists=lock.exists(),files={p.name:p.read_text() for p in lock.iterdir() if p.is_file()} if lock.exists() else {})
if lock.exists():assert (lock/'pid').read_text().strip() not in ['98269','98266']
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=C['base'],head=C['head'],actual_clean_pushed_source_unchanged=True,all46_Git_archive_inert_and_screen_export_sources_exact=True,all23_complete_population_preserved=True,base_receipt_and_output_exact_adoption=True,head_actual_exit0_and_output_hash_verified=True,head_runner_hash_unchanged=True,original95_files_byte_identical=True,original_interrupted_HEAD_not_completed=True,stopped_f72_generation_preserved_exit_minus15=True,actual_final_screen_PID_gone=True,shared_lock_released_event=events[-1],current_shared_lock_state=lockstate,current_active_screen_rows=active,all_verified_source_rows=checked)
(OUT/'final-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='all_verified_source_rows'},indent=2))
