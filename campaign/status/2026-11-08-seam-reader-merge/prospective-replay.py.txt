"""Merged-tree replay with one full overlay and dependency-gated Lean jobs."""
from concurrent.futures import FIRST_COMPLETED,ThreadPoolExecutor,wait
from pathlib import Path
import datetime,hashlib,json,os,runpy,shutil,subprocess,sys,tarfile,time
cfg=json.loads(Path(sys.argv[1]).read_bytes())
R=Path(cfg['repository']).resolve();S=Path(os.environ['TCSLIB_SCRATCH'])
I=S/cfg['input_snapshot'];O=S/cfg['output_snapshot'];E=Path(cfg['evidence'])
assert not E.exists() and not O.exists();E.mkdir()
W=E/'runtime';W.mkdir()
def save(name,x):(E/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def rev(r):
 h=git('rev-parse',r).decode().strip();git('cat-file','-e',h+'^{commit}');return h
def om(root):return {p.relative_to(root).as_posix():sha(p.read_bytes()) for p in sorted(root.rglob('*.olean'))}
h=rev(cfg['head_ref']);b=rev(cfg['baseline']);r=rev('origin/complexity/arora-barak-ch3-4')
assert h==rev(cfg['head'])
assert not git('diff','--name-only',b,r,'--','*.lean')
mt=subprocess.run(['git','-C',str(R),'merge-tree','--write-tree',r,h],capture_output=True,check=True)
tree=mt.stdout.decode().splitlines()[0];git('cat-file','-e',tree+'^{tree}')
(E/'prospective-merge.txt').write_bytes(mt.stdout+mt.stderr)
changes=git('diff','--name-only',b,tree,'--','*.lean').decode().splitlines()
assert changes and changes==cfg['expected_owners']
lean_blobs={}
for row in git('ls-tree','-rz',tree).split(b'\0'):
 if not row:continue
 info,p=row.decode().split('\t',1)
 if p.endswith('.lean'):
  mode,kind,blob=info.split()
  assert mode=='100644' and kind=='blob'
  lean_blobs[p]=blob
assert len(lean_blobs)==1004
extra=[p for p in lean_blobs if not p.startswith('TCSlib/') and p!='TCSlib.lean']
archive=subprocess.Popen(
 ['git','-C',str(R),'archive','--format=tar',tree,'TCSlib','TCSlib.lean',
  'lean-toolchain','lake-manifest.json','devtools/seyoon',*extra],stdout=subprocess.PIPE)
with tarfile.open(fileobj=archive.stdout,mode='r|') as contents:
 contents.extractall(W,filter='data')
assert archive.wait()==0
(W/'.lake').mkdir()
(W/'.lake/packages').symlink_to((Path(os.environ['TCSLIB_REPO'])/'.lake/packages').resolve(),target_is_directory=True)
for name in ('lean-toolchain','lake-manifest.json'):
 assert (W/name).read_bytes()==git('show',b+':'+name)
def sm():
 result={}
 for path,blob in sorted(lean_blobs.items()):
  raw=(W/path).read_bytes()
  assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blob
  result[path]={'sha256':sha(raw),'blob':blob,'bytes':len(raw)}
 return result
api=S/'api/staticsorry.py';assert b'module_plan' in api.read_bytes()
dev=W/'devtools/seyoon'
for src,name in [(dev/x,x) for x in ('graph.py','mkdownmulti.py','leanelab.sh','leanelab-o.sh')]+[(api,'staticsorry.py'),(Path(__file__),'driver.py')]:
 shutil.copyfile(src,E/name)
tools=['python3','-I',str(dev/'mkdownmulti.py'),str(W),str(dev),str(E/'down.txt')]
result=subprocess.run(tools+[p[:-5].replace('/','.') for p in changes],capture_output=True,check=True)
(E/'plan.log').write_bytes(result.stdout+result.stderr)
mods=(E/'down.txt').read_text().splitlines();idx={m:i for i,m in enumerate(mods)}
assert len(idx)==len(mods) and 'TCSlib' not in idx and len(mods)==int(result.stdout.strip())
source=sm();save('source-before.json',source)
imp=runpy.run_path(str(dev/'graph.py'))['imports_of']
T={p[:-5]:[x.replace('.','/') for x in imp(W/p)] for p in source if p.startswith('TCSlib/')}
deps={m:[x for x in T[m] if x in idx] for m in mods}
assert all(idx[d]<idx[m] for m in mods for d in deps[m])
assert all(m in idx or not (set(di)&set(idx)) for m,di in T.items())
objs=om(I);assert objs==json.loads(Path(cfg['input_hash_map']).read_bytes())
assert all(m+'.olean' in objs for m in mods)
pkg=[x/'.lake/build/lib/lean' for x in (W/'.lake/packages').iterdir() if (x/'.lake/build/lib/lean').is_dir()]
assert any(x.parent.parent.parent.name=='mathlib' for x in pkg) or (W/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib').is_dir()
missing=[(m,x) for m in mods for x in T[m] if x not in idx and x+'.olean' not in objs and not any((p/(x+'.olean')).is_file() for p in pkg) and x.startswith('TCSlib/')]
assert not missing,missing
# Estimate the remaining path with timings from a completed historical replay.
# Ready jobs still require receipts for every dependency in this run.
timing=Path(cfg['historical_timing'])
history=json.loads(timing.read_bytes())
cost={r['module']:max(0.2,r['seconds']) for r in history if r['pass']}
dependents={m:[] for m in mods}
for m in mods:
 for d in deps[m]:dependents[d].append(m)
rank={}
for m in reversed(mods):
 rank[m]=cost.get(m,2.0)+max((rank[d] for d in dependents[m]),default=0.0)
save('scheduling.json',{'historical_timing_sha256':sha(timing.read_bytes()),'critical_path_seconds_estimates':rank})
(E/'module-receipts').mkdir()
save('dependencies.json',{'modules':mods,'all_local_imports':{m:T[m] for m in mods},'dependency_gates':deps,'no_outside_TCSlib_importer_of_rebuilt_module':True})
save('request.json',cfg|{'baseline':b,'head':h,'campaign_records':r,'clean_prospective_tree':tree,'modules':len(mods),'whole_input_objects':len(objs),'no_snapshot_splice':True})
save('input-before.json',objs)
subprocess.run(['cp','-cR',str(I),str(O)],check=True);assert om(O)==objs
workers=min(3,int(os.environ.get('TCSLIB_LEAN_SLOTS','3')),cfg.get('workers',3));assert 1<=workers<=3
started=time.monotonic()
def one(m):
 t=time.monotonic();f=m+'.lean';sf=(W/f).read_bytes()
 assert sha(sf)==source[f]['sha256']
 z=E/'compiled-source'/(f+'.txt');z.parent.mkdir(parents=True,exist_ok=True);z.write_bytes(sf)
 for ext in ('.olean','.ilean','.c','.trace'):(O/(m+ext)).unlink(missing_ok=True)
 cmd=['bash',str(dev/'leanelab-o.sh'),str(W),str(O),f,str(O)]
 lp=E/'logs'/(m+'.log');lp.parent.mkdir(parents=True,exist_ok=True)
 with lp.open('wb') as output:pr=subprocess.run(cmd,stdout=output,stderr=subprocess.STDOUT)
 out=lp.read_bytes();p=O/(m+'.olean')
 e=out.count(b'error:');ok=pr.returncode==e==0 and p.is_file() and p.stat().st_size>0
 return {'module':m,'argv':cmd,'exit':pr.returncode,'errors':e,'sorry':out.count(b"declaration uses 'sorry'"),
  'fresh_output':p.is_file(),'log_sha256':sha(out),'compiled_source_sha256':sha(sf),'compiled_source_git_blob':source[f]['blob'],
  'start_s':t-started,'finish_s':time.monotonic()-started,'seconds':time.monotonic()-t,'pass':ok}
rows={};active={};left=set(mods);completion=[];failed=False
with ThreadPoolExecutor(max_workers=workers) as pool:
 while left or active:
  if not failed:
   ready=sorted((m for m in left if all(d in rows and rows[d]['pass'] for d in deps[m])),key=lambda m:(-rank[m],idx[m]))
   for m in ready[:workers-len(active)]:
    left.remove(m);active[pool.submit(one,m)]=m
  if not active:
   assert failed or not left,left
   break
  done,_=wait(active,return_when=FIRST_COMPLETED)
  for task in done:
   m=active.pop(task)
   row=task.result();rows[m]=row;completion.append(m);failed |= not row['pass']
   assert all(rows[d]['finish_s']<=row['start_s'] for d in deps[m])
   # Write each validated return before another module may use its output.
   row['output_sha256']=sha((O/(m+'.olean')).read_bytes()) if row['pass'] else None
   receipt=E/'module-receipts'/f'{idx[m]:04d}.json'
   temporary=receipt.with_suffix('.tmp')
   temporary.write_text(json.dumps(row,ensure_ascii=False,indent=2)+'\n')
   temporary.replace(receipt)
   save('progress.json',{'completed':len(rows),'modules':len(mods),'last':row,'active':sorted(active.values()),'failures':sum(not z['pass'] for z in rows.values())})
   if len(rows)%10==0 or failed or not left:print(len(rows),'/',len(mods),m,'PASS' if row['pass'] else 'FAIL',flush=True)
ordered=[rows[m] for m in mods if m in rows];save('module-results.json',ordered)
save('completion-order.json',completion);save('input-after.json',om(I));out=om(O);save('output.json',out)
assert om(I)==objs and set(out)==set(objs)
diff=sorted(m for m in out if out[m]!=objs[m]);assert set(diff)<={m+'.olean' for m in mods}
save('object-accounting.json',{'input_objects':len(objs),'output_objects':len(out),'input_unchanged':True,'changed_objects':diff,'changed_count':len(diff),'outside_closure_unchanged':True})
assert sm()==source
log=E/'replay.log'
log.write_text('# actual dependency-ordered replay '+h+'\n'+''.join(f'{z["module"]} exit={z["exit"]} errors={z["errors"]} sorry={z["sorry"]}\n' for z in ordered)+f'# modules={len(rows)} failed={sum(not z["pass"] for z in ordered)}\n')
check=subprocess.run(['python3','-I',str(E/'staticsorry.py'),str(W),str(log),str(E/'down.txt')],capture_output=True)
(E/'static.txt').write_bytes(check.stdout+check.stderr)
passed=len(rows)==len(mods) and not failed and check.returncode==0
save('RESULT.json',{'pass':passed,'head':h,'baseline':b,'modules':len(rows),'expected_modules':len(mods),'failed':sum(not z['pass'] for z in ordered),'static_exit':check.returncode,'inherited_admissions':sum(z['sorry'] for z in ordered),'snapshot_valid':passed,'prospective_tree':tree,'input_objects':len(objs),'output_objects':len(out),'source_unchanged':True,'workers':workers,'seconds':time.monotonic()-started})
print('REPLAY FINAL',cfg['output_snapshot'],'PASS' if passed else 'FAIL',flush=True)
sys.exit(0 if passed else 1)
