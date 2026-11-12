from pathlib import Path
import subprocess,os,json,hashlib,shutil,datetime,sys
sys.dont_write_bytecode=True
O=Path('/private/tmp/ab34-fe-live1-final-validation');E=O/'evidence';F=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);B='9b5dcf46408db681bcbc721930ef2203fa6bc47d';H='a93d1867d6ed9700f2fd89a28092e39a45db2dd2'
def git(*a):return subprocess.check_output(['git','-C',str(F),*a])
def put(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()
assert git('rev-parse','HEAD').decode().strip()==H
assert git('rev-parse','refs/remotes/origin/codex/ab34-fe-live1').decode().strip()==H
assert not git('status','--porcelain','--untracked-files=no').strip()
subprocess.run(['git','-C',str(F),'merge-base','--is-ancestor',B,H],check=True)
paths=git('diff','--name-only',B,H,'--','*.lean').decode().splitlines();assert len(paths)==5
helpers=['devtools/seyoon/mkdownmulti.py','devtools/seyoon/mkreplay.py','devtools/seyoon/graph.py','devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','devtools/seyoon/scratch-api/slotrun.sh','scripts/lean_check_tree.sh','devtools/seyoon/scratch-api/staticsorry.py']
for p in helpers:
 d=E/'helpers'/p;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(F/p,d)
for name in ['slotrun.sh','staticsorry.py']:
 d=E/'helpers/effective-api'/name;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(S/'api'/name,d)
 assert (S/'api'/name).read_bytes()==(F/'devtools/seyoon/scratch-api'/name).read_bytes(),name
for p in ['START-HERE.md','WORKFLOW.md','HANDOFF.md']:
 d=E/'standing-context'/p;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(F/'campaign/maintainer'/p,d)
for p in ['policy.md','workflow.md','campaign/standards/TEMPLATE.md','lean-toolchain','lake-manifest.json']:
 d=E/'standing-context'/p;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(F/p,d)
for p in ['receipt.json','object-hashes.json','Lean-tree.json']:
 d=E/'baseline-adoption'/p;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(F/'campaign/status/2026-11-08-mig1-merge'/p,d)
for p in ['replay-mjoint1.log','replay-mjoint1-static.txt','replay-mjoint1.sh','order-mjoint1.txt']:
 d=E/'baseline-execution'/p;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(S/'fills/replay'/p,d)
source=[]
for p in paths:
 row={'path':p}
 for label,rev in [('BASE',B),('HEAD',H)]:
  b=git('show',f'{rev}:{p}');d=E/'source'/label/(p+'.txt');d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b)
  row[label]={'blob':git('rev-parse',f'{rev}:{p}').decode().strip(),'bytes':len(b),'sha256':sha(b)}
  if label=='HEAD':assert (F/p).read_bytes()==b
 source.append(row)
put(E/'SOURCE.json',{'base':B,'head':H,'pushed_tracking_ref':'refs/remotes/origin/codex/ab34-fe-live1','tracking_ref_exact':True,'status_tracked_clean':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':source})
alllean=[]
for rev,label in [(B,'BASE'),(H,'HEAD')]:
 rows=[]
 for line in git('ls-tree','-r',rev).decode().splitlines():
  meta,p=line.split('\t',1)
  if p.endswith('.lean'):
   blob=meta.split()[2];b=git('cat-file','blob',blob);rows.append({'path':p,'blob':blob,'bytes':len(b),'sha256':sha(b)})
 put(E/f'{label}-whole-Lean-tree.json',rows);alllean.append(rows)
assert {r['path'] for r in alllean[0]}=={r['path'] for r in alllean[1]}
changed=[r['path'] for r,s in zip(alllean[0],alllean[1]) if r!=s];assert sorted(changed)==sorted(paths)
mods=[p[:-5].replace('/','.') for p in paths];hp=E/'helpers/devtools/seyoon';lst=E/'replay-order.txt'
r=subprocess.run(['python3','-I','-B',str(hp/'mkdownmulti.py'),str(F),str(hp),str(lst),*mods],capture_output=True,check=True);(E/'mkdownmulti.out').write_bytes(r.stdout+r.stderr)
order=lst.read_text().splitlines();assert order and 'TCSlib' not in order
sys.path.insert(0,str(hp));from graph import imports_of
modsall={p[:-5].replace('/','.'):[i for i in imports_of(F/p) if i.startswith('TCSlib')] for p in git('ls-files','TCSlib/*.lean','TCSlib/**/*.lean').decode().splitlines() if p.endswith('.lean')}
pos={m.replace('/','.'):i for i,m in enumerate(order)};bad=[]
libs=[S/'oleans-mac8']+list((F/'.lake/packages').glob('*/.lake/build/lib/lean'))
for m,i in pos.items():
 for imp in modsall[m]:
  if imp in pos:
   if pos[imp]>=i:bad.append([m,imp,'listed later'])
  elif not any((lib/(imp.replace('.','/')+'.olean')).is_file() for lib in libs):bad.append([m,imp,'missing object'])
assert not bad,bad
put(E/'CLOSURE.json',{'targets':mods,'count':len(order),'order':order,'root_excluded':True,'imports_earlier_or_present':True,'full_source_graph':modsall,'whole_source_Lean_paths':len(alllean[1]),'only_five_changed':True})
pins=';'.join(r['path']+':'+r['HEAD']['blob'] for r in source)
r=subprocess.run(['python3','-I','-B',str(hp/'mkreplay.py'),str(E/'generated-mkreplay-NOT-EXECUTED.sh'),'mfe-live1-final','wt-followup','codex/ab34-fe-live1',B,'MAC8 baseline',str(lst),str(S/'fills/replay/replay-mjoint1.log'),'oleans-mac8','oleans-fe-live1-final','FE-LIVE-1 final five-owner closure',pins],capture_output=True,check=True);(E/'mkreplay.out').write_bytes(r.stdout+r.stderr)
print(json.dumps({'head':H,'owners':paths,'closure':len(order),'whole_Lean_paths':len(alllean[1]),'evidence':str(E)}),flush=True)
