# io-sprg Rule10 runner/config,2026-11-18. ROOT-ONLY EXECUTION.
# Host adaptation: fixed managed Mac worktree replaces historical /home/user/fill/tcslib.
# All Lean invocations delegate to existing runner_full.py, which acquires lean-slot.sh
# and runs foreground lean -DmaxErrors=0 WITHOUT -o, one process at a time.
# This script is staged, not executed by its preparing subagent.
import argparse,json,os,shutil,subprocess,sys,runpy
from pathlib import Path
ROOT='/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange'
BASE='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
ap=argparse.ArgumentParser();ap.add_argument('phase',choices=['collect','generate','pretest','seals','controls','summarize','scan-prepare','scan-run'])
ap.add_argument('--root',default=ROOT);ap.add_argument('--tree',required=True)
ap.add_argument('--collector-log');ap.add_argument('--rev',default='HEAD');ap.add_argument('--run',required=True)
ap.add_argument('--inventory',required=True)
a=ap.parse_args();wt=Path(a.root).resolve();home=Path(__file__).resolve().parent
T=wt/'evidence/tools/seal';G=T/'review/archived-gate10-tools'
R=wt/'evidence/rule10'/a.run;P='evidence/probes/io_sprg_'+a.run
if R.exists():assert (R/'inventory.json').exists(),'historical unbound run is immutable; choose fresh --run'
else:assert not (wt/P).exists(),'historical probe path exists; choose fresh --run'
R.mkdir(parents=True,exist_ok=True);(wt/P).mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_SLOT_TAG='io-sprg',SEAL_CHUNK='2048',SEAL_FAST_LOG='1')
iv=runpy.run_path(str(home.parent/'checkpoint_inventory.py'))
inventory=iv['load'](a.inventory,wt);assert inventory['base']==BASE
assert a.rev in ['HEAD',inventory['head']],'revision differs from committed inventory'
a.rev=inventory['head'];S=R/'static'
mods=list(inventory['owners']);files=iv['files'](inventory)
snapshot=R/'inventory.json'
if snapshot.exists():assert json.loads(snapshot.read_text())==inventory,'run inventory changed'
else:snapshot.write_text(json.dumps(inventory,indent=2)+'\n')
def cmd(argv,log=None,extra=None):
 e=dict(env);e.update(extra or {})
 if log:
  Path(log).parent.mkdir(parents=True,exist_ok=True)
  with Path(log).open('wb')as f:subprocess.run(list(map(str,argv)),cwd=wt,env=e,stdout=f,stderr=subprocess.STDOUT,check=True)
 else:subprocess.run(list(map(str,argv)),cwd=wt,env=e,check=True)
def python(script,*args,**kw):cmd(['python3','-I',script,*args],**kw)
def run_order(order,logs):python(T/'runner_full.py',wt,order,a.tree,logs)
def write_order(name,paths):
 p=R/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(''.join(str(x)+'\n'for x in paths));return p
COL=Path(a.collector_log).resolve() if a.collector_log else R/'collector-runs/mods'/(P.replace('/','_')+'_CollectHead.log')
if a.phase=='collect':
 python(home/'prepare_static.py','--root',wt,'--out',S,'--inventory',a.inventory)
 current=iv['load'](a.inventory,wt);assert current==inventory
 assert (S/'owners.txt').read_text().split()==mods and (S/'files.txt').read_text().split()==files
 python(T/'review/mkcollect.py',T/'review/NmCollect.template.lean',S/'owners.txt','io-sprg '+a.run,wt/P/'CollectHead.lean')
 binds=runpy.run_path(str(home/'environment_binding.py'));before=binds['snapshot'](a.tree,R)
 order=write_order('orders/collector.txt',[P+'/CollectHead']);run_order(order,R/'collector-runs')
 environment=binds['snapshot'](a.tree,R);assert environment==before,'collector environment changed during run'
 rows=[json.loads(x)for x in(R/'collector-runs/results.jsonl').read_text().splitlines()]
 rr=next(x for x in reversed(rows) if x.get('module')==P+'/CollectHead')
 sha=lambda p:__import__('hashlib').sha256(Path(p).read_bytes()).hexdigest()
 assert rr['rc']==rr['errors']==0 and not __import__('re').search(r'error[:(]',COL.read_text()),'collector failed'
 assert rr['source_sha256']==sha(wt/(P+'/CollectHead.lean')) and rr['log_sha256']==sha(COL),'collector source/log differs'
 (R/'collector-current-binding.json').write_text(json.dumps(dict(head=inventory['head'],
  inventory_sha256=inventory['inventory_sha256'],owners=mods,environment_sha256=environment,
  probe_module=P+'/CollectHead',source_sha256=rr['source_sha256'],log_sha256=rr['log_sha256'],
  log=str(COL),status='CURRENT_COLLECTOR_PASS'),indent=2)+'\n')
 python(home/'request_counts.py',COL,R,'--inventory',a.inventory,'--probe-binding',R/'collector-current-binding.json')
elif a.phase=='generate':
 python(home/'prepare_static.py','--root',wt,'--out',S,'--inventory',a.inventory)
 current=iv['load'](a.inventory,wt);assert current==inventory
 assert (S/'owners.txt').read_text().split()==mods and (S/'files.txt').read_text().split()==files
 # Check source bytes explicitly; mkseals reads git show and binds its hashes.
 for f in files:
  saved=subprocess.check_output(['git','-C',str(wt),'show',a.rev+':'+f])
  assert saved==(wt/f).read_bytes(),'UNCOMMITTED SOURCE DIFFERENCE '+f
 python(T/'review/touched.py',wt,BASE,a.rev,R/'touched.json',*files,log=R/'touched.tsv')
 for variant,coE,eval_b in [('strict-A',False,False),('strict-B',False,True),('coe-A',True,False),('coe-B',True,True)]:
  letter='B'if eval_b else'A';rec=R/'seals'/variant;sub=P+'/seals_'+variant.replace('-','_')
  python(T/('review/mkseals_coe.py'if coE else'review/mkseals_ab.py'),G,COL,wt,a.rev,rec,sub,'Seal'+letter+'_',*mods,
   log=R/('prepare-'+variant+'.log'),extra={'SEAL_EVAL':'1'if eval_b else'0'})
  python(home/'mkctl_iosprg.py',G,rec,wt,P+'/controls_'+variant.replace('-','_'),R/'controls'/variant,
   '--static-plan',S/'static-plan.json',log=R/('prepare-controls-'+variant+'.log'))
elif a.phase=='pretest':
 paths=[]
 for d in sorted((R/'controls').iterdir()):paths+=(d/'unsealed-order.txt').read_text().split()
 run_order(write_order('orders/controls-unsealed.txt',paths),R/'control-runs')
 rows=[json.loads(x)for x in(R/'control-runs/results.jsonl').read_text().splitlines()if '"module"'in x]
 bad=[x for x in rows if x['rc']!=0 or x['errors']!=0]
 (R/'unsealed-pretest.json').write_text(json.dumps(dict(all_ok=not bad,bad=bad),indent=1)+'\n')
 assert not bad,'UNSEALED CONTROL PRETEST FAILED: do not run sealed controls until repaired'
elif a.phase=='seals':
 python(home/'run_matrix.py',wt,a.tree,R.relative_to(wt))
elif a.phase=='controls':
 # The resumable queue executes every unsealed group before any sealed group.
 python(home/'run_controls.py',wt,a.tree,R.relative_to(wt))
elif a.phase=='summarize':
 for d in sorted((R/'seals').iterdir()):
  python(T/'review/sealsum.py',d,R/'seal-runs',R/'touched.json',R/('seals-'+d.name+'.tsv'))
 for d in sorted((R/'controls').iterdir()):
  python(T/'review/ctlcheck2.py',d/'controls-plan.json',R/'control-runs',R/('ctlcheck-'+d.name+'.json'),
   log=R/('ctlcheck-'+d.name+'.log'))
  assert json.loads((R/('ctlcheck-'+d.name+'.json')).read_text())['all_ok'],'CONTROL FAILURE '+d.name
elif a.phase=='scan-prepare':
 probe=wt/P/'ExplicitKinds.lean'
 python(T/'scan1_g40.py',G/'scan_explicit.py',wt,R/'touched.json',R/'explicit-items.json',probe,*files,
  extra={'SCAN_IMPORTS':' '.join(mods)})
 (R/'explicit-inventory-binding.json').write_text(json.dumps(dict(head=inventory['head'],
  inventory_sha256=inventory['inventory_sha256'],source_sha256={f:inventory['source_sha256'][f] for f in files},
  probe_module=P+'/ExplicitKinds',probe_sha256=__import__('hashlib').sha256(probe.read_bytes()).hexdigest(),
  items_sha256=__import__('hashlib').sha256((R/'explicit-items.json').read_bytes()).hexdigest()),indent=2)+'\n')
elif a.phase=='scan-run':
 run_order(write_order('orders/explicit.txt',[P+'/ExplicitKinds']),R/'explicit-runs')
 lp=R/'explicit-runs/mods'/(P.replace('/','_')+'_ExplicitKinds.log')
 python(T/'scan2.py',R/'explicit-items.json',lp,R/'explicit-classified.json',log=R/'explicit-summary.log')
 eb=json.loads((R/'explicit-inventory-binding.json').read_text())
 assert eb['inventory_sha256']==inventory['inventory_sha256']
 rr=next(r for r in reversed([json.loads(l) for l in(R/'explicit-runs/results.jsonl').read_text().splitlines()]) if r.get('module')==P+'/ExplicitKinds')
 sha=lambda p:__import__('hashlib').sha256(Path(p).read_bytes()).hexdigest()
 assert rr['rc']==rr['errors']==0 and not __import__('re').search(r'error[:(]',lp.read_text())
 assert rr['source_sha256']==eb['probe_sha256']==sha(wt/(P+'/ExplicitKinds.lean'))
 assert rr['log_sha256']==sha(lp) and eb['items_sha256']==sha(R/'explicit-items.json')
 binds=runpy.run_path(str(home/'environment_binding.py'));environment=binds['snapshot'](a.tree,R)
 summary=json.loads((R/'explicit-classified.json').read_text())['summary'];assert summary['foreign_items']==0
 eb.update(environment_sha256=environment,foreign_items=summary['foreign_items'],items=summary['items'],run=rr)
 (R/'explicit-current-binding.json').write_text(json.dumps(eb,indent=2)+'\n')
