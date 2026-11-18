# io-sprg Rule10 runner/config,2026-11-18. ROOT-ONLY EXECUTION.
# Host adaptation: fixed managed Mac worktree replaces historical /home/user/fill/tcslib.
# All Lean invocations delegate to existing runner_full.py, which acquires lean-slot.sh
# and runs foreground lean -DmaxErrors=0 WITHOUT -o, one process at a time.
# This script is staged, not executed by its preparing subagent.
import argparse,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT='/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange'
BASE='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
ap=argparse.ArgumentParser();ap.add_argument('phase',choices=['collect','generate','pretest','seals','controls','summarize','scan-prepare','scan-run'])
ap.add_argument('--root',default=ROOT);ap.add_argument('--tree',required=True)
ap.add_argument('--collector-log');ap.add_argument('--rev',default='HEAD');ap.add_argument('--run',default='m0')
a=ap.parse_args();wt=Path(a.root).resolve();home=Path(__file__).resolve().parent
T=wt/'evidence/tools/seal';G=T/'review/archived-gate10-tools'
R=wt/'evidence/rule10'/a.run;P='evidence/probes/io_sprg_'+a.run
R.mkdir(parents=True,exist_ok=True);(wt/P).mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_SLOT_TAG='io-sprg',SEAL_CHUNK='2048',SEAL_FAST_LOG='1')
mods=(home/'owners.txt').read_text().split();files=(home/'files.txt').read_text().split()
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
 python(home/'prepare_static.py','--root',wt,'--out',home)
 python(T/'review/mkcollect.py',T/'review/NmCollect.template.lean',home/'owners.txt','io-sprg '+a.run,wt/P/'CollectHead.lean')
 order=write_order('orders/collector.txt',[P+'/CollectHead']);run_order(order,R/'collector-runs')
 rows=[json.loads(x)for x in(R/'collector-runs/results.jsonl').read_text().splitlines()]
 assert any(x.get('module')==P+'/CollectHead'and x['rc']==0 and x['errors']==0 for x in rows),'collector failed'
 python(home/'request_counts.py',COL,R)
elif a.phase=='generate':
 python(home/'prepare_static.py','--root',wt,'--out',home)
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
   '--static-plan',home/'static-plan.json',log=R/('prepare-controls-'+variant+'.log'))
elif a.phase=='pretest':
 paths=[]
 for d in sorted((R/'controls').iterdir()):paths+=(d/'unsealed-order.txt').read_text().split()
 run_order(write_order('orders/controls-unsealed.txt',paths),R/'control-runs')
 rows=[json.loads(x)for x in(R/'control-runs/results.jsonl').read_text().splitlines()if '"module"'in x]
 bad=[x for x in rows if x['rc']!=0 or x['errors']!=0]
 (R/'unsealed-pretest.json').write_text(json.dumps(dict(all_ok=not bad,bad=bad),indent=1)+'\n')
 assert not bad,'UNSEALED CONTROL PRETEST FAILED: do not run sealed controls until repaired'
elif a.phase=='seals':
 paths=[]
 for d in sorted((R/'seals').iterdir()):
  paths += [p['probe_module']for p in json.loads((d/'manifest.json').read_text())['probes']]
 run_order(write_order('orders/seals.txt',paths),R/'seal-runs')
elif a.phase=='controls':
 assert json.loads((R/'unsealed-pretest.json').read_text())['all_ok'],'unsealed pretest not passed'
 paths=[]
 for d in sorted((R/'controls').iterdir()):paths+=(d/'sealed-order.txt').read_text().split()
 run_order(write_order('orders/controls-sealed.txt',paths),R/'control-runs')
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
elif a.phase=='scan-run':
 run_order(write_order('orders/explicit.txt',[P+'/ExplicitKinds']),R/'explicit-runs')
 lp=R/'explicit-runs/mods'/(P.replace('/','_')+'_ExplicitKinds.log')
 python(T/'scan2.py',R/'explicit-items.json',lp,R/'explicit-classified.json',log=R/'explicit-summary.log')
