"""Run one fresh phase2 head screen; reuse both pinned earlier full outputs."""
from pathlib import Path
import ast, datetime, hashlib, json, os, signal, subprocess, sys, tempfile, time
p=Path(__file__).resolve().parent;root=p.parents[4]
capture=json.loads((p/'capture.json').read_text());paths=[r['path'] for r in capture['files']]
scratch=Path(os.environ['TCSLIB_SCRATCH']);lock=scratch/'locks/screen';events=p/'lock-events.jsonl'
sha=lambda data:hashlib.sha256(data).hexdigest()
screen=root/'scripts/copy-text-screen-v3.py';data=screen.read_bytes()
assert data==(p/'copy-text-screen-v3.py.txt').read_bytes()
pairdiff=root/'devtools/seyoon/pairdiff.py';pair_data=pairdiff.read_bytes()
assert pair_data==(p/'pairdiff.py.txt').read_bytes()
temp=Path(tempfile.mkdtemp(prefix='tcslib-mig-phase2-head25-',dir='/private/tmp'))
for row in capture['files']:
 data_in=(p/'inputs/head'/(row['path']+'.txt')).read_bytes()
 assert sha(data_in)==row['head_sha256']
 q=temp/row['path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data_in)
(p/'trees.json').write_text(json.dumps({'temporary_head_root':str(temp),'count':25},indent=2)+'\n')

# Reuse only the already reviewed shared-lock functions, never its main workflow.
old=p.parent/'screen-current25-draft/run_screens.py';lock_source=old.read_text()
nodes=[n for n in ast.parse(lock_source).body if isinstance(n,ast.FunctionDef) and n.name in ['event','acquire','release']]
assert len(nodes)==3
exec(compile(ast.Module(body=nodes,type_ignores=[]),'<reviewed-shared-screen-lock-functions>','exec'))
(p/'lock-helper-source.json').write_text(json.dumps({'source':str(old),'sha256':sha(old.read_bytes()),
 'functions':['event','acquire','release'],'unmodified_functions_reused':True},indent=2)+'\n')
child=None
def stop(signum,frame):
 if child is not None and child.poll() is None:child.terminate();child.wait()
 raise SystemExit(128+signum)
signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
assert not(p/'head.out').exists() and not(p/'head.json').exists()
command=['nice','-n','10',sys.executable,'-I',str(screen),str(temp),*paths]
acquire('phase2-head')
start=time.time()
try:
 with (p/'head.out').open('wb') as output:
  child=subprocess.Popen(command,cwd=root,stdout=output,stderr=subprocess.STDOUT);code=child.wait()
 assert screen.read_bytes()==data
 receipt={'label':'phase2-head','command':command,'exit':code,'elapsed_seconds':time.time()-start,
  'screen_sha256':sha(data),'output_sha256':sha((p/'head.out').read_bytes()),
  'source_count':25,'shared_lock':str(lock),'lock_owner_pid':os.getpid(),
  'captured_input_hashes_verified':True,'fresh_tiling_runs_this_phase':1,
  'baseline_reused':True,'previous_head_reused':True}
 (p/'head.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
 assert code==0
finally:
 if child is not None and child.poll() is None:child.terminate();child.wait()
 child=None;release('phase2-head')
for label,earlier in [('vs-base','base.out'),('vs-previous-head','previous-head.out')]:
 assert pairdiff.read_bytes()==pair_data
 cmd=[sys.executable,'-I',str(pairdiff),str(p/'head.out'),str(p/earlier)]
 run=subprocess.run(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (p/(label+'.out')).write_bytes(run.stdout)
 (p/(label+'.json')).write_text(json.dumps({'command':cmd,'exit':run.returncode,
  'pairdiff_sha256':sha(pair_data),'output_sha256':sha(run.stdout)},indent=2)+'\n')
 assert run.returncode==0
 print(label+' '+run.stdout.decode().splitlines()[0],flush=True)
