from pathlib import Path
import datetime,hashlib,json,os,resource,subprocess,sys,time
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
side=sys.argv[1];assert side in ['base','head']
CAP=OUT/(side+'-capture.json');C=json.loads(CAP.read_text());assert C['side']==side and len(C['population'])==25
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen';held=False;owner=None
sha=lambda b:hashlib.sha256(b).hexdigest();now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def event(kind,**fields):
 with (OUT/'lock-events.jsonl').open('a') as f:f.write(json.dumps(dict(utc=now(),side=side,event=kind,**fields))+'\n')
def active():
 q=subprocess.run(['ps','-axo','pid=,command='],check=True,stdout=subprocess.PIPE,text=True)
 return [x for x in q.stdout.splitlines() if 'copy-text-screen-v3.py' in x]
try:
 output=OUT/(side+'.out');receipt=OUT/(side+'-run.json');assert not output.exists() and not receipt.exists()
 if side=='head':assert json.loads((OUT/'base-run.json').read_text())['exit']==0
 tool=ROOT/'scripts/copy-text-screen-v3.py';assert sha(tool.read_bytes())==C['tool_sha256'];tree=Path(C['tree'])
 for row in C['files']:assert sha((tree/row['path']).read_bytes())==row['sha256']
 event('waiting',lock=str(lock))
 while not held:
  screens=active()
  if screens:time.sleep(2);continue
  try:
   lock.mkdir();held=True;owner=os.getpid();(lock/'pid').write_text(str(owner)+'\n')
  except FileExistsError:
   p=lock/'pid';value=p.read_text().strip() if p.exists() else '';alive=False
   if value.isdigit():
    try:os.kill(int(value),0);alive=True
    except ProcessLookupError:pass
   old=time.time()-lock.stat().st_mtime>60
   if not alive and (value or old) and not active():
    assert {p.name for p in lock.iterdir()}<={'pid'};event('reclaiming_verified_stale',old_pid=value);p.unlink(missing_ok=True);lock.rmdir();event('reclaimed_stale',old_pid=value)
   else:time.sleep(2)
 event('acquired',pid=owner);assert not active()
 cmd=['nice','-n','10','python3','-I',str(tool),str(tree),*C['population']];row=dict(side=side,source_commit=C['commit'],command=cmd,start_utc=now(),orchestrator_sha256=sha(Path(__file__).read_bytes()),side_capture_sha256=sha(CAP.read_bytes()),python_version=sys.version,script_sha256=sha(tool.read_bytes()),full_population=25,lock=str(lock),fresh_execution=True)
 (OUT/(side+'-request.json')).write_text(json.dumps(row,indent=2)+'\n');tick=time.time();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 with output.open('wb') as f:
  child=subprocess.Popen(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT);owner=child.pid;(lock/'pid').write_text(str(owner)+'\n');event('launched',pid=owner,source_commit=C['commit']);print('ACTUAL '+side.upper()+' START '+row['start_utc']+' PID '+str(owner)+' SOURCE '+C['commit'],flush=True);code=child.wait()
 after=resource.getrusage(resource.RUSAGE_CHILDREN);data=output.read_bytes();row.update(pid=owner,end_utc=now(),seconds=time.time()-tick,exit=code,output_sha256=sha(data),bytes=len(data),user_cpu_seconds=after.ru_utime-before.ru_utime,system_cpu_seconds=after.ru_stime-before.ru_stime,child_maxrss=after.ru_maxrss,first_line=data.decode(errors='replace').splitlines()[0] if data else '')
 for r in C['files']:assert sha((tree/r['path']).read_bytes())==r['sha256']
 assert sha(CAP.read_bytes())==row['side_capture_sha256'];receipt.write_text(json.dumps(row,indent=2)+'\n');event('completed',pid=owner,exit=code);owner=os.getpid();(lock/'pid').write_text(str(owner)+'\n');print(json.dumps(row),flush=True)
 if code:raise RuntimeError('screen exited nonzero')
finally:
 if held:
  p=lock/'pid';assert p.read_text().strip()==str(owner);p.unlink();lock.rmdir();event('released',pid=owner);print('SHARED SCREEN LOCK RELEASED '+side+' '+now(),flush=True)
