from pathlib import Path
import datetime, hashlib, json, os, resource, subprocess, sys, time
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
C=json.loads((OUT/'capture.json').read_text())
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen'
held=False
owner=None
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda b:hashlib.sha256(b).hexdigest()
def event(kind,**fields):
 with (OUT/'lock-events.jsonl').open('a') as f:f.write(json.dumps(dict(utc=now(),event=kind,**fields))+'\n')
def active():
 p=subprocess.run(['ps','-axo','pid=,command='],check=True,stdout=subprocess.PIPE,text=True)
 return [r for r in p.stdout.splitlines() if 'copy-text-screen-v3.py' in r]
try:
 tool=ROOT/'scripts/copy-text-screen-v3.py'
 assert sha(tool.read_bytes())==C['tools']['scripts/copy-text-screen-v3.py']
 tree=Path(C['temporary_trees']['head'])
 for row in C['sides']['head']['files']:assert sha((tree/row['path']).read_bytes())==row['sha256']
 assert not (OUT/'head.out').exists() and not (OUT/'head-run.json').exists()
 event('waiting',lock=str(lock))
 while not held:
  screens=active()
  if screens:
   event('waiting_active_screens',processes=screens);time.sleep(2);continue
  try:
   lock.mkdir();held=True;owner=os.getpid();(lock/'pid').write_text(str(owner)+'\n')
  except FileExistsError:
   p=lock/'pid';value=p.read_text().strip() if p.exists() else ''
   alive=False
   if value.isdigit():
    try:os.kill(int(value),0);alive=True
    except ProcessLookupError:pass
   if not alive and value=='78950' and not active():
    assert {x.name for x in lock.iterdir()}=={'pid'}
    event('reclaiming_verified_stale',old_pid=value,no_running_screen=True)
    p.unlink();lock.rmdir();event('reclaimed_stale',old_pid=value)
   else:time.sleep(2)
 event('acquired',pid=owner)
 assert not active()
 cmd=['nice','-n','10','python3','-I',str(tool),str(tree),*C['population']]
 row=dict(side='head',command=cmd,start_utc=now(),orchestrator_sha256=sha(Path(__file__).read_bytes()),python_version=sys.version,script_sha256=sha(tool.read_bytes()),full_population=23,lock=str(lock),base_adoption_receipt_sha256=sha((OUT/'base-adoption.json').read_bytes()))
 (OUT/'head-request.json').write_text(json.dumps(row,indent=2)+'\n')
 tick=time.time();before=resource.getrusage(resource.RUSAGE_CHILDREN)
 with (OUT/'head.out').open('wb') as f:
  process=subprocess.Popen(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
  owner=process.pid;(lock/'pid').write_text(str(owner)+'\n')
  event('head_launched',pid=owner,command=cmd)
  print('ACTUAL HEAD START '+row['start_utc']+' PID '+str(owner),flush=True)
  code=process.wait()
 after=resource.getrusage(resource.RUSAGE_CHILDREN);data=(OUT/'head.out').read_bytes()
 row.update(pid=owner,end_utc=now(),seconds=time.time()-tick,exit=code,output_sha256=sha(data),bytes=len(data),user_cpu_seconds=after.ru_utime-before.ru_utime,system_cpu_seconds=after.ru_stime-before.ru_stime,child_maxrss=after.ru_maxrss,first_line=data.decode(errors='replace').splitlines()[0] if data else '')
 (OUT/'head-run.json').write_text(json.dumps(row,indent=2)+'\n')
 event('head_completed',pid=owner,exit=code,output_sha256=sha(data))
 owner=os.getpid();(lock/'pid').write_text(str(owner)+'\n')
 print(json.dumps(row),flush=True)
 if code:raise RuntimeError('HEAD screen failed')
finally:
 if held:
  p=lock/'pid';assert p.read_text().strip()==str(owner);p.unlink();lock.rmdir();event('released',pid=owner)
  print('SHARED SCREEN LOCK RELEASED '+now(),flush=True)
