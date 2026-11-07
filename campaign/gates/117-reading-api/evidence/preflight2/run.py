from pathlib import Path
import os, subprocess, json, hashlib, datetime, time, re
R=Path.cwd(); S=Path(os.environ['TCSLIB_SCRATCH']); W=S/'wt-natbits'; E=R/'campaign/gates/117-reading-api/evidence/preflight2'; O=S/'oleans-reading-preflight2'
head=subprocess.check_output(['git','-C',str(W),'rev-parse','HEAD']).decode().strip();subprocess.run(['git','-C',str(W),'cat-file','-e',head+'^{commit}'],check=True)
files=subprocess.check_output(['git','-C',str(W),'diff','--name-only','origin/complexity/arora-barak-ch3-4...HEAD','--','*.lean']).decode().splitlines();assert len(files)==5
order=[m for m in (S/'fills/replay/down-mra2.txt').read_text().splitlines() if m+'.lean' in files];assert len(order)==5
assert not O.exists();subprocess.run(['cp','-cR',str(S/'oleans-mac3'),str(O)],check=True)
r={'head':head,'snapshot':'oleans-reading-preflight2','base_snapshot':'oleans-mac3','order':order,'runs':[],'scope':'five changed modules only; not the394-module downstream replay'}
for m in order:
 for suffix in ['.olean','.ilean','.c','.trace']:
  (O/(m+suffix)).unlink(missing_ok=True)
 f=m+'.lean';data=(W/f).read_bytes();out=E/(m.replace('/','__')+'.out');start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
 cmd=['bash',str(R/'devtools/seyoon/leanelab-o.sh'),str(W),str(O),f,str(O)]
 with out.open('wb') as stream:p=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
 log=out.read_bytes();errors=len(re.findall(rb':\d+:\d+: error',log))
 r['runs'].append({'file':f,'source_sha256':hashlib.sha256(data).hexdigest(),'start_utc':start,'seconds':time.monotonic()-t,'exit':p.returncode,'errors':errors,'command':cmd,'log':str(out.relative_to(R)),'log_sha256':hashlib.sha256(log).hexdigest()})
 (E/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
 print(f+' exit='+str(p.returncode)+' errors='+str(errors),flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 assert data==(W/f).read_bytes()
r['complete']=True;r['failed']=0;(E/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print('PREFLIGHT PASSED:5 changed modules',flush=True)
