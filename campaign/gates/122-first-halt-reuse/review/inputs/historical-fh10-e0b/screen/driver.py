from pathlib import Path
import os,json,subprocess,time,hashlib,shutil,datetime
out=Path('/private/tmp/ab34-fh10-screen');request=json.loads((out/'REQUEST.json').read_text());pop=request['population'];lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen';shutil.copyfile(__file__,out/'driver.py');rows=[]
for side in ['BASE','HEAD']:
 tree=out/'exports'/side
 while True:
  try:lock.mkdir();(lock/'pid').write_text(str(os.getpid())+'\n');break
  except FileExistsError:
   try:pid=int((lock/'pid').read_text());os.kill(pid,0)
   except ProcessLookupError:(lock/'pid').unlink();lock.rmdir();continue
   except(FileNotFoundError,ValueError):pass
   time.sleep(2)
 start=time.monotonic();(out/'progress.json').write_text(json.dumps({'phase':side,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'completed':rows},indent=2)+'\n');print('FH43 SCREEN START',side,flush=True)
 try:
  with(out/(side+'.txt')).open('wb') as f:r=subprocess.run(['nice','-n','10','python3','-I',str(tree/'scripts/copy-text-screen-v3.py'),str(tree),*pop],stdout=f,stderr=subprocess.STDOUT)
 finally:(lock/'pid').unlink(missing_ok=True);lock.rmdir()
 assert request['exports'][side]['sha256']=={p:hashlib.sha256((tree/p).read_bytes()).hexdigest() for p in request['exports'][side]['sha256']}
 b=(out/(side+'.txt')).read_bytes();row={'side':side,'source':request['exports'][side]['source'],'exit':r.returncode,'seconds':time.monotonic()-start,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':True};rows.append(row);(out/'RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n');assert r.returncode==0;print('FH43 SCREEN PASS',side,flush=True)
head=out/'exports/HEAD';(out/'pairdiff.txt').write_bytes(subprocess.check_output(['python3','-I',str(head/'devtools/seyoon/pairdiff.py'),str(out/'HEAD.txt'),str(out/'BASE.txt')]))
(out/'COMPLETE.json').write_text(json.dumps({'pass':True,'head':request['head'],'population':43,'results':rows},indent=2)+'\n')
