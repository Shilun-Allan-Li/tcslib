from pathlib import Path
import os,json,subprocess,time,hashlib,shutil,datetime
out=Path('/private/tmp/ab34-late-context-screen');request=json.loads((out/'REQUEST.json').read_text());lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen';shutil.copyfile(__file__,out/'driver.py');rows=[]
for side in ['BASE','NAT','LADNER']:
 tree=out/'exports'/side;part=request['exports'][side];pop=part['files']
 while True:
  try:lock.mkdir();(lock/'pid').write_text(str(os.getpid())+'\n');break
  except FileExistsError:
   try:pid=int((lock/'pid').read_text());os.kill(pid,0)
   except ProcessLookupError:(lock/'pid').unlink();lock.rmdir();continue
   except(FileNotFoundError,ValueError):pass
   time.sleep(2)
 start=time.monotonic();(out/'progress.json').write_text(json.dumps({'phase':side,'population':len(pop),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'completed':rows},indent=2)+'\n');print('LATE FULL SCREEN START',side,len(pop),flush=True)
 try:
  with(out/(side+'.txt')).open('wb') as f:r=subprocess.run(['nice','-n','10','python3','-I',str(tree/'scripts/copy-text-screen-v3.py'),str(tree),*pop],stdout=f,stderr=subprocess.STDOUT)
 finally:(lock/'pid').unlink(missing_ok=True);lock.rmdir()
 assert part['sha256']=={p:hashlib.sha256((tree/p).read_bytes()).hexdigest() for p in part['sha256']}
 b=(out/(side+'.txt')).read_bytes();row={'side':side,'source':part['source'],'population':len(pop),'exit':r.returncode,'seconds':time.monotonic()-start,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source_unchanged':True};rows.append(row);(out/'RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n');assert r.returncode==0;print('LATE FULL SCREEN PASS',side,flush=True)
 if side!='BASE':(out/(side+'-pairdiff.txt')).write_bytes(subprocess.check_output(['python3','-I',str(tree/'devtools/seyoon/pairdiff.py'),str(out/(side+'.txt')),str(out/'BASE.txt')]))
 time.sleep(3)
(out/'COMPLETE.json').write_text(json.dumps({'pass':True,'results':rows,'populations':[48,48,49],'new_file_absence_explicit':True},indent=2)+'\n')
