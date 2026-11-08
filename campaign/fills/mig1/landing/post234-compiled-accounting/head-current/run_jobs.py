from pathlib import Path
import sys,re,subprocess,hashlib,gzip,base64,json,time,datetime,os,shutil
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());queue=json.loads((P/sys.argv[1]).read_text());project=Path(ctx['project']);wrapper=Path(ctx['wrapper'])
assert hashlib.sha256(wrapper.read_bytes()).hexdigest()==ctx['wrapper_sha256']and(project/'lean-toolchain').read_text()=='leanprover/lean4:v4.25.0\n'and(project/'.lake/packages').resolve()==Path(ctx['packages'])
for job in queue:
 name=job['name'];side=job['side'];probe=project/job['project_file'];evidence=P/job['evidence_file'];assert probe.read_bytes()==evidence.read_bytes();snap=next(x['path']for x in ctx['snapshots']if x['side']==side);req={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':name,'side':side,'source':ctx['base']if side=='Base'else ctx['source'],'snapshot':snap,'snapshot_whole895':True,'probe_sha256':hashlib.sha256(probe.read_bytes()).hexdigest(),'command':['bash',str(wrapper),str(project),snap,str(probe)],'toolchain':ctx['toolchain'],'one_Lean_at_a_time':True,'local_slots':3,'machine_cap':5,'no_theorem_proof_values_printed':True,'no_snapshot_output':True}
 assert not(P/(name+'-run.json')).exists(),name
 (P/(name+'-request.json')).write_text(json.dumps(req,indent=2)+'\n');raw=P/(name+'.raw.tmp');t=time.monotonic();env=os.environ.copy();env['TCSLIB_LEAN_SLOTS']='3'
 with raw.open('wb')as f:r=subprocess.run(req['command'],stdout=f,stderr=subprocess.STDOUT,env=env)
 elapsed=time.monotonic()-t;h=hashlib.sha256();errors=warnings=sorries=0
 with raw.open('rb')as f:
  for line in f:h.update(line);errors+=bool(re.search(rb': error(?:\([^\n)]*\))?:',line));warnings+=bool(re.search(rb': warning(?:\([^\n)]*\))?:',line));sorries+=b"declaration uses 'sorry'"in line
 zpath=P/(name+'.out.gz')
 with raw.open('rb')as inf,zpath.open('wb')as outf:
  with gzip.GzipFile(fileobj=outf,filename='',mode='wb',mtime=0)as z:shutil.copyfileobj(inf,z)
 z=zpath.read_bytes();coded=base64.encodebytes(z);(P/(name+'.out.gz.base64.txt')).write_bytes(coded);h2=hashlib.sha256()
 with gzip.open(zpath,'rb')as f:
  while b:=f.read(1<<20):h2.update(b)
 assert h.hexdigest()==h2.hexdigest()and base64.decodebytes(coded)==z
 run=req|{'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds_including_slot_wait':elapsed,'exit':r.returncode,'errors':errors,'warnings':warnings,'sorry_warnings':sorries,'raw_bytes':raw.stat().st_size,'raw_sha256':h.hexdigest(),'gzip_bytes':len(z),'gzip_sha256':hashlib.sha256(z).hexdigest(),'base64_bytes':len(coded),'base64_sha256':hashlib.sha256(coded).hexdigest(),'full_raw_lossless_gzip_and_Base64':True}
 (P/(name+'-run.json')).write_text(json.dumps(run,indent=2)+'\n');raw.unlink();print(json.dumps({k:run[k]for k in ['name','side','source','seconds_including_slot_wait','exit','errors','warnings','sorry_warnings','raw_bytes','raw_sha256']}),flush=True)
 expect=job.get('expected_errors',0);assert r.returncode==job.get('expected_exit',0)and errors==expect and warnings==job.get('expected_warnings',0)and sorries==0,(name,run)
