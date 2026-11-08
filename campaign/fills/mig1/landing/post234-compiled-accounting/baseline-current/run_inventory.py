from pathlib import Path
import subprocess,json,hashlib,gzip,base64,time,datetime,os,sys,shutil
P=Path('/private/tmp/mig-post234-compiled-accounting')
ctx=json.loads((P/'preparation.json').read_text())
assert sys.argv[1]=='Base','HEAD requires a separately verified final-context relay'
stage='Base';project=Path(ctx['project']);probe=project/'Base.lean';snap=Path(ctx['base_snapshot'])
assert hashlib.sha256(probe.read_bytes()).hexdigest()==ctx['probe_sha256']
assert hashlib.sha256(Path(ctx['wrapper']).read_bytes()).hexdigest()==ctx['wrapper_sha256']
assert (project/'lean-toolchain').read_text()=='leanprover/lean4:v4.25.0\n'
assert (project/'.lake/packages').resolve()==Path(ctx['packages'])
command=['bash',ctx['wrapper'],str(project),str(snap),str(probe)]
req={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'stage':stage,'source':ctx['campaign_base'],'snapshot':str(snap),'whole_objects':895,'command':command,'probe_sha256':ctx['probe_sha256'],'toolchain':ctx['toolchain'],'local_slots':3,'machine_cap':5,'plain_wrapper_no_snapshot_writes':True,'no_proof_value_rendering':True}
assert not(P/'Base-run.json').exists()
(P/'Base-request.json').write_text(json.dumps(req,indent=2)+'\n')
t=time.monotonic();raw=P/'Base.raw.tmp';env=os.environ.copy();env['TCSLIB_LEAN_SLOTS']='3'
with raw.open('wb')as f:r=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,env=env)
seconds=time.monotonic()-t
h=hashlib.sha256();errors=warnings=sorries=0
with raw.open('rb')as f:
 for line in f:
  h.update(line)
  errors+=b': error:'in line
  warnings+=b': warning:'in line
  sorries+=b"declaration uses 'sorry'"in line
rawsha=h.hexdigest();rawsize=raw.stat().st_size
gz=P/'Base.out.gz'
with raw.open('rb')as inf,gz.open('wb')as of:
 with gzip.GzipFile(filename='',fileobj=of,mode='wb',mtime=0)as z:shutil.copyfileobj(inf,z)
b64=P/'Base.out.gz.base64.txt';data=gz.read_bytes();b64.write_bytes(base64.encodebytes(data))
h2=hashlib.sha256()
with gzip.open(gz,'rb')as f:
 while chunk:=f.read(1<<20):h2.update(chunk)
assert h2.hexdigest()==rawsha and base64.decodebytes(b64.read_bytes())==data
run={**req,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds_including_slot_wait':seconds,'exit':r.returncode,'errors':errors,'warnings':warnings,'sorry_warnings':sorries,'raw_bytes':rawsize,'raw_sha256':rawsha,'gzip_bytes':len(data),'gzip_sha256':hashlib.sha256(data).hexdigest(),'base64_bytes':b64.stat().st_size,'base64_sha256':hashlib.sha256(b64.read_bytes()).hexdigest(),'complete_raw_retained_losslessly_in_gzip_and_base64':True}
(P/'Base-run.json').write_text(json.dumps(run,indent=2)+'\n')
raw.unlink()
print(json.dumps(run,indent=2),flush=True)
assert r.returncode==0 and errors==0 and warnings==0 and sorries==0
