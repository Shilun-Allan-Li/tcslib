"""Run exactly one reviewed inert input through the managed Lean wrapper.
No payload execution; every run gets a fresh immutable attempt receipt.
"""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys,tempfile,time
out=Path(__file__).resolve().parent; root=out.parents[4]
source=out/sys.argv[1]
if source.parent!=out or not source.name.endswith('.lean.txt'):raise SystemExit('direct inert probe only')
stem=source.name.removesuffix('.lean.txt');log=out/(stem+'.out');receipt=out/(stem+'-run.json')
if log.exists() or receipt.exists():raise SystemExit('immutable attempt already exists')
data=source.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-mig1-primitives-',dir='/private/tmp'));probe=tmp/(stem.replace('-','_')+'.lean');probe.write_bytes(data)
s=Path(os.environ['TCSLIB_SCRATCH']);wt=s/'wt-epad';ov=s/'oleans-mig1-primitives-repair';wrapper=root/'devtools/seyoon/leanelab.sh'
command=['bash',str(wrapper),str(wt),str(ov),str(probe)]
start=time.time();r=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(r.stdout)
t=r.stdout.decode(errors='replace');d={'command':command,'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'seconds':time.time()-start,'input_sha256':hashlib.sha256(data).hexdigest(),'output_sha256':hashlib.sha256(r.stdout).hexdigest(),'exit':r.returncode,'errors':len(re.findall(r'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',t)),'snapshot':'Private complete overlay chained from oleans-reading-preflight2; no combined campaign replay claim.','temporary_input':str(probe)};receipt.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2));print(t if len(t)<12000 else 'Full output preserved: '+str(log))
