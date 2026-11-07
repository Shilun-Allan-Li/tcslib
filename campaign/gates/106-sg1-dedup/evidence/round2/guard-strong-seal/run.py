from pathlib import Path
import os,sys,re,tempfile,time,subprocess,json,hashlib
out=Path(__file__).resolve().parent;r=Path.cwd();s=Path(os.environ['TCSLIB_SCRATCH'])
for label in ['Inventory','Guard-SAT','Guard-Hardness','Controls-unsealed','Controls-sealed']:
 src=out/(label+'.lean.txt');data=src.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-sg1-strong-',dir='/private/tmp'));p=tmp/(label.replace('-','_')+'.lean');p.write_bytes(data);log=out/(label+'.out');rec=out/(label+'-run.json');assert not log.exists() and not rec.exists()
 cmd=['bash',str(r/'devtools/seyoon/leanelab.sh'),str(s/'wt-sg1'),str(s/'oleans-msg4'),str(p)];t=time.time();c=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(c.stdout);j={'command':cmd,'seconds':time.time()-t,'exit':c.returncode,'errors':len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',c.stdout)),'input_sha256':hashlib.sha256(data).hexdigest(),'output_sha256':hashlib.sha256(c.stdout).hexdigest()};rec.write_text(json.dumps(j,indent=2)+'\n');print(label,j['exit'],j['errors'],flush=True)
