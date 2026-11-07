"""Run one reviewed proposal probe against a complete fixed snapshot, retaining actual receipts."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,tempfile,time
out=Path(__file__).resolve().parent
root=out.parents[4]
scratch=Path(os.environ['TCSLIB_SCRATCH']);wt=scratch/'wt-epad';snapshot=scratch/'oleans-mig1-preflight-current1'
label,filename=sys.argv[1:3]
assert re.fullmatch(r'[A-Za-z0-9_-]+',label)
source=out/filename;assert source.parent==out and source.name.endswith('.lean.txt')
assert not (out/(label+'.json')).exists() and not (out/(label+'.out')).exists()
data=source.read_bytes();directory=Path(tempfile.mkdtemp(prefix='tcslib-redirect-home-',dir='/private/tmp'));probe=directory/(label+'.lean');probe.write_bytes(data)
command=['bash',str(root/'devtools/seyoon/leanelab.sh'),str(wt),str(snapshot),str(probe)]
start=time.time();p=subprocess.run(command,cwd=wt,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/(label+'.out')).write_bytes(p.stdout)
r=dict(label=label,source=str(source),snapshot=str(snapshot),command=command,exit=p.returncode,errors=len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',p.stdout)),seconds=time.time()-start,input_sha256=hashlib.sha256(data).hexdigest(),output_sha256=hashlib.sha256(p.stdout).hexdigest(),source_still_matches=source.read_bytes()==data)
(out/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));print(p.stdout.decode(errors='replace'))
