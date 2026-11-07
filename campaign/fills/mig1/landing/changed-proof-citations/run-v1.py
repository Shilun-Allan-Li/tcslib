from pathlib import Path
import os,tempfile,time,hashlib,re,json,subprocess
r=Path.cwd();out=r/'campaign/fills/mig1/landing/changed-proof-citations';s=Path(os.environ['TCSLIB_SCRATCH']);src=out/'All140.lean.txt';data=src.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-mig1-all140-',dir='/private/tmp'));p=tmp/'All140.lean';p.write_bytes(data)
cmd=['bash',str(r/'devtools/seyoon/leanelab.sh'),str(s/'wt-epad'),str(s/'oleans-mig1-preflight-current2'),str(p)];t=time.time();c=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'All140.out').write_bytes(c.stdout)
j={'command':cmd,'seconds':time.time()-t,'exit':c.returncode,'errors':len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',c.stdout)),'input_sha256':hashlib.sha256(data).hexdigest(),'output_sha256':hashlib.sha256(c.stdout).hexdigest(),'scope':'140 actual new/changed proof roots and all compiled descendants, recursive axioms and direct citation ownership, final2 complete read-only preflight; no replay'}
(out/'All140-run.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j));print(c.stdout.decode(errors='replace')[-2500:] if c.returncode else 'Complete raw root/descendant/citation output retained.')
raise SystemExit(c.returncode)
