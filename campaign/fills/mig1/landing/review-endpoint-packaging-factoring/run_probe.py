"""Run a reviewed inert probe against complete current2, retaining exact receipts."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys, tempfile, time
p=Path(__file__).resolve().parent
root=p.parents[4]
scratch=Path(os.environ['TCSLIB_SCRATCH']);wt=scratch/'wt-epad';snapshot=scratch/'oleans-mig1-preflight-current2'
label,filename=sys.argv[1:3]
assert re.fullmatch(r'[A-Za-z0-9_-]+',label)
source=p/filename
assert source.name.endswith('.lean.txt') and source.parent==p
assert not (p/(label+'.json')).exists() and not (p/(label+'.out')).exists()
data=source.read_bytes()
tmp=Path(tempfile.mkdtemp(prefix='tcslib-endpoint-package-',dir='/private/tmp'))
probe=tmp/(label+'.lean');probe.write_bytes(data)
actual=wt/'TCSlib/Complexity/TuringMachine/Build/Catalog.lean'
before=hashlib.sha256(actual.read_bytes()).hexdigest()
command=['bash',str(root/'devtools/seyoon/leanelab.sh'),str(wt),str(snapshot),str(probe)]
start=time.time()
r=subprocess.run(command,cwd=wt,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(p/(label+'.out')).write_bytes(r.stdout)
row={'label':label,'command':command,'snapshot':str(snapshot),
 'started_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),
 'exit':r.returncode,'errors':len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',r.stdout)),
 'seconds':time.time()-start,'input_sha256':hashlib.sha256(data).hexdigest(),
 'output_sha256':hashlib.sha256(r.stdout).hexdigest(),'source_still_matches':source.read_bytes()==data,
 'actual_catalog_before_sha256':before,'actual_catalog_after_sha256':hashlib.sha256(actual.read_bytes()).hexdigest(),
 'plain_managed_no_compiled_output':True,'local_slots':os.environ.get('TCSLIB_LEAN_SLOTS')}
(p/(label+'.json')).write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(row,indent=2))
print('\n'.join(line for line in r.stdout.decode(errors='replace').splitlines() if 'error' in line or 'axiom' in line or line.startswith('API|') or line.startswith('DIRECT_DEF|')))
