"""Freshly compile the reviewed owned module or one read-only dependency into this agent's private complete overlay."""
from pathlib import Path
import os,sys,subprocess,json,hashlib,datetime,time,re
out=Path(__file__).resolve().parent;root=out.parents[4];s=Path(os.environ['TCSLIB_SCRATCH']);wt=s/'wt-epad';ov=s/'oleans-mig1-primitives-repair'
relative=sys.argv[1];label=sys.argv[2]
allowed={'TCSlib/Complexity/TuringMachine/Build/Primitives.lean','TCSlib/Complexity/TuringMachine/Simulation.lean','TCSlib/Complexity/TuringMachine/Composition.lean','TCSlib/Complexity/TuringMachine/Build/Wrappers.lean','TCSlib/Complexity/TuringMachine/Build/Loop.lean','TCSlib/Complexity/TuringMachine/Encoding.lean','TCSlib/Complexity/ClassP/TimeConstructible.lean'}
if relative not in allowed:raise SystemExit('not an authorized owned module/dependency')
if (out/(label+'.json')).exists() or (out/(label+'.out')).exists():raise SystemExit('attempt already exists')
source=wt/relative;data=source.read_bytes();(out/(label+'-source.lean.txt')).write_bytes(data)
for suffix in ['.olean','.ilean','.c','.trace']:
 target=ov/relative.removesuffix('.lean');target=target.with_suffix(suffix)
 if target.exists():target.unlink()
command=['bash',str(root/'devtools/seyoon/leanelab-o.sh'),str(wt),str(ov),relative,str(ov)]
start=time.time();r=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/(label+'.out')).write_bytes(r.stdout)
after=source.read_bytes();text=r.stdout.decode(errors='replace');target=ov/relative.removesuffix('.lean');target=target.with_suffix('.olean')
receipt={'command':command,'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'seconds':time.time()-start,'source_sha256':hashlib.sha256(data).hexdigest(),'source_after_sha256':hashlib.sha256(after).hexdigest(),'source_stable':data==after,'exit':r.returncode,'errors':len(re.findall(r'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',text)),'output_sha256':hashlib.sha256(r.stdout).hexdigest(),'olean_sha256':hashlib.sha256(target.read_bytes()).hexdigest() if target.exists() and r.returncode==0 else None,'snapshot':'Private complete overlay; output artifacts unlinked before compilation. No shared snapshot writes or complete replay claim.'};(out/(label+'.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));print(text if len(text)<6000 else 'Full raw output preserved')
