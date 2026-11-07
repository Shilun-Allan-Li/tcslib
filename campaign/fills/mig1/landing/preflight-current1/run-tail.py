from pathlib import Path
import os,subprocess,hashlib,json,re,time
r=Path.cwd();s=Path(os.environ['TCSLIB_SCRATCH']);out=r/'campaign/fills/mig1/landing/preflight-current1';ov=s/'oleans-mig1-preflight-current1';wt=s/'wt-epad'
files=['TCSlib/Complexity/TuringMachine/Build/Primitives.lean','TCSlib/Complexity/TuringMachine/Build/Catalog.lean','TCSlib/Complexity/TuringMachine/Build/CertShell.lean','TCSlib/Complexity/TuringMachine/CodeSimulator.lean','TCSlib/Complexity/RAMSimulation/WordSize.lean'];results=[]
for f in files:
 src=wt/f;data=src.read_bytes();label=Path(f).stem;arch=out/(label+'.lean.txt');assert not arch.exists();arch.write_bytes(data)
 for suffix in ['.olean','.ilean','.c','.trace']:(ov/Path(f).with_suffix(suffix)).unlink(missing_ok=True)
 cmd=['bash',str(r/'devtools/seyoon/leanelab-o.sh'),str(wt),str(ov),f,str(ov)];t=time.time();c=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=out/(label+'.out');raw.write_bytes(c.stdout);j={'source':f,'source_sha256':hashlib.sha256(data).hexdigest(),'source_unchanged_during_compile':src.read_bytes()==data,'command':cmd,'seconds':time.time()-t,'exit':c.returncode,'errors':len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',c.stdout)),'output_sha256':hashlib.sha256(c.stdout).hexdigest()};(out/(label+'-run.json')).write_text(json.dumps(j,indent=2)+'\n');results.append(j);print(label,j['exit'],j['errors'],j['source_unchanged_during_compile'],flush=True)
 if c.returncode or j['errors'] or not j['source_unchanged_during_compile']:raise SystemExit('preflight failure; preserve overlay, no pass claim')
(out/'tail-receipt.json').write_text(json.dumps({'stage':'five tail modules compiled, including exactly Primitives milestone2; no full current replay claim','base_complete_snapshot':'oleans-mra2','overlay':str(ov),'results':results},indent=2)+'\n')
