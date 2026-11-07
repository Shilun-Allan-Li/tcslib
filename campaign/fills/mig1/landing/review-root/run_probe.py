from pathlib import Path
import os,sys,subprocess,tempfile,re,time,json,hashlib,datetime
out=Path(__file__).resolve().parent;r=out.parents[4];s=Path(os.environ['TCSLIB_SCRATCH'])
source=out/sys.argv[1];assert source.parent==out and source.name.endswith('.lean.txt')
label=source.name.removesuffix('.lean.txt');log=out/(label+'.out');rec=out/(label+'-run.json');assert not log.exists() and not rec.exists()
data=source.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-mig1-root-',dir='/private/tmp'));p=tmp/(label.replace('-','_')+'.lean');p.write_bytes(data)
cmd=['bash',str(r/'devtools/seyoon/leanelab.sh'),str(s/'wt-natbits'),str(s/'oleans-mra2'),str(p)]
t=time.time();c=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(c.stdout)
j={'command':cmd,'context':'complete oleans-mra2, frozen published API head1160; focused proof checks, not final MIG1 combined chain','at_utc':datetime.datetime.fromtimestamp(t,datetime.timezone.utc).isoformat(),'seconds':time.time()-t,'exit':c.returncode,'errors':len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',c.stdout)),'input_sha256':hashlib.sha256(data).hexdigest(),'output_sha256':hashlib.sha256(c.stdout).hexdigest()};rec.write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j));print(c.stdout.decode(errors='replace')[-6000:])
