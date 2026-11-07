from pathlib import Path
import hashlib,json,re,subprocess,sys,time,datetime
OUT=Path(__file__).resolve().parent;ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
s=json.loads((OUT/'setup.json').read_text());project=Path(s['project']);overlay=Path(s['overlay']);name,mode=sys.argv[1:3];assert mode in ('plain','module')
assert not (OUT/(name+'-run.json')).exists() and not (OUT/(name+'.out')).exists()
if mode=='module':
 rel='TCSlib/Complexity/TuringMachine/Build/'+name.replace('-native','')+'.lean';file=project/rel;source=file.read_bytes()
 for suffix in ['.olean','.ilean','.c','.trace']:
  target=overlay/Path(rel).with_suffix(suffix);assert overlay in target.parents;target.unlink(missing_ok=True)
 cmd=['bash',str(ROOT/'devtools/seyoon/leanelab-o.sh'),str(project),str(overlay),rel,str(overlay)]
else:
 source=(OUT/(name+'.lean.txt')).read_bytes();file=project/(name.replace('-','_')+'.lean');file.write_bytes(source);cmd=['bash',str(ROOT/'devtools/seyoon/leanelab.sh'),str(project),str(overlay),str(file)]
start=time.time();row={'name':name,'mode':mode,'command':cmd,'source':str(file),'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'input_sha256':hashlib.sha256(source).hexdigest()};(OUT/(name+'-request.json')).write_text(json.dumps(row,indent=2)+'\n')
r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,cwd=project);(OUT/(name+'.out')).write_bytes(r.stdout);row.update(exit=r.returncode,errors=len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',r.stdout)),seconds=time.time()-start,output_sha256=hashlib.sha256(r.stdout).hexdigest())
if mode=='module'and r.returncode==0:row['olean_sha256']=hashlib.sha256((overlay/Path(rel).with_suffix('.olean')).read_bytes()).hexdigest()
(OUT/(name+'-run.json')).write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row,indent=2));print(r.stdout.decode(errors='replace'))
