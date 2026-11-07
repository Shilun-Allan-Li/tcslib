"""Native-check proposed copies/import consumers in an isolated temporary source project."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys,time
out=Path(__file__).resolve().parent;root=out.parents[4]
setup=json.loads((out/'scratch-setup.json').read_text());project=Path(setup['project']);overlay=Path(setup['overlay'])
label,mode,rel=sys.argv[1:4]
assert re.fullmatch(r'[A-Za-z0-9_-]+',label)
assert mode in ('module','consumer') and '..' not in Path(rel).parts
source=project/rel;data=source.read_bytes()
assert not (out/(label+'.json')).exists() and not (out/(label+'.out')).exists()
if mode=='module':cmd=['bash',str(root/'devtools/seyoon/leanelab-o.sh'),str(project),str(overlay),rel,str(overlay)]
else:cmd=['bash',str(root/'devtools/seyoon/leanelab.sh'),str(project),str(overlay),rel]
start=time.time();p=subprocess.run(cmd,cwd=project,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/(label+'.out')).write_bytes(p.stdout)
r=dict(label=label,mode=mode,source=str(source),complete_overlay=str(overlay),command=cmd,exit=p.returncode,errors=len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',p.stdout)),seconds=time.time()-start,input_sha256=hashlib.sha256(data).hexdigest(),output_sha256=hashlib.sha256(p.stdout).hexdigest(),source_still_matches=source.read_bytes()==data)
if mode=='module' and p.returncode==0:
    o=overlay/Path(rel).with_suffix('.olean');r.update(olean=str(o),olean_sha256=hashlib.sha256(o.read_bytes()).hexdigest())
(out/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));text=p.stdout.decode(errors='replace');print(text if len(text)<7000 else 'Full raw output retained in '+str(out/(label+'.out')))
