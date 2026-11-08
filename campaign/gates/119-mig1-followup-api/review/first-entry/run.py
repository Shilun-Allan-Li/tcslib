"""Sequential managed elaboration with immutable input/log/request receipts."""
from pathlib import Path
import json,hashlib,subprocess,datetime,tempfile,re,time,sys,os
out=Path(__file__).resolve().parent;root=out.parents[4];context=json.loads((out/'context.json').read_text());wt=Path(context['worktree']);base=Path(context['snapshot']);overlay=Path(context['own_complete_overlay']);H=lambda b:hashlib.sha256(b).hexdigest();kind=sys.argv[1]
if kind=='Actual-module':
 name=kind;source=wt/'TCSlib/Complexity/TuringMachine/Finite.lean';command=['bash',str(root/'devtools/seyoon/leanelab-o.sh'),str(wt),str(overlay),'TCSlib/Complexity/TuringMachine/Finite.lean',str(overlay)]
else:
 name=kind;source=out/(name+'.lean.txt');assert source.is_file();tmp=Path(tempfile.mkdtemp(prefix='tcslib-g119-first-entry-',dir='/private/tmp'));p=tmp/(name.replace('-','_')+'.lean');p.write_bytes(source.read_bytes());command=['bash',str(root/'devtools/seyoon/leanelab.sh'),str(wt),str(overlay),str(p)]
log=out/(name+'.out');receipt=out/(name+'-run.json');assert not log.exists() and not receipt.exists();data=source.read_bytes();start=time.time();r={'command':command,'kind':kind,'input_path':str(source),'input_sha256':H(data),'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'local_slots':os.environ.get('TCSLIB_LEAN_SLOTS'),'scope':'Isolated actualFinite/section/metadata/controls; not integrated5module chain or replay.'};(out/(name+'-request.json')).write_text(json.dumps(r,indent=2)+'\n');result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(result.stdout);text=result.stdout.decode(errors='replace');r.update(exit=result.returncode,seconds=time.time()-start,errors=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',text,re.M)),warnings=len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M)),output_sha256=H(result.stdout),input_source_stable=source.read_bytes()==data)
if kind=='Actual-module':r['own_output_olean_sha256']=H((overlay/'TCSlib/Complexity/TuringMachine/Finite.olean').read_bytes()) if result.returncode==0 else None
receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));print(text)
