"""One managed read-only import probe; all attempt bytes/commands retained."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys,tempfile,time
out=Path(__file__).resolve().parent;root=out.parents[4]
mode=sys.argv[1];assert mode in ['base','head'];stem='Inventory-'+mode
source=out/(stem+'.lean.txt');context=json.loads((out/'context.json').read_text());tree=Path(context[mode+'_snapshot']);wt=Path(context['worktree']);H=lambda b:hashlib.sha256(b).hexdigest()
log=out/(stem+'.out');receipt=out/(stem+'-run.json');assert not log.exists() and not receipt.exists()
for r in context['source_and_olean_pins']:assert H(Path(r[mode+'_olean_path']).read_bytes())==r[mode+'_olean_sha256']
raw=source.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-g119-compiled-',dir='/private/tmp'))/(stem.replace('-','_')+'.lean');tmp.write_bytes(raw)
cmd=['bash',str(root/'devtools/seyoon/leanelab.sh'),str(wt),str(tree),str(tmp)]
start=time.time();r={'mode':mode,'command':cmd,'input_path':str(source),'temporary_input':str(tmp),'input_sha256':H(raw),'snapshot':str(tree),'local_lean_slots':os.environ.get('TCSLIB_LEAN_SLOTS'),'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'read_only_imports_no_compiled_output':True}
(out/(stem+'-request.json')).write_text(json.dumps(r,indent=2)+'\n')
result=subprocess.run(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(result.stdout);text=result.stdout.decode(errors='replace')
r.update(exit=result.returncode,seconds=time.time()-start,output_sha256=H(result.stdout),output_bytes=len(result.stdout),errors=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',text,re.M)),warnings=len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M)),input_stable=source.read_bytes()==raw)
r['all_five_snapshot_outputs_unchanged']=all(H(Path(x[mode+'_olean_path']).read_bytes())==x[mode+'_olean_sha256'] for x in context['source_and_olean_pins'])
r['all_five_actual_sources_stable']=all(H((wt/x['file']).read_bytes())==x['head_source_sha256'] for x in context['source_and_olean_pins'])
receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if result.returncode:print(text[:12000])
