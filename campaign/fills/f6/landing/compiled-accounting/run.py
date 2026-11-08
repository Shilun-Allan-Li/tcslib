"""Run one reviewed import-only probe through the managed plain wrapper; input trees read-only."""
from pathlib import Path
import base64,datetime,gzip,hashlib,io,json,os,re,subprocess,sys,time
out=Path(__file__).resolve().parent;root=out.parents[4];context=json.loads((out/'context.json').read_text());H=lambda b:hashlib.sha256(b).hexdigest()
assert context['execution_authorized_by_parent_after_completed_native1']
name=sys.argv[1];names={'Base':('base','Inventory-base.lean.txt'),'Head':('head','Inventory-head.lean.txt'),'Fintype-native':('head','Fintype-controls-native.lean.txt'),'Fintype-sealed':('head','Fintype-controls-sealed.lean.txt'),'Fintype-uses':('head','Fintype-witness-uses.lean.txt'),'Fintype-uses-v2':('head','Fintype-witness-uses-v2.lean.txt'),'Fintype-uses-v3':('head','Fintype-witness-uses-v3.lean.txt')};assert name in names
endpoint,inputfile=names[name];pin=next(r for r in context['snapshots_read_only'] if r['endpoint']==endpoint);project=Path(context['probe_project'])
assert (project/'lean-toolchain').read_text().strip()==context['toolchain']=='leanprover/lean4:v4.25.0'
assert H((Path(context['actual_worktree'])/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes())==context['actual_source_sha256']
for r in context['snapshots_read_only']:
 assert H(Path(r['owner_olean']).read_bytes())==r['owner_olean_sha256'];assert H(Path(r['source_path']).read_bytes())==r['source_sha256']
source=(out/inputfile).read_bytes();file=project/(name.replace('-','_')+'.lean');assert not file.exists();file.write_bytes(source);raw=project/(name+'.out');assert not raw.exists();assert not (out/(name+'-run.json')).exists()
argv=['bash',str(root/'devtools/seyoon/leanelab.sh'),str(project),pin['snapshot'],str(file)];env=dict(os.environ,TCSLIB_LEAN_SLOTS='3')
start=datetime.datetime.now(datetime.timezone.utc).isoformat();record={'start_utc':start,'name':name,'argv':argv,'toolchain':context['toolchain'],'source_head':context['candidate_head'],'endpoint':endpoint,'complete_snapshot':pin['snapshot'],'input':inputfile,'input_sha256':H(source),'local_budget':3,'machine_cap':5,'single_Lean_sequential_plain_wrapper':True,'snapshot_owner_olean_before_sha256':pin['owner_olean_sha256']}
(out/(name+'-request.json')).write_text(json.dumps(record,indent=2)+'\n');t=time.monotonic()
with raw.open('wb') as f:proc=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,env=env)
seconds=time.monotonic()-t;data=raw.read_bytes();data.decode('utf-8');buf=io.BytesIO()
with gzip.GzipFile(filename='',mode='wb',fileobj=buf,compresslevel=9,mtime=0) as z:z.write(data)
gz=buf.getvalue();encoded=base64.encodebytes(gz);(out/(name+'.out.gz')).write_bytes(gz);(out/(name+'.out.gz.base64.txt')).write_bytes(encoded)
assert gzip.decompress(base64.b64decode(b''.join(encoded.split()),validate=True))==data
for r in context['snapshots_read_only']:assert H(Path(r['owner_olean']).read_bytes())==r['owner_olean_sha256']
assert H((Path(context['actual_worktree'])/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes())==context['actual_source_sha256']
record.update({'exit':proc.returncode,'seconds_including_any_slot_wait':seconds,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'errors':len(re.findall(rb'error:',data)),'warnings':len(re.findall(rb'warning:',data)),'raw_scratch_output':str(raw),'raw_stdout_stderr_bytes':len(data),'raw_stdout_stderr_sha256':H(data),'gzip_bytes':len(gz),'gzip_sha256':H(gz),'utf8_base64_bytes':len(encoded),'utf8_base64_sha256':H(encoded),'lossless_strict_stdlib_roundtrip':True,'all_source_and_two_owner_oleans_unchanged':True,'scope':'Import-only metadata/diagnostic run; no source, compiled snapshot, Git, cache, screen or integrated replay action'})
(out/(name+'-run.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
if proc.returncode and name!='Fintype-sealed':sys.exit(proc.returncode)
