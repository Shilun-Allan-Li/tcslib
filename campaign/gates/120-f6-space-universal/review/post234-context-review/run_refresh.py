from pathlib import Path
import json,os,hashlib,subprocess,time,datetime,re,gzip,io,base64
O=Path('/private/tmp/f6-post234-context-review');D=O/'fresh-validation';c=json.loads((O/'refresh-context.json').read_bytes());project=Path(c['project'])
def sha(b):return hashlib.sha256(b).hexdigest()
assert (project/'lean-toolchain').read_text().strip()==c['toolchain']=='leanprover/lean4:v4.25.0';assert sha(Path(c['wrapper']).read_bytes())==c['wrapper_sha256']
jobs=[('Base','Inventory.lean.txt','Base'),('Head','Inventory.lean.txt','Head'),('Owner-native','Owner-native.lean.txt','Head'),('Owner-sealed','Owner-sealed.lean.txt','Head'),('Controls-native','Controls-native.lean.txt','Head'),('Controls-sealed','Controls-sealed.lean.txt','Head'),('ArbitraryFiniteness','ArbitraryFiniteness.lean.txt','Head')]
for name,inputname,endpoint in jobs:
 snap=next(x for x in c['snapshots'] if x['endpoint']==endpoint);src=(D/inputname).read_bytes();assert sha(src)==next(x['sha256'] for x in c['inputs'] if x['name']==inputname);f=project/('Post234_'+name.replace('-','_')+'.lean');assert not f.exists();f.write_bytes(src);rawpath=project/(name+'.out');assert not rawpath.exists();argv=['bash',c['wrapper'],str(project),snap['path'],str(f)]
 assert sha((Path(c['source_worktree'])/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes())==c['source_sha256']
 assert all(sha(Path(s['owner_olean']).read_bytes())==s['owner_sha256'] for s in c['snapshots'])
 rec={'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['source_head'],'campaign_base':c['campaign_base'],'Hierarchy_sha256':c['source_sha256'],'name':name,'endpoint':endpoint,'argv':argv,'toolchain':c['toolchain'],'input':inputname,'input_sha256':sha(src),'snapshot':snap['path'],'complete_objects':895,'single_Lean_plain_wrapper':True,'local_slots':3,'machine_cap':5,'no_olean_output':True,'no_proof_value_prettyprint':True};(D/(name+'-request.json')).write_text(json.dumps(rec,indent=2)+'\n');t=time.monotonic()
 with rawpath.open('wb') as log:proc=subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,TCSLIB_LEAN_SLOTS='3'))
 elapsed=time.monotonic()-t;raw=rawpath.read_bytes();raw.decode('utf8');b=io.BytesIO()
 with gzip.GzipFile(filename='',fileobj=b,mode='wb',compresslevel=9,mtime=0) as z:z.write(raw)
 gz=b.getvalue();enc=base64.encodebytes(gz);(D/(name+'.out.gz')).write_bytes(gz);(D/(name+'.out.gz.base64.txt')).write_bytes(enc)
 if name not in ['Base','Head']:(D/(name+'.out')).write_bytes(raw)
 assert gzip.decompress(base64.b64decode(b''.join(enc.split()),validate=True))==raw
 rec.update({'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':proc.returncode,'seconds_including_slot_wait':elapsed,'errors':len(re.findall(rb'error:',raw)),'warnings':len(re.findall(rb'warning:',raw)),'sorry_warnings':len(re.findall(rb"declaration uses 'sorry'",raw)),'raw_bytes':len(raw),'raw_sha256':sha(raw),'gzip_bytes':len(gz),'gzip_sha256':sha(gz),'base64_bytes':len(enc),'base64_sha256':sha(enc),'strict_roundtrip':True,'all_owner_oleans_unchanged':all(sha(Path(s['owner_olean']).read_bytes())==s['owner_sha256'] for s in c['snapshots'])});(D/(name+'-run.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2),flush=True)
 if name=='Controls-sealed':
  if proc.returncode!=1 or rec['errors']!=72:raise SystemExit('Unexpected negative control outcome')
 elif proc.returncode:raise SystemExit(proc.returncode)
