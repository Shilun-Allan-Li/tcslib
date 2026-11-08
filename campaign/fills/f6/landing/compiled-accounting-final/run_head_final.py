from pathlib import Path
import os,json,hashlib,datetime,subprocess,time,re,io,gzip,base64
O=Path('/private/tmp/f6-compiled-accounting-final');c=json.loads((O/'context.json').read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
project=Path(c['probe_project']);assert (project/'lean-toolchain').read_text().strip()==c['toolchain']=='leanprover/lean4:v4.25.0'
assert sha(Path(c['wrapper']).read_bytes())==c['wrapper_sha256']
assert sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256']
assert sha(Path(c['owner_olean']).read_bytes())==c['owner_olean_sha256']
assert sha(Path(c['BASE_owner_olean']).read_bytes())==c['BASE_owner_olean_sha256']
assert (project/'.lake/packages').resolve()==Path(c['packages_resolved'])
probe=(O/'Inventory-head.lean.txt').read_bytes();assert sha(probe)==c['exact_probe_SHA256']
f=project/'HeadFinal2.lean';assert not f.exists();f.write_bytes(probe)
rawpath=project/'HeadFinal2.out';assert not rawpath.exists();assert not (O/'Head-run.json').exists()
argv=['bash',c['wrapper'],str(project),c['snapshot'],str(f)]
rec={'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':'Head','source_head':c['candidate_head'],'source_sha256':c['source_sha256'],'argv':argv,'toolchain':c['toolchain'],'input':'Inventory-head.lean.txt','input_sha256':sha(probe),'endpoint':'fresh final HEAD','complete_snapshot':c['snapshot'],'complete_snapshot_olean_count':895,'owner_olean_before_sha256':c['owner_olean_sha256'],'local_budget':3,'machine_cap':5,'single_Lean_sequential_plain_wrapper':True,'no_olean_output':True,'no_theorem_proof_value_rendering':True}
(O/'Head-request.json').write_text(json.dumps(rec,indent=2)+'\n');start=time.monotonic()
with rawpath.open('wb') as f:proc=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,TCSLIB_LEAN_SLOTS='3'))
seconds=time.monotonic()-start;raw=rawpath.read_bytes();raw.decode('utf8');buf=io.BytesIO()
with gzip.GzipFile(filename='',mode='wb',fileobj=buf,compresslevel=9,mtime=0) as z:z.write(raw)
gz=buf.getvalue();enc=base64.encodebytes(gz);(O/'Head.out.gz').write_bytes(gz);(O/'Head.out.gz.base64.txt').write_bytes(enc)
assert base64.b64decode(b''.join(enc.split()),validate=True)==gz and gzip.decompress(gz)==raw
assert sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256']
assert sha(Path(c['owner_olean']).read_bytes())==c['owner_olean_sha256']
assert sha(Path(c['BASE_owner_olean']).read_bytes())==c['BASE_owner_olean_sha256']
rec.update({'exit':proc.returncode,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds_including_any_slot_wait':seconds,'errors':len(re.findall(rb'error:',raw)),'warnings':len(re.findall(rb'warning:',raw)),'raw_scratch_output':str(rawpath),'raw_stdout_stderr_bytes':len(raw),'raw_stdout_stderr_sha256':sha(raw),'gzip_bytes':len(gz),'gzip_sha256':sha(gz),'utf8_base64_bytes':len(enc),'utf8_base64_sha256':sha(enc),'strict_stdlib_lossless_roundtrip':True,'source_and_BASE_HEAD_owner_oleans_unchanged':True})
(O/'Head-run.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
if proc.returncode:raise SystemExit(proc.returncode)
