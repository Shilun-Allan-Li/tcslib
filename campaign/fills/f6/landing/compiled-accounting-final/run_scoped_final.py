from pathlib import Path
import os,json,hashlib,datetime,subprocess,time,re,gzip,base64,io
O=Path('/private/tmp/f6-compiled-accounting-final');D=O/'scoped-seals-final';c=json.loads((O/'context.json').read_bytes());project=Path(c['probe_project'])
def sha(b):return hashlib.sha256(b).hexdigest()
assert (project/'lean-toolchain').read_text().strip()==c['toolchain']=='leanprover/lean4:v4.25.0'
assert sha(Path(c['wrapper']).read_bytes())==c['wrapper_sha256']
for name in ['Owner-native','Owner-sealed','Controls-native','Controls-sealed']:
 assert sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256'];assert sha(Path(c['owner_olean']).read_bytes())==c['owner_olean_sha256']
 src=(D/(name+'.lean.txt')).read_bytes();file=project/('Final_'+name.replace('-','_')+'.lean');assert not file.exists();file.write_bytes(src);rawpath=project/('Final_'+name+'.out');assert not rawpath.exists()
 argv=['bash',c['wrapper'],str(project),c['snapshot'],str(file)];record={'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'name':name,'source_head':c['candidate_head'],'source_sha256':c['source_sha256'],'argv':argv,'toolchain':c['toolchain'],'input':name+'.lean.txt','input_sha256':sha(src),'snapshot':c['snapshot'],'local_slots':3,'machine_cap':5,'one_Lean_at_a_time':True,'plain_wrapper_no_olean_output':True,'no_theorem_proof_value_prettyprint':True}
 (D/(name+'-request.json')).write_text(json.dumps(record,indent=2)+'\n');t=time.monotonic()
 with rawpath.open('wb') as f:proc=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,TCSLIB_LEAN_SLOTS='3'))
 elapsed=time.monotonic()-t;raw=rawpath.read_bytes();raw.decode('utf8');buf=io.BytesIO()
 with gzip.GzipFile(filename='',mode='wb',fileobj=buf,compresslevel=9,mtime=0) as z:z.write(raw)
 gz=buf.getvalue();enc=base64.encodebytes(gz);(D/(name+'.out')).write_bytes(raw);(D/(name+'.out.gz')).write_bytes(gz);(D/(name+'.out.gz.base64.txt')).write_bytes(enc);assert gzip.decompress(base64.b64decode(b''.join(enc.split()),validate=True))==raw
 record.update({'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':proc.returncode,'seconds_including_any_slot_wait':elapsed,'errors':len(re.findall(rb'error:',raw)),'warnings':len(re.findall(rb'warning:',raw)),'sorry_warnings':len(re.findall(rb"declaration uses 'sorry'",raw)),'raw_stdout_stderr_bytes':len(raw),'raw_stdout_stderr_sha256':sha(raw),'gzip_bytes':len(gz),'gzip_sha256':sha(gz),'utf8_base64_bytes':len(enc),'utf8_base64_sha256':sha(enc),'strict_roundtrip':True,'owner_olean_unchanged':sha(Path(c['owner_olean']).read_bytes())==c['owner_olean_sha256'],'source_unchanged':sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256']})
 (D/(name+'-run.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2),flush=True)
 if name!='Controls-sealed' and proc.returncode:raise SystemExit(proc.returncode)
